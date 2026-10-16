"""Generate source-bound partial proof receipts after actual Lean compilation."""
import datetime, hashlib, json, os, pathlib, re, shutil, subprocess

ROOT = pathlib.Path(".")
OUT = ROOT / "evidence-cofinal" / "assembly"
OUT.mkdir(parents=True, exist_ok=True)
META = ROOT / "research/rh/assembly"

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def git_sha(p=ROOT):
    return subprocess.check_output(["git", "-C", str(p), "rev-parse", "HEAD"], text=True).strip()

def write(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")

def run_closure_probes(root, meta, out):
    """Require the narrow constructor to pass and the pi-window misuse to fail."""
    results = {}
    for stem in ("RH_CLOSURE_PROBE", "RH_CLOSURE_NEGATIVE_PI_PROBE"):
        source = root / (stem + ".lean")
        source.write_text((meta / (stem + ".txt")).read_text())
        probe = subprocess.run(["lake", "env", "lean", str(source)],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (out / (stem + ".log")).write_text(probe.stdout)
        results[stem] = probe
    positive = results["RH_CLOSURE_PROBE"]
    if positive.returncode != 0 or "sorryAx" in positive.stdout or "error:" in positive.stdout:
        raise RuntimeError("NARROW_CONSTRUCTOR_PROBE_FAILED\n" + positive.stdout)
    name = "AEGIS.RHAssemblyV1.narrow_window_schur_family"
    audit = re.search(r"'" + re.escape(name) +
                      r"'\s+depends on axioms:\s*\[([^\]]*)\]", positive.stdout)
    if audit is None:
        raise RuntimeError("NARROW_CONSTRUCTOR_AXIOM_AUDIT_MISSING")
    axioms = {item.strip() for item in audit.group(1).split(",") if item.strip()}
    if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
        raise RuntimeError("NARROW_CONSTRUCTOR_UNEXPECTED_AXIOMS " + repr(axioms))
    negative = results["RH_CLOSURE_NEGATIVE_PI_PROBE"]
    if negative.returncode == 0:
        raise RuntimeError("PI_WINDOW_NEGATIVE_PROBE_UNEXPECTEDLY_COMPILED")
    if ("type mismatch" not in negative.stdout.lower()
            or "LogWindowContainsV1" not in negative.stdout):
        raise RuntimeError("PI_WINDOW_PROBE_FAILED_FOR_UNEXPECTED_REASON\n" + negative.stdout)
    return positive, negative

manifest = json.loads((ROOT / "evidence-cofinal/source-manifest.json").read_text())
head = git_sha()
modules = {}
source_snapshots = {line.split()[0]: line.split()[1]
                    for line in (ROOT / "evidence-cofinal/archived-source-lock.txt").read_text().splitlines()}
abel_members = {"WeilSignedPrimeFiniteSupportV1", "WeilPrimeAbelReductionV1",
                "WeilPrimeDiscrepancyV1", "WeilPrimeDiscrepancyEstimateV1"}
originals = json.loads((ROOT / "research/rh/aegis_pr721_fb983fd/source_manifest.json").read_text())
originals_by_name = {r["module"]: r for r in originals["files"]}
for record in manifest:
    module = record["module"]
    source = pathlib.Path(record["source"])
    assert digest(source) == record["sha256"], module
    log = ROOT / "evidence-cofinal" / ("compile-" + module.replace(".", "_") + ".log")
    text = log.read_text()
    assert "sorryAx" not in text and "error:" not in text, module
    src = source.read_text()
    imports = re.findall(r"^import\s+(\S+)", src, re.M)
    if str(source).startswith(".aegis/"):
        provenance = {"repo": "Aegis-Omega/AEGIS-OMEGA", "sha": os.environ["AEGIS_SHA"]}
    elif module.startswith(("Lc.", "Hadamard.", "FunctionsOfOneComplexVariable.")):
        provenance = {"repo": "nicholasbulka/li-criterion-rh-equivalence-lean",
                      "sha": os.environ["LI_CRITERION_SHA"],
                      "adaptation_note": "Factorization has three source-locked API edits recorded in the workflow"}
    elif str(source).startswith(("AEGISOverlay/", "FormalConjecturesUtil/", "research/", "AegisRH/")):
        provenance = {"repo": "tarikskalic33/formal-conjectures", "sha": head}
    else:
        provenance = {"repo": "tarikskalic33/formal-conjectures",
                      "replay_sha": head, "historical_containing_commit": None,
                      "note": "Archived/blob-staged input; see archived-source-lock and archive digest"}
    if module in source_snapshots:
        snapshot = "research/rh/assembly/exact-source-inputs/" + module + ".lean.txt"
        assert source.read_bytes() == (ROOT / snapshot).read_bytes(), module
        provenance = {"repo": "tarikskalic33/formal-conjectures", "sha": head,
                      "source_file": snapshot, "git_blob": source_snapshots[module],
                      "original_historical_commit": None}
    elif module in abel_members:
        provenance = {"repo": "tarikskalic33/formal-conjectures", "sha": head,
                      "source_archive": "research/rh/integration/AEGIS_PR63_ARCHIVED_ABEL_SOURCES_V6.tar.gz",
                      "archive_member": module + ".lean"}
    original = originals_by_name.get(module)
    if original and source.read_bytes() == (ROOT / original["archive"]).read_bytes():
        provenance = {"repo": "Aegis-Omega/AEGIS-OMEGA",
                      "sha": originals["source_head"],
                      "source_file": originals["source_subtree"] + "/" + module + ".lean"
                         if "/" in originals["source_subtree"] else
                         "sovereign-omega-v2/formal/bridges/lean/" + module + ".lean",
                      "git_blob": original["sha"],
                      "archive_in_replay": original["archive"],
                      "replay_sha": head}
    probes = re.findall(r"^#print axioms (\S+)$", src, re.M)
    modules[module] = dict(record, imports=imports, provenance=provenance,
                          kernel_status="compiled_on_exact_head", printed_axiom_probes=probes)
    dest = OUT / "sources" / pathlib.Path(module.replace(".", "/") + ".lean")
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, dest)

terms = json.loads((OUT / "proof-terms.json").read_text())
rows = {r["identifier"]: r for r in terms["declarations"]}
missing = sorted({d for r in rows.values() for d in r["direct_dependencies"] if d not in rows})
adj = {n: set(r["direct_dependencies"]) & rows.keys() for n, r in rows.items()}
reverse = {n: set() for n in rows}
for n, deps in adj.items():
    for d in deps:
        reverse[d].add(n)

# Condense recursive type/constructor dependencies into a genuine DAG.
seen = set()
order = []
for start in rows:
    stack = [(start, False)]
    while stack:
        n, exiting = stack.pop()
        if exiting:
            order.append(n)
            continue
        if n in seen:
            continue
        seen.add(n)
        stack.append((n, True))
        stack.extend((d, False) for d in adj[n] if d not in seen)
component = {}
components = []
for start in reversed(order):
    if start in component:
        continue
    idx = len(components)
    members = []
    stack = [start]
    while stack:
        n = stack.pop()
        if n in component:
            continue
        component[n] = idx
        members.append(n)
        stack.extend(reverse[n] - component.keys())
    components.append(members)
dag = sorted({(component[n], component[d]) for n, deps in adj.items() for d in deps
              if component[n] != component[d]})
# The root list is a bounded integration scope, not the whole historical corpus.
# These previously established stronger lanes MUST remain visible on every
# subsequent replay. Fail a narrowed audit rather than quietly restarting the
# search from a single optimized hselect/Schur terminal.
mandatory_producers = {
    "AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_finite_actual_weil_partition",
    "AEGIS.RHKreinMultiplicativeTransportV1.every_packet_actual_two_block_zero_quadratic",
    "AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support",
    "AEGIS.RHActualMixedDefectV1.fine_cluster_nine_exact_counterpart",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_arithmetic_nonpositive",
    "AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_optimized_q16_coercive",
    "AEGIS.RHTimeSliceWeilV1.fsTwoThreeShiftGroup_dense",
    "AEGIS.RHTimeSliceWeilV1.fsTwoThreeDetectorSign_iff_riemannHypothesis",
    "AEGIS.RHBaguaActualWeilV1.bagua_complementary_phase_coupling_margin",
    "AEGIS.RHLogThreeSignedPrimeProducerV1.actual_signed_prime_gap_two_log_three",
    "AEGIS.RHNarrowDetectingTrigramDenseV1.dense_narrow_detector_iff_riemannHypothesis",
    "AEGIS.RHGlobalizationChainV13.rh_of_vanishing_error_on_exhaustion",
    "AEGIS.RHCofinalActualTerminalV1.riemannHypothesis_of_cofinal_lower_certificates",
    "AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer",
}
missing_mandatory = mandatory_producers - set(terms["roots"])
missing_resolved = set(terms["roots"]) - rows.keys()
if missing_mandatory or missing_resolved:
    raise RuntimeError("RH_PROOF_GRAPH_ROOT_COVERAGE_REGRESSION "
                       + repr({"missing_mandatory": sorted(missing_mandatory),
                               "missing_resolved": sorted(missing_resolved)}))
root_coverage = {
    "scope": "selected current-branch import DAG only; NOT an exhaustive cross-branch audit",
    "root_count": len(terms["roots"]),
    "resolved_root_count": len(terms["roots"]) - len(missing_resolved),
    "mandatory_stronger_roots": sorted(mandatory_producers),
    "mandatory_stronger_roots_resolved": True,
    "historical_repository_and_archive_exhaustiveness": False,
}

root_axioms = {root: rows[root]["axioms"] for root in terms["roots"]}
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
for root, axioms in root_axioms.items():
    assert set(axioms) <= allowed_axioms, (root, axioms)

# Assess only what the kernel-compiled *selected roots* actually establish.
# A theorem with conclusion RH but a premise (e.g. hselect/hcert) is not a
# closed proof. Absence of a closed root in this limited graph does not imply
# that none exists in other branches, repos, or source DAGs.
closed_rh_roots = [
    root for root in terms["roots"]
    if rows[root]["type_expr"].strip() in ("RiemannHypothesis", "_root_.RiemannHypothesis")
    and rows[root]["has_body"]
    and not rows[root]["is_axiom"]
    and set(rows[root]["axioms"]) <= allowed_axioms
]
rh_assessment = (
    "CLOSED_CANONICAL_RH_ROOT_KERNEL_AND_AXIOM_PASS"
    if closed_rh_roots else
    "CANONICAL_RH_CLOSURE_NOT_ASSESSED_OUTSIDE_SELECTED_ROOTS"
)
rh_proven_in_selected_roots = True if closed_rh_roots else None

for row in rows.values():
    module = row["module"]
    row["source"] = modules.get(module)
    if module.startswith("Mathlib"):
        row["external_pin"] = {"repo": "leanprover-community/mathlib4",
                               "sha": os.environ["MATHLIB_SHA"]}
    elif module.startswith(("Lean", "Init", "Std", "Lake")):
        row["external_pin"] = {"toolchain": os.environ["LEAN_TOOLCHAIN"]}
    row["kernel_status"] = "reachable_from_kernel_compiled_and_axiom_audited_roots"

graph = {"status": "selected_root_elaborated_type_and_available_proof_dependency_closure",
         "scope_limit": "Selected terminal/constructor/Gram route; not an all-history repository census",
         "exact_replay_sha": head, "modules": modules, "root_coverage": root_coverage,
         "roots": terms["roots"], "root_axioms": root_axioms,
         "declarations": list(rows.values()), "missing_environment_constants": missing,
         "strongly_connected_components": components,
         "condensation_dag_edges": dag,
         "unresolved_producer": json.loads((META / "RH_BLOCKER.json").read_text())["obligation_type"]}
write("RH_PROOF_GRAPH.json", graph)

probe, negative_probe = run_closure_probes(ROOT, META, OUT)
probe_file = ROOT / "RH_CLOSURE_PROBE.lean"
negative_probe_file = ROOT / "RH_CLOSURE_NEGATIVE_PI_PROBE.lean"

blocker = json.loads((META / "RH_BLOCKER.json").read_text())
blocker["status"] = "CONSTRUCTOR_KERNEL_PASS; " + rh_assessment
blocker["attempts"][0]["status"] = "KERNEL_AND_STANDARD_AXIOM_AUDIT_PASS"
blocker["attempts"][1].update(
    operation="Compile established narrow-window constructor; separately reject pi-window misuse",
    status="NARROW_KERNEL_AND_AXIOM_PASS; PI_WINDOW_NEGATIVE_TYPE_MISMATCH")
for attempt in blocker["attempts"]:
    if attempt.get("source") == "AEGISOverlay/RHActualUniversalFineGramV1.lean":
        assert "AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram" in root_axioms
        attempt["status"] = "KERNEL_AND_STANDARD_AXIOM_AUDIT_PASS"
        attempt["exact_head"] = head
blocker["observed_positive_test"] = {"command": "lake env lean RH_CLOSURE_PROBE.lean",
                                   "exit_code": probe.returncode, "log": probe.stdout}
blocker["observed_failing_test"] = {"command": "lake env lean RH_CLOSURE_NEGATIVE_PI_PROBE.lean",
                                  "exit_code": negative_probe.returncode, "log": negative_probe.stdout}
write("RH_BLOCKER.json", blocker)

passport = json.loads((META / "RH_EVIDENCE_PASSPORT.json").read_text())
event = json.loads(pathlib.Path(os.environ["GITHUB_EVENT_PATH"]).read_text()) if os.environ.get("GITHUB_EVENT_PATH") else {}
passport.update(verification_status="SELECTED_ROOTS_KERNEL_AND_AXIOM_PASS; " + rh_assessment,
                RH_PROVEN_UNCONDITIONALLY=rh_proven_in_selected_roots,
                final_theorem_signature="RiemannHypothesis" if closed_rh_roots else None,
                final_theorem_axioms={root: root_axioms[root] for root in closed_rh_roots} if closed_rh_roots else None,
                closed_rh_roots_in_selected_graph=closed_rh_roots,
                root_coverage=root_coverage,
                unconditional_proof_scope="Selected kernel-compiled Lean roots only; null means not determined",
                exact_replay_sha=head, new_candidate_axioms=root_axioms,
                active_repository="tarikskalic33/formal-conjectures",
                active_pull_request=(event.get("pull_request") or {}).get("number"),
                active_branch=os.environ.get("GITHUB_HEAD_REF") or None,
                proof_graph_status=graph["status"],
                workflow_run_id=os.environ.get("GITHUB_RUN_ID"),
                workflow_job=os.environ.get("GITHUB_JOB"),
                recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                actual_lean_version=subprocess.check_output(["lean", "--version"], text=True).strip(),
                actual_mathlib_sha=git_sha(ROOT / ".lake/packages/mathlib"),
                source_hashes={m: r["sha256"] for m, r in modules.items()},
                proof_term_graph_sha256=digest(OUT / "proof-terms.json"),
                compiler_probe={"exit_code": probe.returncode, "log_sha256": digest(OUT / "RH_CLOSURE_PROBE.log")},
                negative_compiler_probe={"exit_code": negative_probe.returncode,
                                         "log_sha256": digest(OUT / "RH_CLOSURE_NEGATIVE_PI_PROBE.log")},
                certificate_hashes={"abel_archive": digest(ROOT / "research/rh/integration/AEGIS_PR63_ARCHIVED_ABEL_SOURCES_V6.tar.gz")})
write("RH_EVIDENCE_PASSPORT.json", passport)
shutil.copyfile(ROOT / "AEGISOverlay/AEGIS_RH_Unconditional.lean", OUT / "AEGIS_RH_Unconditional.lean")
book = (META / "RH_PROOFBOOK.md").read_text()
book += "\n\n## Observed exact-head kernel receipt\n\n"
book += "Exact replay head: `" + head + "`. The following selected roots compiled "
book += "and have only permitted foundational axioms. Earlier candidate labels describe "
book += "the committed source snapshot; this observed receipt records the replay result.\n\n"
for root, axioms in root_axioms.items():
    module = rows[root]["module"]
    record = modules.get(module)
    if record:
        prov = record["provenance"]
        sha = prov.get("sha", head)
        repo = prov.get("repo", "tarikskalic33/formal-conjectures")
        path = prov.get("source_file", record["source"])
        if path.startswith(".aegis/"): path = path[len(".aegis/"):]
        url = "https://github.com/" + repo + "/blob/" + sha + "/" + path
        book += "- [`" + root + "`](" + url + "): `" + ", ".join(axioms) + "`.\n"
    else:
        book += "- `" + root + "`: `" + ", ".join(axioms) + "`.\n"
book += "\n## Canonical RH proof admission (observed, not pre-set)\n"
book += "Selected-root status: `" + rh_assessment + "`.\n"
book += "Closed canonical RH roots in this compiled graph: `" + repr(closed_rh_roots) + "`.\n"
book += "The RH_PROVEN_UNCONDITIONALLY field is true only for a kernel-compiled "
book += "axiom-clean root with EXACT type RiemannHypothesis. Otherwise it is null "
book += "(unknown outside this selected DAG), not a hard-coded false assertion.\n"
book += "\nStronger producer coverage: `" + str(root_coverage["root_count"]) + "` roots, " + str(len(mandatory_producers)) + " mandatory lanes retained; NOT an all-branch census.\n"
book += "The previously described producer obligation is retained in RH_BLOCKER.json "
book += "as a candidate route, NOT as a global impossibility or closure verdict.\n"
(OUT / "RH_PROOFBOOK.md").write_text(book)
shutil.copyfile(META / "RH_EXACT_HEAD_REPLAY.sh", OUT / "RH_EXACT_HEAD_REPLAY.sh")
shutil.copyfile(probe_file, OUT / "RH_CLOSURE_PROBE.lean")
shutil.copyfile(negative_probe_file, OUT / "RH_CLOSURE_NEGATIVE_PI_PROBE.lean")
print("ASSEMBLY_KERNEL_ROOTS", len(terms["roots"]))
print("STRONGER_PRODUCER_ROOT_COVERAGE", "PASS", len(mandatory_producers))
print("ASSEMBLY_PROOF_GRAPH_DECLARATIONS", len(rows))
print("ASSEMBLY_NARROW_PROBE_PASS", probe.returncode)
print("ASSEMBLY_PI_NEGATIVE_PROBE_ACTUAL_TYPE_MISMATCH", negative_probe.returncode)
print("CANONICAL_RH_SELECTED_ROOT_ASSESSMENT", rh_assessment)
