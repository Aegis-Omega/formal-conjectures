# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Build an exact-head upstream handoff from an ALREADY kernel-exported RH graph.

This script never upgrades an unrelated successful workflow or historical status
to an RH proof. It verifies the exact Mathlib target, exported axiom dependencies,
tracked source identity, and an independent Lean proof application.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
OFFICIAL_MODULE = "FormalConjectures.Millennium.RiemannHypothesis"
OFFICIAL_SOURCE = "FormalConjectures/Millennium/RiemannHypothesis.lean"
CHECKPOINTS = {
    "pr91_headers_ancestor": "d6dc5256a0a73773438cad49da222ff239b3aaf6",
    "pr89_proof_ancestor": "5d7425dcc6f4137b2cf3f57bc953504135a388e6",
    "pr88_assembly_ancestor": "aacdd511877e3e725dbee05b1167ee38b681ab31",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closed_candidates(rows: list[dict]) -> list[dict]:
    """Only Lean-reported definitional equality and permissible kernel axioms count."""
    return sorted((
        row for row in rows
        if row.get("type_defeq_riemann_hypothesis") is True
        and row.get("has_body") is True
        and row.get("is_axiom") is False
        and isinstance(row.get("axioms"), list)
        and set(row["axioms"]) <= ALLOWED_AXIOMS
        and isinstance(row.get("identifier"), str)
    ), key=lambda row: row["identifier"])


def make_probe(module: str, identifier: str) -> str:
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*", name)
               for name in (module, identifier)):
        raise ValueError("Invalid Lean module or declaration name")
    return (f"import {module}\n\n"
            f"example : _root_.RiemannHypothesis := {identifier}\n"
            f"#print axioms {identifier}\n")


def audited_axioms(text: str, identifier: str) -> set[str] | None:
    """Match the requested declaration only, never an unrelated audit."""
    target = re.escape(identifier)
    m = re.search(r"'" + target + r"' depends on axioms:\s*\[([^]]*)\]", text)
    if m:
        return {a.strip() for a in m.group(1).split(",") if a.strip()}
    if re.search(r"'" + target + r"' does not depend on any axioms", text):
        return set()
    return None


def tracked_source(root: Path, record: dict, identifier: str) -> tuple[str, int] | None:
    path = record.get("source")
    if not isinstance(path, str) or not path.endswith(".lean"):
        return None
    rel = Path(path)
    if rel.is_absolute() or ".." in rel.parts or not (root / rel).is_file():
        return None
    git = subprocess.run(
        ["git", "cat-file", "-e", f"HEAD:{rel.as_posix()}"],
        cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if git.returncode != 0 or sha256(root / rel) != record.get("sha256"):
        return None
    name = identifier.rsplit(".", 1)[-1]
    pattern = re.compile(r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
                         r"(?:theorem|lemma|def|opaque)\s+" + re.escape(name) + r"\b")
    for number, line in enumerate((root / rel).read_text().splitlines(), 1):
        if pattern.search(line):
            return rel.as_posix(), number
    return None


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    out = root / "evidence-cofinal" / "assembly"
    out.mkdir(parents=True, exist_ok=True)
    graph_path = out / "environment-rh-candidates.json"
    manifest_path = root / "evidence-cofinal" / "source-manifest.json"
    if not graph_path.is_file() or not manifest_path.is_file():
        raise RuntimeError("EXACT_HEAD_KERNEL_EXPORT_NOT_PRESENT")

    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    manifest = json.loads(manifest_path.read_text())
    census = json.loads(graph_path.read_text())
    if census.get("defeq_target_type") != "RiemannHypothesis":
        raise RuntimeError("WRONG_RH_TARGET_TYPE")
    if census.get("semantic_declarations_checked", 0) <= 0:
        raise RuntimeError("NO_IMPORTED_ENVIRONMENT_SCAN")
    passport = json.loads((out / "RH_EVIDENCE_PASSPORT.json").read_text())
    if passport.get("exact_replay_sha") != head:
        raise RuntimeError("REPLAY_HEAD_DRIFT")
    by_module = {row["module"]: row for row in manifest}
    # The canonical theorem is itself an admissible proof if the Lean kernel
    # verifies its body and axioms. Do not reject it merely by declaration name.
    # Source identity still requires this tracked exact-head file.
    if (root / OFFICIAL_SOURCE).is_file():
        by_module[OFFICIAL_MODULE] = {
            "module": OFFICIAL_MODULE,
            "source": OFFICIAL_SOURCE,
            "sha256": sha256(root / OFFICIAL_SOURCE),
        }
    candidates = closed_candidates(census.get("declarations", []))
    status = "NO_CLOSED_RH_DECLARATION_IN_THIS_IMPORTED_ENVIRONMENT"
    declaration = None
    receipt = {
        "schema": "aegis.rh.official-submission-checkpoint.v1",
        "repository": "tarikskalic33/formal-conjectures",
        "exact_head": head,
        "target": "_root_.RiemannHypothesis",
        "scan_scope": census.get("inspected_count"),
        "verified_ancestor_commit_ids": CHECKPOINTS,
        "ancestor_note": "Git lineage is separately checked; an ancestor receipt is not a current proof verdict",
        "proof_graph_sha256": sha256(out / "proof-terms.json"),
        "imported_environment_sha256": sha256(graph_path),
        "source_manifest_sha256": sha256(manifest_path),
        "closed_type_candidates": [row["identifier"] for row in candidates],
        "ready_for_official_submission": False,
        "status": status,
    }

    for row in candidates:
        identifier = row["identifier"]
        module = row.get("module")
        if not isinstance(module, str) or module not in by_module:
            continue
        resolved = tracked_source(root, by_module[module], identifier)
        if resolved is None:
            continue
        source_path, line = resolved
        probe = out / "RHOfficialExactTypeProbe.lean"
        probe.write_text(make_probe(module, identifier))
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / "RHOfficialExactTypeProbe.log").write_text(result.stdout)
        actual_axioms = audited_axioms(result.stdout, identifier)
        if result.returncode != 0 or actual_axioms is None or not actual_axioms <= ALLOWED_AXIOMS:
            raise RuntimeError("OFFICIAL_RH_PROOF_TERM_OR_AXIOM_AUDIT_FAILED")
        if actual_axioms != set(row["axioms"]):
            raise RuntimeError("INDEPENDENT_AXIOM_AUDIT_MISMATCH")
        declaration = identifier
        receipt.update({
            "status": "INDEPENDENT_CANONICAL_RH_TERM_KERNEL_AND_AXIOM_PASS",
            "ready_for_official_submission": True,
            "declaration": identifier,
            "module": module,
            "source_path": source_path,
            "source_line": line,
            "axioms": sorted(actual_axioms),
            "probe_log_sha256": sha256(out / "RHOfficialExactTypeProbe.log"),
        })
        template = (root / "research/rh/assembly/upstream-formal-proof.patch.in").read_text()
        patch = template.replace("FINAL_VERIFIED_SHA", head).replace(
            "FINAL_PROOF_PATH", source_path).replace("FINAL_DECLARATION_LINE", str(line))
        (out / "upstream-formal-proof.patch").write_text(patch)
        break

    (out / "RH_OFFICIAL_SUBMISSION.json").write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    (out / "RH_OFFICIAL_SUBMISSION.md").write_text(
        "# RH official submission readiness (exact-head)\n\n"
        + f"- Commit: {head}\n- Status: {receipt['status']}\n"
        + f"- Ready: {receipt['ready_for_official_submission']}\n"
        + f"- Canonical type candidates in the imported environment: {len(candidates)}\n"
        + (f"- Verified declaration: {declaration}\n" if declaration else "")
        + "\nThe candidate census covers this imported kernel environment, not other branches "
          "or external archives. Historical metadata is not evidence of an unresolved theorem.\n")
    print("RH_OFFICIAL_SUBMISSION_STATUS=" + receipt["status"])
    print("RH_OFFICIAL_SUBMISSION_READY=" + str(receipt["ready_for_official_submission"]).lower())
    return 0


if __name__ == "__main__":
    sys.exit(main())
