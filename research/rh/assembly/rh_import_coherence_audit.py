#!/usr/bin/env python3
"""Dependency-aware, no-write RH graft triage across exact GitHub source blobs.

A Git blob match proves only source identity, not elaboration or theorem validity.
No files are automatically transplanted and no RH theorem is promoted.
"""
from __future__ import annotations

import argparse
import base64
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request

IMPORT = re.compile(r"^\s*import\s+([^\n]+)$", re.MULTILINE)
COMMENT = re.compile(r"\s+--.*$")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
RH_ROOT = "research/rh/"


def parsed_imports(source):
    out = []
    for match in IMPORT.finditer(source):
        text = COMMENT.sub("", match.group(1))
        for name in text.split():
            if MODULE.fullmatch(name) and name not in out:
                out.append(name)
    return out


def module_name(path):
    # Research modules use basenames; AEGISOverlay imports are qualified.
    if path.startswith("AEGISOverlay/") and path.endswith(".lean"):
        return path[:-5].replace("/", ".")
    return Path(path).stem


def verified_local_overlay_sources():
    """Load only tracked, unchanged overlay Lean blobs from this exact checkout."""
    if not Path("AEGISOverlay").is_dir():
        raise RuntimeError("LOCAL_OVERLAY_DIRECTORY_MISSING")
    entries = subprocess.check_output(
        ["git", "ls-tree", "-r", "HEAD", "--", "AEGISOverlay"], text=True)
    result = {}
    for entry in entries.splitlines():
        metadata, path = entry.split("\t", 1)
        mode, kind, expected_sha = metadata.split(" ")
        if not path.endswith(".lean"):
            continue
        if mode != "100644" or kind != "blob" or not path.startswith("AEGISOverlay/"):
            raise RuntimeError("OVERLAY_TREE_ENTRY_INVALID:" + path)
        source = Path(path)
        if not source.is_file() or source.is_symlink():
            raise RuntimeError("OVERLAY_SOURCE_MISSING:" + path)
        if git_blob_sha(source.read_bytes()) != expected_sha:
            raise RuntimeError("OVERLAY_SOURCE_DRIFT:" + path)
        result[path] = expected_sha
    if not result:
        raise RuntimeError("NO_VERIFIED_OVERLAY_SOURCES")
    return result


def git_blob_sha(raw):
    data = ("blob " + str(len(raw)) + "\0").encode("ascii") + raw
    return hashlib.sha1(data).hexdigest()


def remote_blob(repo, sha, token, api="https://api.github.com"):
    req = urllib.request.Request(
        api + "/repos/" + repo + "/git/blobs/" + sha,
        headers={"Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28",
                 "User-Agent": "AEGIS-RH-import-coherence-v1",
                 "Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=45) as response:
        result = json.load(response)
    if result.get("sha") != sha:
        raise RuntimeError("BLOB_SHA_MISMATCH:" + sha)
    if result.get("encoding") != "base64":
        raise RuntimeError("UNEXPECTED_ENCODING:" + sha)
    raw = base64.b64decode(result["content"], validate=False)
    if len(raw) != result.get("size") or git_blob_sha(raw) != sha:
        raise RuntimeError("GIT_BLOB_INTEGRITY_FAIL:" + sha)
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise RuntimeError("SOURCE_NOT_UTF8:" + sha) from exc


def classify(graph, source_by_blob, local_sources, blob_limit=1200):
    target = graph["target_exact_sha"]
    if graph.get("errors") or not graph.get("inventory_complete"):
        raise RuntimeError("UPSTREAM_INVENTORY_NOT_COMPLETE")
    if graph.get("repository") is None:
        raise RuntimeError("MISSING_REPOSITORY_IDENTITY")
    trees = graph["tree_by_sha"]
    if target not in trees:
        raise RuntimeError("MISSING_EXACT_TARGET_TREE")
    target_paths = trees[target]["sources"]
    if len(target_paths) == 0:
        raise RuntimeError("EMPTY_TARGET_RH_TREE")
    candidates = defaultdict(lambda: defaultdict(set))
    for node in graph["github_pr_base_graph"]["nodes"]:
        source_paths = trees.get(node["head_sha"], {}).get("sources", {})
        for path, sha in source_paths.items():
            if path not in target_paths or target_paths[path] != sha:
                candidates[path][sha].add(node["number"])
    remote_shas = sorted({sha for variants in candidates.values() for sha in variants})
    if len(remote_shas) > blob_limit:
        raise RuntimeError("BLOB_COUNT_EXCEEDS_BOUND:" + str(len(remote_shas)))
    absent = {p for p in candidates if p not in target_paths}
    divergent = {p for p in candidates if p in target_paths}
    all_names = defaultdict(set)
    for path in set(target_paths) | set(candidates) | set(local_sources):
        all_names[module_name(path)].add(path)
    # The local checkout must match the exact candidate Git tree contents.
    target_imports = {}
    actual_source_count = 0
    for path, sha in sorted(target_paths.items()):
        raw_path = Path(path)
        if not raw_path.is_file():
            raise RuntimeError("MISSING_LOCAL_TARGET_SOURCE:" + path)
        raw = raw_path.read_bytes()
        if git_blob_sha(raw) != sha:
            raise RuntimeError("TARGET_SOURCE_SHA_MISMATCH:" + path)
        target_imports[path] = parsed_imports(raw.decode("utf-8"))
        actual_source_count += 1
    local_names = {module_name(path) for path in set(target_paths) | set(local_sources)}
    missing_names = {module_name(p) for p in absent}
    edges = set()
    external = set()
    candidate_detail = []
    for path, variants in sorted(candidates.items()):
        for sha, prs in sorted(variants.items()):
            if sha not in source_by_blob:
                raise RuntimeError("UNFETCHED_BLOB:" + sha)
            content = source_by_blob[sha]
            imports = parsed_imports(content)
            neighbors = []
            required_new = []
            unknown = []
            ambiguous = []
            for name in imports:
                existing = all_names.get(name, set())
                if len(existing) > 1:
                    ambiguous.append({"import": name, "candidates": sorted(existing)})
                elif name in missing_names and name not in local_names:
                    required_new.append(name)
                    neighbors.append(name)
                    edges.add((module_name(path), name))
                elif name not in local_names:
                    unknown.append(name)
                    external.add(name)
            ambiguity = len(all_names[module_name(path)]) > 1
            # External imports may be legitimate Mathlib / LiCriterion modules.
            # They cannot be resolved by this RH-scoped source inventory.
            status = ("BLOCKED_NAME_COLLISION" if ambiguity or ambiguous else
                      "NEEDS_MISSING_RH_IMPORTS" if required_new else
                      "REQUIRES_EXTERNAL_IMPORT_CHECK" if unknown else
                      "SOURCE_READY_FOR_LEAN_PROBE")
            if path in divergent:
                status = "DIVERGENT_EXISTING_SOURCE_REVIEW_REQUIRED"
            candidate_detail.append({
                "path": path, "source_sha": sha, "source_prs": sorted(prs),
                "is_absent": path in absent,
                "status": status, "imports": imports,
                "missing_RH_imports": sorted(set(required_new)),
                "external_or_other_tree_imports": sorted(set(unknown)),
                "ambiguous_imports": ambiguous, "ambiguous_module_name": ambiguity})
    target_imports_missing = []
    for path, imports in target_imports.items():
        for name in imports:
            if name in missing_names and name not in local_names:
                target_imports_missing.append({"source": path, "missing": name})
    edge_list = sorted([{"from": a, "to": b} for a, b in edges],
                       key=lambda x: (x["from"], x["to"]))
    graph_map = defaultdict(list)
    for a, b in edges:
        graph_map[a].append(b)
    color = {}
    cycles = []
    def visit(name, stack):
        if color.get(name) == 1:
            cycles.append(stack[stack.index(name):] + [name])
        elif color.get(name) is None:
            color[name] = 1
            for nxt in graph_map[name]:
                visit(nxt, stack + [nxt])
            color[name] = 2
    for module in sorted(graph_map):
        if color.get(module) is None:
            visit(module, [module])
    return {
        "schema": "aegis.rh.import-coherence.v1",
        "target_exact_sha": target,
        "base_source_count": actual_source_count,
        "absent_paths": len(absent),
        "divergent_existing_paths": len(divergent),
        "candidate_blob_count": len(remote_shas),
        "candidate_path_variants": len(candidate_detail),
        "classification_counts": dict(Counter(v["status"] for v in candidate_detail)),
        "target_imports_absent_modules": target_imports_missing,
        "missing_to_missing_edges": edge_list,
        "import_cycles": cycles,
        "scope_external_imports_not_bound": sorted(external),
        "candidates": candidate_detail,
        "verified_local_overlay_source_count": len(local_sources),
        "verified_local_overlay_source_blobs": dict(sorted(local_sources.items())),
        "verified_local_overlay_modules": sorted(module_name(p) for p in local_sources),
        "source_only_audit_pass": True,
        "kernel_type_audit_pass": None,
        "auto_cherry_pick_authorized": False
    }


def reconcile_archived_recovery(root, restored, manifest_file):
    """Compare recovered originals with the already maintained consolidated source archive.

    A manifest digest match means that source was already inventoried for replay,
    not that the compiled theorem or RH has been validated here.
    """
    entries = json.loads(Path(manifest_file).read_text(encoding="utf-8"))
    if not isinstance(entries, list):
        raise RuntimeError("BAD_CONSOLIDATED_MANIFEST")
    by_path = {}
    for row in entries:
        if not all(key in row for key in ("module", "path", "sha256")):
            raise RuntimeError("INCOMPLETE_ARCHIVE_SOURCE_ROW")
        if row["path"] in by_path:
            raise RuntimeError("DUPLICATE_CONSOLIDATED_PATH:" + row["path"])
        by_path[row["path"]] = row
    matching, conflicting, not_in_archive = [], [], []
    for row in restored:
        path = row["path"]
        actual = (root / path).read_bytes()
        if git_blob_sha(actual) != row["blob_sha"]:
            raise RuntimeError("BAD_RECOVERED_BLOB:" + path)
        digest = hashlib.sha256(actual).hexdigest()
        archived = by_path.get(path)
        record = {"path": path, "git_blob_sha": row["blob_sha"],
                  "sha256": digest, "source_prs": row["prs"]}
        if archived is None:
            not_in_archive.append(record)
        elif digest == archived["sha256"]:
            matching.append({**record, "archived_module": archived["module"]})
        else:
            conflicting.append({**record, "archived_module": archived["module"],
                                "archived_sha256": archived["sha256"]})
    return {
        "schema": "aegis.rh.recovered-to-consolidated-source.v1",
        "archive_manifest": str(manifest_file),
        "archive_entries": len(entries),
        "recovered_count": len(restored),
        "source_exact_archive_matches": matching,
        "different_version_from_archive": conflicting,
        "not_present_in_archive": not_in_archive,
        "summary": {"matched": len(matching), "different": len(conflicting),
                    "not_archived": len(not_in_archive)},
        "historical_compilation_not_replayed": True,
        "kernel_closure_verified": None
    }


def self_test():
    assert parsed_imports("import A B\n-- import NO\nimport Mathlib.Data.Real.Basic\n") == ["A", "B", "Mathlib.Data.Real.Basic"]
    assert module_name("research/rh/other/A.lean") == "A"
    assert module_name("AEGISOverlay/ExampleV1.lean") == "AEGISOverlay.ExampleV1"
    assert git_blob_sha(b"x") == "c1b0730e0133447badcfd47fd144e254807b06e1"
    sample = {"target_exact_sha": "A", "repository": "org/repo",
              "inventory_complete": True, "errors": [],
              "tree_by_sha": {
                  "A": {"sources": {"research/rh/base/MathA.lean": git_blob_sha(b"import Mathlib\n")}},
                  "B": {"sources": {"research/rh/new/NewB.lean": git_blob_sha(b"import MathA\n")}}},
              "github_pr_base_graph": {"nodes": [{"number": 9, "head_sha": "B"}]}}
    from tempfile import TemporaryDirectory
    import os as _os
    from contextlib import contextmanager
    @contextmanager
    def cwd(path):
        previous = _os.getcwd()
        try:
            _os.chdir(path)
            yield
        finally:
            _os.chdir(previous)
    with TemporaryDirectory() as folder, cwd(folder):
        p = Path("research/rh/base/MathA.lean")
        p.parent.mkdir(parents=True)
        p.write_bytes(b"import Mathlib\n")
        result = classify(sample, {git_blob_sha(b"import MathA\n"): "import MathA\n"}, {})
        new_source = "import MathA AEGISOverlay.ExampleV1\n"
        variant = json.loads(json.dumps(sample))
        variant["tree_by_sha"]["B"]["sources"]["research/rh/new/NewB.lean"] = git_blob_sha(new_source.encode())
        overlay = {"AEGISOverlay/ExampleV1.lean": git_blob_sha(b"import Mathlib\n")}
        joined = classify(variant, {git_blob_sha(new_source.encode()): new_source}, overlay)
        assert "AEGISOverlay.ExampleV1" not in joined["scope_external_imports_not_bound"]
        assert joined["verified_local_overlay_source_blobs"] == overlay
        assert joined["verified_local_overlay_source_count"] == 1
    assert result["absent_paths"] == 1
    assert result["classification_counts"] == {"SOURCE_READY_FOR_LEAN_PROBE": 1}
    assert not result["auto_cherry_pick_authorized"]
    from tempfile import TemporaryDirectory as _Temp
    with _Temp() as folder:
        home = Path(folder)
        p = "research/rh/test/Example.lean"
        raw = b"import Mathlib\n"
        f = home / p
        f.parent.mkdir(parents=True)
        f.write_bytes(raw)
        archive = home / "manifest.json"
        archive.write_text(json.dumps([{"module": "Example", "path": p,
                                        "sha256": hashlib.sha256(raw).hexdigest()}]))
        expected = [{"path": p, "blob_sha": git_blob_sha(raw), "prs": [1]}]
        reconciliation = reconcile_archived_recovery(home, expected, archive)
        assert reconciliation["summary"] == {"matched": 1, "different": 0,
                                                "not_archived": 0}
        archive.write_text(json.dumps([{"module": "Example", "path": p,
                                        "sha256": hashlib.sha256(b"wrong").hexdigest()}]))
        assert reconcile_archived_recovery(home, expected, archive)["summary"]["different"] == 1
    print("IMPORT_SELF_TEST_PASS")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"))
    ap.add_argument("--output")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--recovery-dir", default=None)
    ap.add_argument("--consolidated-manifest", default="research/rh/consolidated_v1/manifest.json")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.graph or not args.repo or not args.output:
        ap.error("--graph, --repo, --output are required")
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        ap.error("GITHUB_TOKEN is required")
    graph = json.loads(Path(args.graph).read_text())
    actual_head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    if graph.get("target_exact_sha") != actual_head:
        raise RuntimeError("TARGET_CHECKOUT_HEAD_MISMATCH")
    if graph.get("repository") != args.repo:
        raise RuntimeError("GRAPH_REPOSITORY_MISMATCH")
    trees = graph["tree_by_sha"]
    target_paths = trees[graph["target_exact_sha"]]["sources"]
    remote = sorted({
        sha for x in graph["github_pr_base_graph"]["nodes"]
        for path, sha in trees.get(x["head_sha"], {}).get("sources", {}).items()
        if target_paths.get(path) != sha
    })
    source_by_blob = {}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(remote_blob, args.repo, sha, token): sha for sha in remote}
        for f in as_completed(futures):
            sha = futures[f]
            source_by_blob[sha] = f.result()
    result = classify(graph, source_by_blob, verified_local_overlay_sources())
    if args.recovery_dir:
        target_paths = trees[graph["target_exact_sha"]]["sources"]
        variants = defaultdict(lambda: defaultdict(set))
        for node in graph["github_pr_base_graph"]["nodes"]:
            for path, sha in trees.get(node["head_sha"], {}).get("sources", {}).items():
                if path not in target_paths:
                    variants[path][sha].add(node["number"])
        root = Path(args.recovery_dir)
        if root.exists() and any(root.iterdir()):
            raise RuntimeError("RECOVERY_DIRECTORY_NOT_EMPTY")
        root.mkdir(parents=True, exist_ok=True)
        restored, withheld = [], []
        for path, copies in sorted(variants.items()):
            if not path.startswith(RH_ROOT) or ".." in Path(path).parts:
                raise RuntimeError("UNSAFE_RECOVERY_PATH:" + path)
            if len(copies) != 1:
                withheld.append({"path": path, "sha_variants": sorted(copies)})
                continue
            sha, ids = next(iter(copies.items()))
            raw = source_by_blob[sha].encode("utf-8")
            if git_blob_sha(raw) != sha:
                raise RuntimeError("RESTORE_BLOB_MISMATCH:" + path)
            destination = root / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            with destination.open("xb") as f:
                f.write(raw)
            restored.append({"path": path, "blob_sha": sha, "prs": sorted(ids)})
        receipt = {"schema": "aegis.rh.source-recovery.v1",
                   "original_target_sha": graph["target_exact_sha"],
                   "not_a_lean_proof": True, "restored": restored,
                   "withheld_multiversion": withheld}
        result["archive_reconciliation"] = reconcile_archived_recovery(
            root, restored, args.consolidated_manifest)
        (root / "ARCHIVE_RECONCILIATION.json").write_text(
            json.dumps(result["archive_reconciliation"], indent=2, sort_keys=True) + "\n")
        (root / "RECOVERY_MANIFEST.json").write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        result["source_recovery"] = {
            "restored": len(restored), "withheld": len(withheld),
            "dir": args.recovery_dir,
            "wrote_to_tracked_source": False,
            "kernel_proof_claim": False}
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "base_source_count", "absent_paths", "divergent_existing_paths",
        "candidate_blob_count", "candidate_path_variants",
        "classification_counts", "import_cycles",
        "target_imports_absent_modules", "source_only_audit_pass",
        "kernel_type_audit_pass")}, indent=2))
    if "archive_reconciliation" in result:
        print("ARCHIVE_RECONCILIATION " + json.dumps(result["archive_reconciliation"]["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
