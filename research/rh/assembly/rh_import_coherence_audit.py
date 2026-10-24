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
    # Research modules conventionally use basename imports. Detect collisions.
    return Path(path).stem


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
    for path in set(target_paths) | set(candidates):
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
    local_names = {name for path in target_paths for name in (module_name(path),)}
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
        "source_only_audit_pass": True,
        "kernel_type_audit_pass": None,
        "auto_cherry_pick_authorized": False
    }


def self_test():
    assert parsed_imports("import A B\n-- import NO\nimport Mathlib.Data.Real.Basic\n") == ["A", "B", "Mathlib.Data.Real.Basic"]
    assert module_name("research/rh/other/A.lean") == "A"
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
    assert result["absent_paths"] == 1
    assert result["classification_counts"] == {"SOURCE_READY_FOR_LEAN_PROBE": 1}
    assert not result["auto_cherry_pick_authorized"]
    print("IMPORT_SELF_TEST_PASS")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"))
    ap.add_argument("--output")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--self-test", action="store_true")
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
    result = classify(graph, source_by_blob, {})
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "base_source_count", "absent_paths", "divergent_existing_paths",
        "candidate_blob_count", "candidate_path_variants",
        "classification_counts", "import_cycles",
        "target_imports_absent_modules", "source_only_audit_pass",
        "kernel_type_audit_pass")}, indent=2))


if __name__ == "__main__":
    main()
