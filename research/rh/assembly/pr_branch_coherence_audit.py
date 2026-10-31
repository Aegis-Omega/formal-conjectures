#!/usr/bin/env python3
"""Live, source-bound inventory of every GitHub PR/branch and RH source graft path.

This is a Git/source coherence audit, not a Lean proof certificate.
Never infer theorem closure from a green check, source match, or PR metadata.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


class GitHub:
    def __init__(self, repo, token, api="https://api.github.com"):
        if len(repo.split("/")) != 2:
            raise ValueError("Expected owner/repository")
        self.prefix = api.rstrip("/") + "/repos/" + repo
        self.token = token
        self._cache = {}

    def get(self, suffix):
        if suffix in self._cache:
            return self._cache[suffix]
        headers = {"Accept": "application/vnd.github+json",
                   "User-Agent": "AEGIS-RH-source-coherence-auditor",
                   "X-GitHub-Api-Version": "2022-11-28"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        for attempt in range(3):
            req = urllib.request.Request(self.prefix + suffix, headers=headers)
            try:
                with urllib.request.urlopen(req, timeout=45) as response:
                    result = json.load(response)
                self._cache[suffix] = result
                return result
            except urllib.error.HTTPError as err:
                if err.code not in (429, 500, 502, 503, 504) or attempt == 2:
                    raise
                time.sleep(2 ** attempt)
        raise RuntimeError("Unreachable HTTP retry state")

    def pages(self, path):
        rows = []
        for page in range(1, 101):
            separator = "&" if "?" in path else "?"
            part = self.get(path + separator + "per_page=100&page=" + str(page))
            if not isinstance(part, list):
                raise ValueError("Pagination returned non-list for " + path)
            rows.extend(part)
            if len(part) < 100:
                return rows
        raise RuntimeError("PAGINATION_BOUND_REACHED:" + path)


def rh_tree(client, sha):
    """Read the RH subtree from immutable Git tree objects, not live default branch."""
    root = client.get("/git/trees/" + sha)
    if root.get("truncated"):
        raise RuntimeError("TRUNCATED_ROOT_TREE:" + sha)
    entries = root.get("tree", [])
    for segment in ("research", "rh"):
        node = next((t for t in entries if t["path"] == segment and
                     t["type"] == "tree"), None)
        if node is None:
            return {"tree_sha": None, "sources": {}}
        parent = client.get("/git/trees/" + node["sha"])
        if parent.get("truncated"):
            raise RuntimeError("TRUNCATED_PARENT_TREE:" + node["sha"])
        entries = parent.get("tree", [])
    tree = client.get("/git/trees/" + node["sha"] + "?recursive=1")
    if tree.get("truncated"):
        raise RuntimeError("TRUNCATED_RH_TREE:" + node["sha"])
    source = {"research/rh/" + n["path"]: n["sha"] for n in tree.get("tree", [])
              if n["type"] == "blob" and n["path"].endswith(".lean")}
    return {"tree_sha": node["sha"], "sources": source}


def check_head(client, sha):
    payload = client.get("/commits/" + sha + "/check-runs?per_page=100")
    checks = payload.get("check_runs", [])
    result = [{"name": r["name"], "status": r["status"],
               "conclusion": r.get("conclusion"), "id": r["id"]}
              for r in checks]
    return {"observed": result,
            "total_count": payload.get("total_count"),
            "complete": len(result) == payload.get("total_count")}


def successors(edges, node):
    graph = {}
    for edge in edges:
        graph.setdefault(edge["from_pr"], []).append(edge["to_pr"])
    seen = set()
    todo = list(graph.get(node, []))
    while todo:
        candidate = todo.pop()
        if candidate in seen:
            continue
        seen.add(candidate)
        todo.extend(graph.get(candidate, []))
    return sorted(seen)


def build_report(client, repo, target_pr, workers=5):
    all_prs = client.pages("/pulls?state=all")
    branches = client.pages("/branches")
    by_ref = {p["head"]["ref"]: p for p in all_prs}
    live_heads = {b["name"]: b["commit"]["sha"] for b in branches}
    pr_numbers = {p["number"] for p in all_prs}
    if target_pr not in pr_numbers:
        raise ValueError("TARGET_PR_NOT_FOUND:" + str(target_pr))
    by_number = {p["number"]: p for p in all_prs}
    nodes = [{
        "number": p["number"], "state": p["state"], "draft": p["draft"],
        "merged": p.get("merged_at") is not None, "head_ref": p["head"]["ref"],
        "head_sha": p["head"]["sha"], "base_ref": p["base"]["ref"],
        "base_sha": p["base"]["sha"], "title": p["title"]
    } for p in all_prs]
    edges = [{
        "from_pr": by_ref[p["base"]["ref"]]["number"],
        "to_pr": p["number"], "kind": "github_base_ref"
    } for p in all_prs if p["base"]["ref"] in by_ref]
    live_mismatches = [{
        "pr": n["number"], "expected": n["head_sha"],
        "observed": live_heads.get(n["head_ref"])
    } for n in nodes if n["state"] == "open" and
        live_heads.get(n["head_ref"]) != n["head_sha"]]

    sha_set = sorted({n["head_sha"] for n in nodes} |
                     {b["commit"]["sha"] for b in branches})
    tree_by_sha = {}
    errors = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(rh_tree, client, sha): sha for sha in sha_set}
        for future in concurrent.futures.as_completed(futures):
            sha = futures[future]
            try:
                tree_by_sha[sha] = future.result()
            except Exception as exc:
                errors.append({"stage": "rh_tree", "sha": sha, "error": str(exc)})

    base_sources = tree_by_sha.get(by_number[target_pr]["head"]["sha"], {}).get("sources", {})
    grafts = []
    for n in sorted(nodes, key=lambda x: x["number"]):
        src = tree_by_sha.get(n["head_sha"], {}).get("sources")
        if src is None:
            grafts.append({"pr": n["number"], "status": "SOURCE_UNAVAILABLE"})
            continue
        reused = [p for p, sha in src.items() if base_sources.get(p) == sha]
        missing = [p for p in src if p not in base_sources]
        divergent = [p for p, sha in src.items()
                     if p in base_sources and base_sources[p] != sha]
        grafts.append({
            "pr": n["number"], "source_count": len(src),
            "reused_exact_count": len(reused), "absent_on_target_count": len(missing),
            "divergent_same_path_count": len(divergent),
            "absent_on_target_paths": sorted(missing),
            "divergent_same_path": [{
                "path": path, "source_blob": src[path],
                "target_blob": base_sources[path]
            } for path in sorted(divergent)]
        })
    # A unique source SHA is necessary, but not sufficient, for proof reuse.
    sources = {}
    for n in nodes:
        for path, sha in tree_by_sha.get(n["head_sha"], {}).get("sources", {}).items():
            sources.setdefault(path, {}).setdefault(sha, []).append(n["number"])
    divergent_paths = [{
        "path": path,
        "variants": [{"sha": sha, "prs": sorted(ids)}
                     for sha, ids in sorted(variants.items())]
    } for path, variants in sorted(sources.items()) if len(variants) > 1]
    checks_by_sha = {}
    open_sha = sorted({n["head_sha"] for n in nodes if n["state"] == "open"})
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(check_head, client, sha): sha for sha in open_sha}
        for future in concurrent.futures.as_completed(futures):
            sha = futures[future]
            try:
                checks_by_sha[sha] = future.result()
                if not checks_by_sha[sha]["complete"]:
                    errors.append({"stage": "checks_pagination", "sha": sha})
            except Exception as exc:
                errors.append({"stage": "check_runs", "sha": sha, "error": str(exc)})
    no_pr_head = sorted(b["name"] for b in branches
                        if b["name"] not in by_ref)
    unused_branches = sorted(b for b in no_pr_head
                             if not any(n["base_ref"] == b for n in nodes))
    report = {
        "schema": "aegis.rh.all-pr-source-paths.v1",
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "repository": repo, "target_pr": target_pr,
        "target_exact_sha": by_number[target_pr]["head"]["sha"],
        "scope": {"all_prs": True, "all_live_branches": True,
                  "all_pr_head_sha_including_deleted_branches": True},
        "counts": {
            "prs": len(nodes), "live_branches": len(branches),
            "open_prs": sum(n["state"] == "open" for n in nodes),
            "merged_prs": sum(n["merged"] for n in nodes),
            "github_base_edges": len(edges),
            "unique_commit_trees_requested": len(sha_set),
            "rh_trees_fetched": len(tree_by_sha),
            "open_heads_with_check_results": len(checks_by_sha),
            "source_paths_with_divergent_blobs": len(divergent_paths),
            "unreferenced_branches": len(unused_branches)
        },
        "github_pr_base_graph": {"nodes": nodes, "edges": edges,
                                  "target_descendants": successors(edges, target_pr)},
        "branch_inventory": [{
            "name": b["name"], "sha": b["commit"]["sha"]
        } for b in branches],
        "branches_without_pr_head": no_pr_head,
        "branches_not_head_or_base": unused_branches,
        "open_head_mismatches": live_mismatches,
        "tree_by_sha": tree_by_sha,
        "source_graft_candidates_by_pr": grafts,
        "source_divergences": divergent_paths,
        "checks_by_exact_sha": checks_by_sha,
        "errors": sorted(errors, key=lambda x: (x["stage"], x.get("sha", ""))),
        "inventory_complete": not errors and not live_mismatches,
        "formal_kernel_coherence_verified": None
    }
    return report


def fake_test():
    """Synthetic two-PR replay, exercises page counting, divergence and ancestry."""
    a = {"number": 1, "head": {"ref": "alpha", "sha": "shaA"},
         "base": {"ref": "main", "sha": "shaM"}, "state": "open",
         "draft": False, "merged_at": None, "title": "first"}
    b = {"number": 2, "head": {"ref": "beta", "sha": "shaB"},
         "base": {"ref": "alpha", "sha": "shaA"}, "state": "open",
         "draft": True, "merged_at": None, "title": "second"}
    class Fake:
        def pages(self, url):
            return [a, b] if url.startswith("/pulls") else [
                {"name": n, "commit": {"sha": s}} for n, s in
                [("main", "shaM"), ("alpha", "shaA"), ("beta", "shaB")]]
        def get(self, url):
            if url.startswith("/commits/"):
                return {"check_runs": [], "total_count": 0}
            name = url.split("/git/trees/")[1].split("?")[0]
            if name in ("shaA", "shaB", "shaM"):
                return {"tree": [{"path": "research", "type": "tree",
                                  "sha": "research" + name}]}
            if name.startswith("research"):
                return {"tree": [{"path": "rh", "type": "tree",
                                  "sha": "rh" + name[8:]}]}
            if name.startswith("rh"):
                version = name[2:]
                items = [{"path": "A.lean", "type": "blob", "sha": "blobA"}]
                if version == "shaB":
                    items.append({"path": "B.lean", "type": "blob", "sha": "blobB"})
                if version == "shaM":
                    items[0]["sha"] = "older"
                return {"tree": items, "truncated": False}
            raise AssertionError(url)
    result = build_report(Fake(), "example/repo", 1, workers=2)
    assert result["counts"]["prs"] == 2
    assert result["counts"]["live_branches"] == 3
    assert result["counts"]["github_base_edges"] == 1
    assert result["github_pr_base_graph"]["target_descendants"] == [2]
    assert result["inventory_complete"]
    assert result["formal_kernel_coherence_verified"] is None
    candidate = next(x for x in result["source_graft_candidates_by_pr"] if x["pr"] == 2)
    assert candidate["reused_exact_count"] == 1
    assert candidate["absent_on_target_count"] == 1
    assert candidate["divergent_same_path_count"] == 0
    print("SELF_TEST_PASS")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getenv("GITHUB_REPOSITORY", ""))
    ap.add_argument("--target-pr", type=int)
    ap.add_argument("--output")
    ap.add_argument("--workers", type=int, default=5)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        fake_test()
        return
    if not args.repo or not args.target_pr or not args.output:
        ap.error("--repo, --target-pr and --output required")
    token = os.getenv("GITHUB_TOKEN")
    if not token:
        ap.error("GITHUB_TOKEN missing; refusing unauthenticated partial inventory")
    report = build_report(GitHub(args.repo, token), args.repo,
                          args.target_pr, workers=args.workers)
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, ensure_ascii=False, sort_keys=True)
        f.write("\n")
    print(json.dumps({"counts": report["counts"], "inventory_complete":
                      report["inventory_complete"],
                      "errors": report["errors"][:10]}, indent=2))
    if not report["inventory_complete"]:
        raise SystemExit("INCOMPLETE_SOURCE_GRAPH_FAIL_CLOSED")


if __name__ == "__main__":
    main()
