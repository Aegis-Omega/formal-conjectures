#!/usr/bin/env python3
"""Exact-head, source-only staging of missing Lean imports recovered from PR history.

Uses the existing all-PR graph. Never claims mathematical or kernel verification.
No fixed theorem, cell, branch, or PR list; no tracked-source mutation.
"""
import argparse
from collections import defaultdict
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
import tempfile
import zipfile


def git_blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def safe_path(name):
    p = PurePosixPath(name)
    if not name.startswith("research/rh/") or p.is_absolute() or ".." in p.parts or not name.endswith(".lean"):
        raise ValueError("UNSAFE_SOURCE_PATH:" + name)
    return name


class Recovery:
    def __init__(self, root):
        self.root = Path(root)
        self.archive = zipfile.ZipFile(self.root) if self.root.is_file() else None
        self.prefix = "rh_source_recovery/" if self.archive else ""

    def read(self, name):
        name = safe_path(name)
        if self.archive:
            return self.archive.read(self.prefix + name)
        path = self.root / name
        if path.is_symlink() or not path.is_file():
            raise ValueError("RECOVERED_SOURCE_MISSING:" + name)
        return path.read_bytes()

    def manifest(self):
        name = self.prefix + "RECOVERY_MANIFEST.json"
        return json.loads(self.archive.read(name) if self.archive else
                          (self.root / name).read_bytes())


def build(graph, imports, recovery, stage=None):
    manifest = recovery.manifest()
    head = graph["target_exact_sha"]
    if head != imports["target_exact_sha"] or head != manifest["original_target_sha"]:
        raise ValueError("EXACT_HEAD_MISMATCH")
    if imports.get("source_only_audit_pass") is not True:
        raise ValueError("SOURCE_AUDIT_NOT_PASS")
    by_name = defaultdict(list)
    checked = {}
    for entry in manifest["restored"]:
        name = safe_path(entry["path"])
        raw = recovery.read(name)
        if git_blob(raw) != entry["blob_sha"]:
            raise ValueError("SOURCE_BLOB_SHA_MISMATCH:" + name)
        if name in checked:
            raise ValueError("DUPLICATE_PATH:" + name)
        checked[name] = entry["blob_sha"]
        by_name[PurePosixPath(name).stem].append(entry)
    missing_by_consumer = defaultdict(set)
    for item in imports["target_imports_absent_modules"]:
        missing_by_consumer[item["source"]].add(item["missing"])
    selected, unresolved, ambiguous, consumers = {}, [], [], []
    for consumer, names in sorted(missing_by_consumer.items()):
        resolved = []
        blocked = []
        for name in sorted(names):
            options = by_name.get(name, [])
            if len(options) == 1:
                entry = options[0]
                selected[name] = entry
                resolved.append({"module": name, "path": entry["path"],
                                 "blob_sha": entry["blob_sha"],
                                 "source_prs": entry.get("prs", [])})
            else:
                record = {"consumer": consumer, "module": name,
                          "candidate_paths": sorted(x["path"] for x in options)}
                (unresolved if not options else ambiguous).append(record)
                blocked.append(name)
        consumers.append({"consumer": consumer, "import_count": len(names),
                          "recovered": resolved, "blocked": blocked,
                          "source_stage_ready": not blocked})
    target_paths = graph["tree_by_sha"][head]["sources"]
    existing = defaultdict(set)
    for path in target_paths:
        if path.endswith(".lean"):
            existing[PurePosixPath(path).stem].add(path)
    # Recursively use verified historical providers for the complete
    # missing-source import closure, not just the first import layer.
    pending = [(name, item) for name, item in selected.items()]
    transitive = []
    while pending:
        consumer_name, item = pending.pop()
        source = recovery.read(item["path"]).decode("utf-8")
        for dependency in re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_]*)\s*$",
                                     source, flags=re.MULTILINE):
            if dependency in selected or dependency in existing:
                continue
            providers = by_name.get(dependency, [])
            if len(providers) == 1:
                provider = providers[0]
                selected[dependency] = provider
                pending.append((dependency, provider))
                transitive.append({"consumer": consumer_name, "module": dependency,
                                   "path": provider["path"],
                                   "blob_sha": provider["blob_sha"]})
            elif len(providers) > 1:
                ambiguous.append({"consumer": consumer_name, "module": dependency,
                                  "candidate_paths": sorted(
                                      x["path"] for x in providers)})
            # Sources outside historical research/rh are resolved separately
            # by actual Lake imports; never hallucinate an external provider.
    for name, item in selected.items():
        if name in existing:
            ambiguous.append({"consumer": "target_tree", "module": name,
                              "candidate_paths": sorted(existing[name]) + [item["path"]]})
    status = ("HOLD_AMBIGUOUS_OR_MISSING" if unresolved or ambiguous
              else "SOURCE_STAGE_READY_KERNEL_UNVERIFIED")
    receipt = {"schema": "aegis.rh.source-reuse-plan.v1",
               "repository": graph["repository"], "exact_head": head,
               "status": status, "source_only_audit_pass": True,
               "kernel_verified": None, "unconditional_rh_verified": None,
               "historical_blobs_checked": len(checked),
               "missing_import_occurrences": sum(len(x) for x in missing_by_consumer.values()),
               "uniquely_recovered": len(selected),
               "transitive_recovered": transitive,
               "transitive_recovered_count": len(transitive),
               "unresolved": unresolved, "ambiguous": ambiguous,
               "consumers": sorted(consumers, key=lambda x: (-x["import_count"], x["consumer"])),
               "stage_root": None, "no_merge_no_deploy_no_spend": True}
    if stage is not None:
        if status != "SOURCE_STAGE_READY_KERNEL_UNVERIFIED":
            raise ValueError(status)
        stage = Path(stage)
        if stage.exists() and any(stage.iterdir()):
            raise ValueError("NONEMPTY_STAGE_DIRECTORY")
        stage.mkdir(parents=True, exist_ok=True)
        for name, entry in sorted(selected.items()):
            dest = stage / (name + ".lean")
            if dest.exists():
                raise ValueError("STAGE_COLLISION:" + name)
            dest.write_bytes(recovery.read(entry["path"]))
        receipt["stage_root"] = str(stage)
    return receipt


def self_test():
    with tempfile.TemporaryDirectory() as td:
        d = Path(td)
        root = d / "recovered"
        file = root / "research/rh/test/AutoModule.lean"
        file.parent.mkdir(parents=True)
        original = b"import NestedModule\ntheorem automatic : True := trivial\n"
        file.write_bytes(original)
        extra = root / "research/rh/test/NestedModule.lean"
        extra.write_bytes(b"theorem nested : True := trivial\n")
        head = "a" * 40
        (root / "RECOVERY_MANIFEST.json").write_text(json.dumps({
            "original_target_sha": head, "restored": [
                {"path": "research/rh/test/AutoModule.lean", "blob_sha": git_blob(original)},
                {"path": "research/rh/test/NestedModule.lean",
                 "blob_sha": git_blob(extra.read_bytes())}]}))
        graph = {"target_exact_sha": head, "repository": "test/repo",
                 "tree_by_sha": {head: {"sources": {"research/rh/test/Consumer.lean": "b"*40}}}}
        imports = {"target_exact_sha": head, "source_only_audit_pass": True,
                   "target_imports_absent_modules": [
                       {"source": "research/rh/test/Consumer.lean", "missing": "AutoModule"}]}
        receipt = build(graph, imports, Recovery(root), d / "stage")
        assert receipt["uniquely_recovered"] == 2 and receipt["kernel_verified"] is None
        assert receipt["transitive_recovered_count"] == 1
        assert (d / "stage/NestedModule.lean").read_bytes() == extra.read_bytes()
        assert (d / "stage/AutoModule.lean").read_bytes() == original
        try:
            build({**graph, "target_exact_sha": "c"*40}, imports, Recovery(root))
            raise AssertionError("stale graph accepted")
        except ValueError as e:
            assert "EXACT_HEAD" in str(e)
        file.write_bytes(b"corrupt")
        try:
            build(graph, imports, Recovery(root))
            raise AssertionError("invalid Git blob accepted")
        except ValueError as e:
            assert "SOURCE_BLOB_SHA_MISMATCH" in str(e)
        file.write_bytes(original)
        negative = {**imports, "target_imports_absent_modules": [
            {"source": "consumer", "missing": "Missing"}]}
        assert build(graph, negative, Recovery(root))["status"] == "HOLD_AMBIGUOUS_OR_MISSING"
        try:
            build(graph, negative, Recovery(root), d / "badstage")
            raise AssertionError("staged missing import")
        except ValueError as e:
            assert "HOLD_AMBIGUOUS_OR_MISSING" in str(e)
    print("SELF_TEST_PASS exact-head+blob+stage+missing+fail-closed")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--graph")
    p.add_argument("--imports")
    p.add_argument("--recovery")
    p.add_argument("--output")
    p.add_argument("--stage-dir")
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    if a.self_test:
        self_test()
        return
    if not all([a.graph, a.imports, a.recovery, a.output]):
        p.error("--graph --imports --recovery --output are required")
    receipt = build(json.loads(Path(a.graph).read_text()),
                    json.loads(Path(a.imports).read_text()),
                    Recovery(a.recovery), a.stage_dir)
    Path(a.output).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: receipt[k] for k in
          ("exact_head", "status", "historical_blobs_checked",
           "missing_import_occurrences", "uniquely_recovered", "kernel_verified")}, indent=2))
    if receipt["status"] != "SOURCE_STAGE_READY_KERNEL_UNVERIFIED":
        raise SystemExit(receipt["status"])


if __name__ == "__main__":
    main()
