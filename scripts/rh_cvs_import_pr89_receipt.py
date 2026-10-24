#!/usr/bin/env python3
"""Validate a pinned PR89 proof-source receipt and emit its required CvS-to-Weil import DAG.

No repository file is overwritten. The caller compiles selected source files
in topological order under the pinned Lean/Mathlib environment.
"""
import argparse
import hashlib
import json
import pathlib
import re

EXPECTED_HEAD = "5d7425dcc6f4137b2cf3f57bc953504135a388e6"
EXPECTED_MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
EXPECTED_LEAN = "4.33.1"
REQUIRED_ROOTS = (
    "AEGISOverlay.RHOptimizedSchurGlobalJoinV1",
    "AEGISOverlay.RHActualUniversalFineGramV1",
    "RHMomentDecayCofinalJoinV1",
)

def verify(root: pathlib.Path, output: pathlib.Path, checkout: pathlib.Path):
    if (root / "formal-conjectures-sha.txt").read_text().strip() != EXPECTED_HEAD:
        raise ValueError("PR89_RECEIPT_HEAD_MISMATCH")
    if (root / "mathlib-sha.txt").read_text().strip() != EXPECTED_MATHLIB:
        raise ValueError("PR89_RECEIPT_MATHLIB_MISMATCH")
    if EXPECTED_LEAN not in (root / "lean-version.txt").read_text():
        raise ValueError("PR89_RECEIPT_LEAN_PIN_MISMATCH")
    manifest = json.loads((root / "source-manifest.json").read_text())
    if not isinstance(manifest, list) or len(manifest) != 324:
        raise ValueError("PR89_RECEIPT_MANIFEST_CARDINALITY")
    source = {}
    deps = {}
    for row in manifest:
        name = row["module"]
        if name in source or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", name):
            raise ValueError("PR89_RECEIPT_BAD_MODULE " + name)
        path = root / "assembly" / "sources" / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError("PR89_RECEIPT_MISSING_SOURCE " + name)
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != row["sha256"]:
            raise ValueError("PR89_RECEIPT_SHA256_DRIFT " + name)
        imports = []
        for line in data.decode("utf-8").splitlines():
            if line.startswith("import "):
                imports.extend(line[7:].split())
        source[name] = path
        deps[name] = imports
    available = set(source)
    for name, imports in deps.items():
        for imp in imports:
            if imp not in available and imp != "Mathlib" and not imp.startswith("Mathlib."):
                raise ValueError("PR89_UNRESOLVED_SOURCE_IMPORT " + name + " -> " + imp)
    roots = set(REQUIRED_ROOTS)
    if not roots <= available:
        raise ValueError("PR89_RECEIPT_MISSING_ROOTS")
    closure = set()
    def visit(name):
        if name in closure:
            return
        closure.add(name)
        for imp in deps[name]:
            if imp in available:
                visit(imp)
    for name in roots:
        visit(name)
    seen = set()
    ordered = []
    for row in manifest:
        name = row["module"]
        if name in closure:
            if not (set(deps[name]) & available) <= seen:
                raise ValueError("PR89_RECEIPT_NONTOPOLOGICAL " + name)
            seen.add(name)
            ordered.append(name)
    if len(ordered) != len(closure) or len(ordered) != 272:
        raise ValueError("PR89_RECEIPT_ORDER_INVALID")
    for name in REQUIRED_ROOTS[:2]:
        current = checkout / (name.replace(".", "/") + ".lean")
        if current.is_file() and current.read_bytes() != source[name].read_bytes():
            raise ValueError("PR89_VS_PR90_ROOT_SOURCE_DRIFT " + name)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(
        name + "\t" + str(source[name]) for name in ordered
    ) + "\n")
    print(f"PR89_SOURCE_MANIFEST_SHA256_PASS total={len(manifest)} needed={len(ordered)}")
    print("PR89_ROOT_MODULES " + " ".join(REQUIRED_ROOTS))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipt", type=pathlib.Path, required=True)
    ap.add_argument("--order", type=pathlib.Path, required=True)
    ap.add_argument("--checkout", type=pathlib.Path, default=pathlib.Path("."))
    args = ap.parse_args()
    verify(args.receipt, args.order, args.checkout)
