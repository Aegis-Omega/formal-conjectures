#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Emit a source-bound RH frontier snapshot from local Lean files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

OFFICIAL = Path("FormalConjectures/Millennium/RiemannHypothesis.lean")
EQUIVALENTS = Path("FormalConjectures/Paper/RiemannHypothesisEquivalents.lean")

IMPORT = re.compile(r"^(?:public\s+)?import\s+(.+)$")
THEOREM = re.compile(r"^theorem\s+([A-Za-z0-9_'.]+)\s*:\s*(.*)\s*:=\s*by\s*$", re.S)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z0-9_'.]+)\s*$")
END = re.compile(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
PLACEHOLDER = re.compile(r"\b(?:sorry|sorryAx|admit)\b")


def parse_namespaced_theorems(source: str) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    namespaces: list[str] = []
    lines = source.splitlines()
    i = 0
    while i < len(lines):
        raw = lines[i]
        line_no = i + 1
        line = raw.split("--", 1)[0].strip()
        m = NAMESPACE.fullmatch(line)
        if m:
            namespaces.append(m.group(1))
            i += 1
            continue
        m = END.fullmatch(line)
        if m:
            name = m.group(1)
            if not namespaces:
                i += 1
                continue
            if name is None or namespaces[-1] == name:
                namespaces.pop()
            i += 1
            continue
        if not line.startswith("theorem "):
            i += 1
            continue

        start = i
        declaration = [line]
        while i + 1 < len(lines) and not re.search(r":=\s*by\s*$", declaration[-1]):
            i += 1
            declaration.append(lines[i].split("--", 1)[0].strip())
        m = THEOREM.fullmatch(" ".join(s for s in declaration if s))
        if m:
            name = m.group(1)
            fq_name = ".".join(namespaces + [name]) if namespaces else name
            out.append({"name": fq_name, "line": start + 1, "type": m.group(2)})
        i += 1
    return out


def parse_local_imports(source: str) -> list[str]:
    imports: list[str] = []
    for raw in source.splitlines():
        line = raw.split("--", 1)[0].strip()
        m = IMPORT.fullmatch(line)
        if not m:
            continue
        for token in m.group(1).split():
            if token.startswith("Mathlib.") or token == "FormalConjecturesUtil":
                continue
            imports.append(token)
    return sorted(set(imports))


def parse_placeholders(source: str) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for i, raw in enumerate(source.splitlines(), start=1):
        stripped = raw.split("--", 1)[0]
        for m in PLACEHOLDER.finditer(stripped):
            out.append({"line": i, "token": m.group(0)})
    return out


def snapshot(root: Path, files: list[Path]) -> dict[str, object]:
    per_file: dict[str, object] = {}
    theorem_total = 0
    placeholder_total = 0
    for rel in files:
        path = root / rel
        source = path.read_text(encoding="utf-8")
        theorems = parse_namespaced_theorems(source)
        placeholders = parse_placeholders(source)
        imports = parse_local_imports(source)
        theorem_total += len(theorems)
        placeholder_total += len(placeholders)
        per_file[rel.as_posix()] = {
            "theorems": theorems,
            "local_imports": imports,
            "placeholders": placeholders,
        }
    return {
        "schema": "aegis.rh.frontier.snapshot.v1",
        "summary": {
            "files_scanned": len(files),
            "theorem_count": theorem_total,
            "placeholder_count": placeholder_total,
            # Lexical absence of placeholders is NOT Lean kernel verification.
            "rh_closed_unconditionally": False,
            "rh_closure_evidence": "SOURCE_SCAN_ONLY_NOT_KERNEL_VERIFIED",
        },
        "files": per_file,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=Path("."))
    p.add_argument("--official", type=Path, default=OFFICIAL)
    p.add_argument("--equivalents", type=Path, default=EQUIVALENTS)
    p.add_argument("--output", type=Path)
    args = p.parse_args(argv)

    files = [args.official, args.equivalents]
    missing = [f.as_posix() for f in files if not (args.root / f).is_file()]
    if missing:
        print("RH_FRONTIER_SNAPSHOT=FAIL")
        print(json.dumps({"missing_files": missing}, sort_keys=True))
        return 1

    data = snapshot(args.root, files)
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
        print(f"RH_FRONTIER_SNAPSHOT=PASS OUTPUT={args.output}")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
