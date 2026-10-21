# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Reject pre-scripted negative *RH proof admission* verdicts in active code.

Historical exact-source archives are deliberately excluded: they are immutable
evidence and do not determine current proof admission.
Only a pinned Lean proof-term/type and axiom audit may emit a positive verdict.
"""
from __future__ import annotations

import ast
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ACTIVE_PREFIXES = (
    ".github/workflows/",
    "scripts/",
    "research/rh/assembly/",
    "research/rh/integration/",
    "research/rh/pattern_phase2/",
    "research/rh/producer_census_v2/",
)
ACTIVE_EXACT = {
    "research/rh/AEGIS_DIRICHLET_QUASI_BRIDGE_V1.json",
    "research/rh/AEGIS_DIRICHLET_QUASI_BRIDGE_V1.md",
}
EXTENSIONS = {".json", ".py", ".yml", ".yaml", ".sh"}
# Count ONLY unconditional-RH admission fields; not real test assertions,
# historical research findings, or meaningful runtime negative test results.
KEY = (
    r"(?:rh_proven_unconditionally|rh_unconditionally_proven|"
    r"unconditional_rh_proven|rh_unconditional_claim|"
    r"unconditional_rh_claim|rh_proven|rh_unconditional)"
)
NEGATIVE_DEFAULT = re.compile(
    r"(?i)(?<![A-Za-z_])['\"]?" + KEY
    + r"['\"]?\s*[:=]\s*['\"]?(?:false|not_claimed|not_proven)\b"
)


KEY_NAME = re.compile(r"(?i)^" + KEY + r"$")


def negative_defaults_in_content(path: str, source: str) -> list[tuple[int, str]]:
    """Report negative machine-readable defaults, never commentary or prose."""
    found: list[tuple[int, str]] = []
    suffix = Path(path).suffix

    def negative(value: object) -> bool:
        return value is False or (
            isinstance(value, str) and value.lower() in {"not_proven", "not_claimed"}
        )

    if suffix == ".json":
        def visit(value: object, location: str = "$") -> None:
            if isinstance(value, dict):
                for key, child in value.items():
                    location_key = f"{location}.{key}"
                    if KEY_NAME.fullmatch(str(key)) and negative(child):
                        found.append((0, location_key))
                    visit(child, location_key)
            elif isinstance(value, list):
                for pos, child in enumerate(value):
                    visit(child, f"{location}[{pos}]")
        visit(json.loads(source))
        return found

    if suffix == ".py":
        def negative_expr(node: ast.AST) -> bool:
            return isinstance(node, ast.Constant) and negative(node.value)

        def expr_name(node: ast.AST) -> str | None:
            if isinstance(node, ast.Name):
                return node.id
            if isinstance(node, ast.Attribute):
                return node.attr
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                return node.value
            if isinstance(node, ast.Subscript):
                return expr_name(node.slice)
            return None

        for node in ast.walk(ast.parse(source, filename=path)):
            if isinstance(node, ast.Assign) and negative_expr(node.value):
                for target in node.targets:
                    if (name := expr_name(target)) and KEY_NAME.fullmatch(name):
                        found.append((node.lineno, name))
            elif isinstance(node, ast.AnnAssign) and node.value is not None \
                    and negative_expr(node.value):
                if (name := expr_name(node.target)) and KEY_NAME.fullmatch(name):
                    found.append((node.lineno, name))
            elif isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values):
                    if key is not None and negative_expr(value):
                        if (name := expr_name(key)) and KEY_NAME.fullmatch(name):
                            found.append((node.lineno, name))
            elif isinstance(node, ast.keyword) and negative_expr(node.value):
                if node.arg and KEY_NAME.fullmatch(node.arg):
                    found.append((node.value.lineno, node.arg))
        return found

    # YAML and shell: ignore comments outside quoted values.
    for number, line in enumerate(source.splitlines(), 1):
        quote, escaped, end = None, False, len(line)
        for pos, char in enumerate(line):
            if escaped:
                escaped = False
            elif char == "\\" and quote == '"':
                escaped = True
            elif char in ("'", '"'):
                if quote is None:
                    quote = char
                elif quote == char:
                    quote = None
            elif char == "#" and quote is None and (
                pos == 0 or line[pos - 1].isspace()
            ):
                end = pos
                break
        if NEGATIVE_DEFAULT.search(line[:end]):
            found.append((number, line[:end].strip()[:180]))
    return found


def main() -> int:
    names = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT)
    active = [
        name.decode("utf-8")
        for name in names.split(b"\0")
        if name and (
            name.decode("utf-8").startswith(ACTIVE_PREFIXES)
            or name.decode("utf-8") in ACTIVE_EXACT
        )
        and Path(name.decode("utf-8")).suffix in EXTENSIONS
    ]
    offenders: list[str] = []
    for path in active:
        source = (ROOT / path).read_text(encoding="utf-8")
        for number, finding in negative_defaults_in_content(path, source):
            offenders.append(f"{path}:{number}: {finding}")
    if offenders:
        print("RH_STATIC_VERDICT_AUDIT=FAIL")
        print("\n".join(offenders))
        return 1
    print(f"RH_STATIC_VERDICT_AUDIT=PASS scanned={len(active)} static_negative_defaults=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
