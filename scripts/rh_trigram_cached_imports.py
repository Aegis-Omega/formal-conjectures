#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Reuse only a complete source-identical import closure from a pinned cache."""
from pathlib import Path

from scripts.rh_restore_source_bound_oleans import imports, source_blob, verified_cache


def reusable_imports(entries: list[dict], cache: Path) -> set[str]:
    old = verified_cache(cache)
    names = {entry["name"] for entry in entries}
    if len(names) != len(entries):
        raise RuntimeError("TRIGRAM_DUPLICATE_SOURCE_MODULE")
    trusted: dict[str, bool] = {}
    for entry in entries:
        name = entry["name"]
        source = Path(entry["source"])
        if source_blob(source) != entry["blob"]:
            raise RuntimeError("TRIGRAM_CURRENT_SOURCE_DRIFT " + name)
        deps = imports(source) & names
        if not deps <= trusted.keys():
            raise RuntimeError("TRIGRAM_NONTOPOLOGICAL_CACHE_SOURCE " + name)
        trusted[name] = (
            old.get(name) == entry["blob"]
            and all(trusted[dep] for dep in deps)
            and (cache / "oleans" / (name + ".olean")).is_file()
        )
    # The final six axiom reports must always come from a fresh compilation.
    return {name for name, valid in trusted.items()
            if valid and name != "RHKreinTrigramAdaptiveV1"}
