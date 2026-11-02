#!/usr/bin/env python3
"""Verify transferred bytes only. This is not a mathematical proof checker."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
manifest = json.loads((root / "MANIFEST.json").read_text())
for entry in manifest["files"]:
    relative = Path(entry["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("unsafe manifest path")
    data = (root / relative).read_bytes()
    if len(data) != entry["bytes"]:
        raise ValueError("size mismatch: " + str(relative))
    if hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError("hash mismatch: " + str(relative))
print(json.dumps({"byte_manifest": "PASS", "files": len(manifest["files"]),
                  "analytic_proof_checked": False, "rh_proven": False}))
