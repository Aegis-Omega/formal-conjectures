#!/usr/bin/env python3
"""Fail-closed historical source identity gate for ACTUAL_INPUT_SOURCES.zip.

Only the three independently reviewed Apache-header normalizations are permitted.
The pinned archive and its SHA-256s remain immutable. This validates *source*
identity and does not replace a Lean type/axiom/kernel replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

EXPECTED_ARCHIVE_SHA256 = "8afe689463234e09eaa1511ce1decaa915f69070e959fb947e35a29592cb9b30"
EXPECTED_EXISTING = {
    "CvSTriangularTransportV1.lean": (
        "9e31d82b6f5d945c6077e898b59bee0302c2e2741c0ec8916d49f3efc442b3a7",
        "3b3a03cd97f996d39ebdf4f7c2a8ca300a92c0c6463fe837902595cb03798503",
    ),
    "CvSRealBasisBoundV1.lean": (
        "7e5aba10dbe4cd114f41e5cd7049d493ffc221c0d4fcc87656770d01e3f27b77",
        "487e7fc9e16dabe35b7a03f1ddd5e907fa03439795622fbf483a9d0212125dab",
    ),
    "CvSProjectedBasisL12V1.lean": (
        "57915883361cad0502d9a451e4af1afe6c1db32707ec9b1623fbcc6c09bfc2ba",
        "4aa7c4e43494a2697cfad857a88ec191693ff2dc06b3cc918e001f6a88e318c8",
    ),
}
ORIGINAL_DIR = "research/rh/feshbach_lean_v1/"
WORK_DIR = "research/rh/checkpoints/20261020_row_budget_bridge/actual_input_execution/"

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def split_license(data: bytes) -> bytes:
    """Strictly parse leading Apache license, preserving every following source byte."""
    if not data.startswith(b"/-\nCopyright 2026 The Formal Conjectures Authors.\n"):
        raise ValueError("UNEXPECTED_LICENSE_START")
    closing = data.find(b"\n-/")
    if closing < 0:
        raise ValueError("UNTERMINATED_LICENSE")
    header = data[:closing + 3]
    mandatory = (
        b'Licensed under the Apache License, Version 2.0 (the "License");',
        b"https://www.apache.org/licenses/LICENSE-2.0",
        b"You may not use this file except in compliance with the License.",
    )
    if any(part not in header for part in mandatory):
        raise ValueError("UNRECOGNIZED_APACHE_HEADER")
    if b"WITHOUT WARRANTIES" in header:
        if b"WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied." not in header:
            raise ValueError("INVALID_EXPANDED_APACHE_HEADER")
    elif b"You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0" not in header:
        raise ValueError("INVALID_COMPACT_APACHE_HEADER")
    tail = data[closing + 3:]
    # Exactly one or two newlines after the header, never arbitrary whitespace.
    if not tail.startswith(b"\n") or tail.startswith(b"\n\n\n"):
        raise ValueError("UNEXPECTED_POST_LICENSE_SEPARATOR")
    if tail.startswith(b"\n\n"):
        tail = tail[2:]
    else:
        tail = tail[1:]
    if not tail.strip():
        raise ValueError("EMPTY_PROOF_SOURCE")
    return tail

def validate(name: str, origin: dict, archived: bytes, checkout: bytes):
    historical_hash = origin.get("sha256")
    archived_hash = digest(archived)
    checkout_hash = digest(checkout)
    if archived_hash != historical_hash:
        raise ValueError("ARCHIVED_SOURCE_MISMATCH:" + name)
    if checkout_hash == historical_hash and checkout == archived:
        return {
            "name": name, "original_path": origin["original_path"],
            "pinned_sha256": historical_hash, "checkout_sha256": checkout_hash,
            "classification": "EXACT_SOURCE_IDENTITY"
        }
    # This fixed allowlist requires the exact historical and normalized bytes.
    allowed = EXPECTED_EXISTING.get(name)
    if allowed is None or allowed != (historical_hash, checkout_hash):
        raise ValueError("UNAUTHORIZED_SOURCE_CHANGE:" + name)
    if origin["original_path"] != ORIGINAL_DIR + name:
        raise ValueError("UNEXPECTED_ORIGIN_PATH:" + name)
    if split_license(archived) != split_license(checkout):
        raise ValueError("MATHEMATICAL_SOURCE_DIFF:" + name)
    return {
        "name": name, "original_path": origin["original_path"],
        "pinned_sha256": historical_hash, "checkout_sha256": checkout_hash,
        "classification": "PINNED_APACHE_HEADER_ONLY",
        "source_remainder_byte_identical": True
    }

def preflight(repo: Path):
    d = repo / WORK_DIR
    manifest = json.loads((d / "ACTUAL_INPUT_SOURCE_MANIFEST.json").read_text())
    arc = d / "ACTUAL_INPUT_SOURCES.zip"
    if manifest.get("archive_sha256") != EXPECTED_ARCHIVE_SHA256:
        raise ValueError("ARCHIVE_MANIFEST_PIN_CHANGED")
    if digest(arc.read_bytes()) != EXPECTED_ARCHIVE_SHA256:
        raise ValueError("ARCHIVE_BYTES_CHANGED")
    copies = manifest["unchanged_existing_source_copies"]
    if set(copies) != set(EXPECTED_EXISTING) | {"CvSTauFarL12V1.lean"}:
        raise ValueError("EXISTING_SOURCE_SET_CHANGED")
    with zipfile.ZipFile(arc) as z:
        names = z.namelist()
        if len(names) != len(set(names)):
            raise ValueError("DUPLICATE_ARCHIVE_ENTRY")
        indexed_sources = {item["name"]: item["sha256"] for item in manifest["sources"]}
        for name, expected in indexed_sources.items():
            if digest(z.read(name)) != expected:
                raise ValueError("ARCHIVED_MEMBER_MISMATCH:" + name)
        validated = []
        for name, origin in sorted(copies.items()):
            if name not in indexed_sources or indexed_sources[name] != origin["sha256"]:
                raise ValueError("ORIGIN_NOT_BOUND_IN_MANIFEST:" + name)
            if not str(origin["original_path"]).startswith(ORIGINAL_DIR):
                raise ValueError("ORIGIN_OUTSIDE_EXPECTED_DIRECTORY:" + name)
            checked = (repo / origin["original_path"]).read_bytes()
            validated.append(validate(name, origin, z.read(name), checked))
    return {
        "schema": "aegis.rh.actual-input-license-source-identity.v1",
        "archive_sha256": EXPECTED_ARCHIVE_SHA256,
        "original_source_count": len(indexed_sources),
        "checked_original_copies": validated,
        "license_only": sum(x["classification"] == "PINNED_APACHE_HEADER_ONLY" for x in validated),
        "exact": sum(x["classification"] == "EXACT_SOURCE_IDENTITY" for x in validated),
        "source_binding_pass": True,
        "lean_kernel_proof_claim": False,
    }

def self_test():
    compact = (b'/-\nCopyright 2026 The Formal Conjectures Authors.\n'
               b'Licensed under the Apache License, Version 2.0 (the "License");\n'
               b'You may not use this file except in compliance with the License.\n'
               b'You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0\n-/\n'
               b'import MathematicalSource\n')
    normalized = (b'/-\nCopyright 2026 The Formal Conjectures Authors.\n\n'
                  b'Licensed under the Apache License, Version 2.0 (the "License");\n'
                  b'You may not use this file except in compliance with the License.\n'
                  b'You may obtain a copy of the License at\n\n'
                  b'    https://www.apache.org/licenses/LICENSE-2.0\n\n'
                  b'Unless required by applicable law or agreed to in writing, software\n'
                  b'distributed under the License is distributed on an "AS IS" BASIS,\n'
                  b'WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n'
                  b'See the License for the specific language governing permissions and\n'
                  b'limitations under the License.\n-/\n\n'
                  b'import MathematicalSource\n')
    name = "CvSTriangularTransportV1.lean"
    origin = {"sha256": digest(compact), "original_path": ORIGINAL_DIR + name}
    assert split_license(compact) == split_license(normalized)
    old = EXPECTED_EXISTING[name]
    try:
        EXPECTED_EXISTING[name] = (digest(compact), digest(normalized))
        item = validate(name, origin, compact, normalized)
        assert item["classification"] == "PINNED_APACHE_HEADER_ONLY"
        failures = [
            (compact, normalized + b"\ntheorem compromised : True := by trivial", "MATHEMATICAL_SOURCE_DIFF"),
            (compact, normalized.replace(b"import MathematicalSource", b"import Other"), "UNAUTHORIZED_SOURCE_CHANGE"),
            (compact + b"x", normalized, "ARCHIVED_SOURCE_MISMATCH"),
        ]
        for source, candidate, message in failures:
            try:
                validate(name, origin, source, candidate)
            except ValueError as err:
                assert message in str(err), (message, str(err))
            else:
                raise AssertionError("FAIL_OPEN:" + message)
    finally:
        EXPECTED_EXISTING[name] = old
    print("LICENSE_GATE_SELF_TEST_PASS")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--preflight", action="store_true")
    parser.add_argument("--receipt", default=None)
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.preflight:
        parser.error("Pass --self-test or --preflight")
    repo = Path(__file__).resolve().parents[5]
    result = preflight(repo)
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
if __name__ == "__main__":
    main()
