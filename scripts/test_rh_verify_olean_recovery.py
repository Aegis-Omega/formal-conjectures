# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Tampering regressions for the actual recovered CI .olean archive verifier."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts/rh_verify_olean_recovery.py"
SPEC = importlib.util.spec_from_file_location("rh_verify_olean_recovery", SOURCE)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class RecoveryArchiveTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.path = Path(tmp.name) / "fixture.zip"
        self.module = "AEGIS.UnitProof"
        self.file = "oleans/AEGIS/UnitProof.olean"
        self.data = b"binary integrity fixture, NOT a Lean object"
        self.digest = hashlib.sha256(self.data).hexdigest()
        self.metadata = {
            "schema": checker.SCHEMA,
            "original_manifest_git_blob": checker.SOURCE_MANIFEST_BLOB,
            "expected_source_module_count": checker.EXPECTED_COUNT,
            "recovered_binary_count": 1,
            "binaries": [{
                "module": self.module,
                "file": self.file,
                "sha256": self.digest,
                "size_bytes": len(self.data),
            }],
            "missing_binary_modules": [
                "AEGIS.Other%03d" % i for i in range(checker.EXPECTED_COUNT - 1)
            ],
        }

    def write_bundle(self, rogue=None):
        with zipfile.ZipFile(self.path, "w", zipfile.ZIP_DEFLATED) as z:
            z.writestr("checkpoint_provenance.json", json.dumps(self.metadata))
            z.writestr("recovered_oleans.sha256", self.digest + "  " + self.file + "\n")
            z.writestr(self.file, self.data)
            z.writestr("README.txt", "test fixture")
            if rogue is not None:
                z.writestr(rogue, b"unlisted content")
        return self.path

    def test_integrity_valid_but_incomplete(self):
        result = checker.verify_bundle(self.write_bundle())
        self.assertEqual(result["verified_binary_objects"], 1)
        self.assertFalse(result["complete"])

    def test_complete_gate_rejects_missing_316_objects(self):
        with self.assertRaisesRegex(ValueError, "INCOMPLETE_OLEAN_CHECKPOINT"):
            checker.verify_bundle(self.write_bundle(), require_complete=True)

    def test_rejects_false_complete_claim(self):
        self.metadata["missing_binary_modules"] = []
        with self.assertRaisesRegex(ValueError, "UNACCOUNTED_SOURCE_MODULES"):
            checker.verify_bundle(self.write_bundle())

    def test_rejects_unmatched_binary_checksum(self):
        self.metadata["binaries"][0]["sha256"] = "a" * 64
        with self.assertRaisesRegex(ValueError, "BINARY_CONTENT_MISMATCH|BINARY_CHECKSUM"):
            checker.verify_bundle(self.write_bundle())

    def test_rejects_unlisted_binary(self):
        with self.assertRaisesRegex(ValueError, "OLEAN_CHECKSUM_FILE_SET_MISMATCH"):
            checker.verify_bundle(self.write_bundle(rogue="oleans/AEGIS/Evil.olean"))

    def test_rejects_zip_path_traversal(self):
        with self.assertRaisesRegex(ValueError, "UNSAFE_ZIP_MEMBER"):
            checker.verify_bundle(self.write_bundle(rogue="../outside.txt"))

    def test_rejects_different_source_manifest_blob(self):
        self.metadata["original_manifest_git_blob"] = "b" * 40
        with self.assertRaisesRegex(ValueError, "SOURCE_MANIFEST_IDENTITY_MISMATCH"):
            checker.verify_bundle(self.write_bundle())


if __name__ == "__main__":
    unittest.main()
