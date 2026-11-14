# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed unit tests for the existing RH source-bound checkpoint reader."""
from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/rh_restore_source_bound_oleans.py"
SPEC = importlib.util.spec_from_file_location("rh_restore_source_bound_oleans", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class SourceBoundCofinalCheckpointTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.cache = Path(temp.name)
        (self.cache / "oleans").mkdir()
        self.module = "AEGIS.Proof"
        self.rel = "oleans/AEGIS.Proof.olean"
        self.olean = self.cache / self.rel
        self.olean.write_bytes(b"kernel-compiled fixture for cache checksum test")
        self.blob = "a" * 40
        self.write_sources(self.module, self.blob)
        self.write_binaries(self.rel, self.olean)

    def write_sources(self, module, digest):
        (self.cache / "source-blobs.txt").write_text(
            module + " " + digest + "\n")

    def write_binaries(self, rel, binary):
        checksum = hashlib.sha256(binary.read_bytes()).hexdigest()
        (self.cache / "oleans.sha256").write_text(checksum + "  " + rel + "\n")

    def test_accepts_matching_source_and_binary_module_names(self):
        self.assertEqual(checker.verified_cache(self.cache),
                         {self.module: self.blob})

    def test_missing_cache_returns_no_restorable_modules(self):
        self.assertEqual(checker.verified_cache(self.cache / "absent"), {})

    def test_rejects_source_blob_for_other_module_with_same_binary_bytes(self):
        self.write_sources("AEGIS.OtherProof", self.blob)
        with self.assertRaisesRegex(RuntimeError, "SOURCE_OLEAN_SET_MISMATCH"):
            checker.verified_cache(self.cache)

    def test_rejects_extra_source_without_binary(self):
        with (self.cache / "source-blobs.txt").open("a") as out:
            out.write("AEGIS.Missing " + "b" * 40 + "\n")
        with self.assertRaisesRegex(RuntimeError, "SOURCE_OLEAN_SET_MISMATCH"):
            checker.verified_cache(self.cache)

    def test_rejects_corrupted_olean(self):
        self.olean.write_bytes(b"tampered")
        with self.assertRaisesRegex(RuntimeError, "HASH_MISMATCH"):
            checker.verified_cache(self.cache)

    def test_rejects_removed_olean(self):
        self.olean.unlink()
        with self.assertRaisesRegex(RuntimeError, "HASH_MISMATCH"):
            checker.verified_cache(self.cache)

    def test_rejects_duplicate_module_metadata(self):
        with (self.cache / "source-blobs.txt").open("a") as out:
            out.write(self.module + " " + self.blob + "\n")
        with self.assertRaisesRegex(RuntimeError, "DUPLICATE_MODULE"):
            checker.verified_cache(self.cache)

    def test_rejects_invalid_source_blob(self):
        self.write_sources(self.module, "not-a-git-blob")
        with self.assertRaisesRegex(RuntimeError, "BAD_SOURCE_BLOB"):
            checker.verified_cache(self.cache)

    def test_rejects_missing_sha_manifest(self):
        (self.cache / "oleans.sha256").unlink()
        with self.assertRaisesRegex(RuntimeError, "INCOMPLETE"):
            checker.verified_cache(self.cache)

    def test_rejects_undeclared_binary(self):
        extra = self.cache / "oleans/AEGIS.Extra.olean"
        extra.write_bytes(b"not in SHA manifest")
        with self.assertRaisesRegex(RuntimeError, "FILE_SET_MISMATCH"):
            checker.verified_cache(self.cache)


if __name__ == "__main__":
    unittest.main()
