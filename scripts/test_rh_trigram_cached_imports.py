# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for transitive checkpoint reuse across proof stages."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.rh_restore_source_bound_oleans import source_blob
from scripts.rh_trigram_cached_imports import reusable_imports


class TrigramCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.cache = self.root / "cache"
        (self.cache / "oleans").mkdir(parents=True)
        self.entries = []
        blobs, hashes = [], []
        for name, text in [("A", "import Mathlib\n"), ("B", "import A\n"),
                           ("RHKreinTrigramAdaptiveV1", "import B\n")]:
            src = self.root / (name + ".lean")
            src.write_text(text)
            blob = source_blob(src)
            self.entries.append({"name": name, "source": str(src), "blob": blob})
            rel = "oleans/" + name + ".olean"
            data = ("fixture: " + name).encode()
            (self.cache / rel).write_bytes(data)
            blobs.append(name + " " + blob + "\n")
            hashes.append(hashlib.sha256(data).hexdigest() + "  " + rel + "\n")
        (self.cache / "source-blobs.txt").write_text("".join(blobs))
        (self.cache / "oleans.sha256").write_text("".join(hashes))

    def change_source(self, index):
        entry = self.entries[index]
        src = Path(entry["source"])
        src.write_text(src.read_text() + "-- changed\n")
        entry["blob"] = source_blob(src)

    def test_verified_imports_reused_but_final_target_recompiled(self):
        self.assertEqual(reusable_imports(self.entries, self.cache), {"A", "B"})

    def test_only_final_source_changed_keeps_entire_import_prefix(self):
        self.change_source(2)
        self.assertEqual(reusable_imports(self.entries, self.cache), {"A", "B"})

    def test_changed_parent_invalidates_unchanged_descendants(self):
        self.change_source(0)
        self.assertEqual(reusable_imports(self.entries, self.cache), set())

    def test_changed_leaf_preserves_earlier_import(self):
        self.change_source(1)
        self.assertEqual(reusable_imports(self.entries, self.cache), {"A"})

    def test_corrupt_olean_rejected(self):
        (self.cache / "oleans/A.olean").write_bytes(b"corrupt")
        with self.assertRaisesRegex(RuntimeError, "HASH_MISMATCH"):
            reusable_imports(self.entries, self.cache)

    def test_current_source_drift_rejected(self):
        Path(self.entries[0]["source"]).write_text("changed without updating manifest")
        with self.assertRaisesRegex(RuntimeError, "CURRENT_SOURCE_DRIFT"):
            reusable_imports(self.entries, self.cache)

    def test_incomplete_cache_rejected(self):
        (self.cache / "oleans.sha256").unlink()
        with self.assertRaisesRegex(RuntimeError, "CHECKPOINT_INCOMPLETE"):
            reusable_imports(self.entries, self.cache)

    def test_wrong_order_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "NONTOPOLOGICAL"):
            reusable_imports(list(reversed(self.entries)), self.cache)

    def test_missing_cache_recompiles(self):
        self.assertEqual(reusable_imports(self.entries, self.root / "absent"), set())


if __name__ == "__main__":
    unittest.main()
