# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Tests for RH frontier snapshot extraction."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent))
from rh_frontier_snapshot import EQUIVALENTS, OFFICIAL, main, snapshot


OFFICIAL_SOURCE = """import FormalConjecturesUtil
namespace RiemannHypothesis
theorem riemannHypothesis : RiemannHypothesis := by
  sorry
end RiemannHypothesis
namespace GRH
theorem generalized_riemann_hypothesis : False := by
  admit
end GRH
"""

EQUIVALENTS_SOURCE = """import FormalConjectures.Millennium.RiemannHypothesis
namespace RiemannHypothesis
theorem robin_criterion : True := by
  trivial
end RiemannHypothesis
"""


class RHFrontierSnapshotTests(unittest.TestCase):
    def test_snapshot_extracts_theorems_imports_and_placeholders(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            official = root / OFFICIAL
            equivalents = root / EQUIVALENTS
            official.parent.mkdir(parents=True, exist_ok=True)
            equivalents.parent.mkdir(parents=True, exist_ok=True)
            official.write_text(OFFICIAL_SOURCE, encoding="utf-8")
            equivalents.write_text(EQUIVALENTS_SOURCE, encoding="utf-8")

            data = snapshot(root, [OFFICIAL, EQUIVALENTS])
            self.assertEqual(data["summary"]["files_scanned"], 2)
            self.assertEqual(data["summary"]["theorem_count"], 3)
            self.assertEqual(data["summary"]["placeholder_count"], 2)
            self.assertFalse(data["summary"]["rh_closed_unconditionally"])

            off = data["files"][OFFICIAL.as_posix()]
            self.assertEqual(
                [t["name"] for t in off["theorems"]],
                [
                    "RiemannHypothesis.riemannHypothesis",
                    "GRH.generalized_riemann_hypothesis",
                ],
            )
            self.assertEqual([p["token"] for p in off["placeholders"]], ["sorry", "admit"])

            eqv = data["files"][EQUIVALENTS.as_posix()]
            self.assertEqual(eqv["local_imports"], ["FormalConjectures.Millennium.RiemannHypothesis"])

    def test_main_fails_closed_when_file_missing(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            rc = main(["--root", str(root)])
            self.assertEqual(rc, 1)

    def test_main_writes_output_json(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            official = root / OFFICIAL
            equivalents = root / EQUIVALENTS
            official.parent.mkdir(parents=True, exist_ok=True)
            equivalents.parent.mkdir(parents=True, exist_ok=True)
            official.write_text(OFFICIAL_SOURCE, encoding="utf-8")
            equivalents.write_text(EQUIVALENTS_SOURCE, encoding="utf-8")

            out = root / "out" / "snapshot.json"
            rc = main(["--root", str(root), "--output", str(out)])
            self.assertEqual(rc, 0)
            payload = json.loads(out.read_text(encoding="utf-8"))
            self.assertEqual(payload["schema"], "aegis.rh.frontier.snapshot.v1")


if __name__ == "__main__":
    unittest.main()
