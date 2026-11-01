# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Tests for RH frontier snapshot extraction."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest
from urllib.parse import quote

sys.path.insert(0, str(Path(__file__).parent))
from rh_frontier_snapshot import (
    EQUIVALENTS,
    OFFICIAL,
    fetch_external_repo_signal,
    main,
    snapshot,
)


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

    def test_empty_files_never_claim_unconditional_rh(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for rel in (OFFICIAL, EQUIVALENTS):
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("import External.Unverified\n", encoding="utf-8")
            data = snapshot(root, [OFFICIAL, EQUIVALENTS])
            self.assertEqual(data["summary"]["theorem_count"], 0)
            self.assertFalse(data["summary"]["rh_closed_unconditionally"])

    def test_axiom_dependent_theorem_never_claims_unconditional_rh(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for rel in (OFFICIAL, EQUIVALENTS):
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    "import External.Unverified\n"
                    "theorem riemannHypothesis : False := by\n"
                    "  exact hiddenAxiom\n", encoding="utf-8"
                )
            data = snapshot(root, [OFFICIAL, EQUIVALENTS])
            self.assertEqual(data["summary"]["placeholder_count"], 0)
            self.assertFalse(data["summary"]["rh_closed_unconditionally"])

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

    def test_external_repo_signal_deduplicates_hits(self):
        owner, repo = "Aegis-Omega", "AEGIS-OMEGA"
        q1 = "https://api.github.com/search/code?q=" + quote(
            f"repo:{owner}/{repo} RiemannHypothesis in:file extension:lean", safe=""
        )
        q2 = "https://api.github.com/search/code?q=" + quote(
            f"repo:{owner}/{repo} riemann in:file extension:lean", safe=""
        )
        payloads = {
            q1: {
                "total_count": 2,
                "items": [
                    {"name": "A.lean", "path": "src/A.lean", "sha": "sha1", "html_url": "u1"},
                    {"name": "B.lean", "path": "src/B.lean", "sha": "sha2", "html_url": "u2"},
                ],
            },
            q2: {
                "total_count": 2,
                "items": [
                    {"name": "A.lean", "path": "src/A.lean", "sha": "sha1", "html_url": "u1"},
                    {"name": "C.lean", "path": "src/C.lean", "sha": "sha3", "html_url": "u3"},
                ],
            },
        }

        def fake_fetch(url: str):
            return payloads[url]

        data = fetch_external_repo_signal(owner, repo, max_items=10, fetch_json=fake_fetch)
        self.assertEqual(data["repo"], "Aegis-Omega/AEGIS-OMEGA")
        self.assertEqual(data["query_total_count"], 4)
        self.assertEqual(data["returned_hit_count"], 3)
        self.assertEqual([h["path"] for h in data["hits"]], ["src/A.lean", "src/B.lean", "src/C.lean"])


if __name__ == "__main__":
    unittest.main()
