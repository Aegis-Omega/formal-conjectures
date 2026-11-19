# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the exact-head RH submission checkpoint gate."""
import subprocess
import tempfile
import unittest
from pathlib import Path

from rh_submission_from_checkpoint import (
    ALLOWED_AXIOMS, audited_axioms, closed_candidates, make_probe,
    sha256, tracked_source,
)


class SubmissionCheckpointTests(unittest.TestCase):
    def test_closed_only_for_exact_kernel_type(self):
        base = {
            "identifier": "AEGIS.RealProof", "module": "AEGISOverlay.Valid",
            "type_defeq_riemann_hypothesis": True, "has_body": True,
            "is_axiom": False, "axioms": sorted(ALLOWED_AXIOMS),
        }
        rows = [
            base,
            dict(base, identifier="AEGIS.Conditional", type_defeq_riemann_hypothesis=False),
            dict(base, identifier="AEGIS.Sorry", axioms=["sorryAx"]),
            dict(base, identifier="AEGIS.Assumed", is_axiom=True),
            dict(base, identifier="AEGIS.BadAxiom", axioms=["AEGIS.newAxiom"]),
            dict(base, identifier="RiemannHypothesis.riemannHypothesis", axioms=["sorryAx"]),
            dict(base, identifier="AEGIS.NoBody", has_body=False),
        ]
        self.assertEqual([r["identifier"] for r in closed_candidates(rows)],
                         ["AEGIS.RealProof"])

    def test_verified_canonical_theorem_is_not_blacklisted_by_its_name(self):
        canonical = {
            "identifier": "RiemannHypothesis.riemannHypothesis",
            "module": "FormalConjectures.Millennium.RiemannHypothesis",
            "type_defeq_riemann_hypothesis": True,
            "has_body": True,
            "is_axiom": False,
            "axioms": ["Classical.choice", "propext", "Quot.sound"],
        }
        self.assertEqual(closed_candidates([canonical]), [canonical])
        self.assertEqual(
            closed_candidates([dict(canonical, axioms=["sorryAx"])]), [])

    def test_empty_candidates_are_not_negative_global_verdict(self):
        self.assertEqual(closed_candidates([]), [])

    def test_probe_requires_direct_exact_mathlib_target(self):
        s = make_probe("AEGISOverlay.Valid", "AEGIS.RealProof")
        self.assertIn("example : _root_.RiemannHypothesis := AEGIS.RealProof", s)
        self.assertIn("#print axioms AEGIS.RealProof", s)
        with self.assertRaises(ValueError):
            make_probe("AEGISOverlay.Valid\naxiom False", "AEGIS.RealProof")

    def test_tracked_source_requires_exact_head_blob(self):
        # A changed source whose manifest was also updated is NOT an
        # exact-head source, even though HEAD still contains that path.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)

            def git(*args):
                subprocess.run(["git", *args], cwd=root, check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

            git("init", "-q")
            git("config", "user.name", "Local RH Gate Test")
            git("config", "user.email", "local-rh-gate@example.invalid")
            source = root / "Producer.lean"
            source.write_text("theorem Producer : True := by trivial\n")
            git("add", "Producer.lean")
            git("commit", "-qm", "record original source")
            record = {"source": "Producer.lean", "sha256": sha256(source)}
            self.assertEqual(tracked_source(root, record, "AEGIS.Producer"),
                             ("Producer.lean", 1))

            source.write_text("theorem Producer : True := by exact True.intro\n")
            record["sha256"] = sha256(source)
            self.assertIsNone(tracked_source(root, record, "AEGIS.Producer"))

            git("add", "Producer.lean")
            git("commit", "-qm", "record updated source")
            self.assertEqual(tracked_source(root, record, "AEGIS.Producer"),
                             ("Producer.lean", 1))

    def test_only_named_declarations_axioms_count(self):
        logs = (
            "'AEGIS.RealProof' depends on axioms: [propext, Classical.choice]\n"
            "'RiemannHypothesis.riemannHypothesis' depends on axioms: [sorryAx]\n")
        self.assertEqual(audited_axioms(logs, "AEGIS.RealProof"),
                         {"propext", "Classical.choice"})
        self.assertIsNone(audited_axioms(logs, "AEGIS.SomeOther"))
        self.assertEqual(audited_axioms(
            "'AEGIS.RealProof' does not depend on any axioms", "AEGIS.RealProof"), set())


if __name__ == "__main__":
    unittest.main()
