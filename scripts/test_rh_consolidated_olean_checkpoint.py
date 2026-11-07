# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Executable integrity regressions for actual source-bound Lean object reuse."""
from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "research/rh/consolidated_v1/build.py"
SPEC = importlib.util.spec_from_file_location("rh_consolidated_checkpoint_build", BUILD)
assert SPEC is not None and SPEC.loader is not None
module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)


class SourceBoundOleanCheckpointTests(unittest.TestCase):
    """Exercise the same byte-check used by resumed and cross-stage builds."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name)
        self.name = "AEGIS.UnitProof"
        self.olean = self.out / "AEGIS/UnitProof.olean"
        self.olean.parent.mkdir(parents=True)
        self.olean.write_bytes(b"verified Lean binary fixture")
        self.source_sha = hashlib.sha256(b"theorem unitProof : True := by trivial").hexdigest()
        self.context_sha = hashlib.sha256(b"Lean and Mathlib pins").hexdigest()
        Path(str(self.olean) + ".sha256").write_text(
            hashlib.sha256(self.olean.read_bytes()).hexdigest() + "\n")
        Path(str(self.olean) + ".source.sha256").write_text(self.source_sha + "\n")
        Path(str(self.olean) + ".context.sha256").write_text(self.context_sha + "\n")

    def trusted(self, source=None, context=None):
        return module.verified_olean(
            self.out, self.name,
            self.source_sha if source is None else source,
            self.context_sha if context is None else context)

    def test_accepts_byte_source_and_context_matched_checkpoint(self):
        self.assertTrue(self.trusted())

    def test_rejects_mutated_binary_even_if_source_unchanged(self):
        self.olean.write_bytes(b"mutated binary")
        self.assertFalse(self.trusted())

    def test_rejects_changed_source_even_if_binary_checksum_matches(self):
        self.assertFalse(self.trusted(source=hashlib.sha256(b"new source").hexdigest()))

    def test_rejects_changed_lean_mathlib_context(self):
        self.assertFalse(self.trusted(context=hashlib.sha256(b"new Mathlib").hexdigest()))

    def test_rejects_absent_source_checkpoint(self):
        Path(str(self.olean) + ".source.sha256").unlink()
        self.assertFalse(self.trusted())

    def test_rejects_absent_context_checkpoint(self):
        Path(str(self.olean) + ".context.sha256").unlink()
        self.assertFalse(self.trusted())

    def test_rejects_absent_binary(self):
        self.olean.unlink()
        self.assertFalse(self.trusted())

    def test_rejects_zero_byte_binary(self):
        self.olean.write_bytes(b"")
        Path(str(self.olean) + ".sha256").write_text(
            hashlib.sha256(b"").hexdigest() + "\n")
        self.assertFalse(self.trusted())

    def test_resume_rejects_transitive_dependents_of_stale_module(self):
        graph = {"ProofA": [], "ProofB": ["ProofA"], "ProofC": ["ProofB"]}
        present = {"ProofA": False, "ProofB": True, "ProofC": True}
        self.assertEqual(
            module.resumable_modules(graph, graph, lambda m: present[m]), set())

    def test_resume_accepts_complete_dependency_closure(self):
        graph = {"ProofA": [], "ProofB": ["ProofA"], "ProofC": ["ProofB"]}
        present = {"ProofA": True, "ProofB": True, "ProofC": True}
        self.assertEqual(
            module.resumable_modules(graph, graph, lambda m: present[m]),
            set(graph))

    def test_resume_hashes_each_cached_olean_once(self):
        graph = {"ProofA": [], "ProofB": ["ProofA"], "ProofC": ["ProofB"]}
        calls = {m: 0 for m in graph}
        def checked(m):
            calls[m] += 1
            return True
        self.assertEqual(module.resumable_modules(graph, graph, checked), set(graph))
        self.assertEqual(calls, {m: 1 for m in graph})

    def test_cross_stage_rejects_stale_indirect_import(self):
        graph = {"ProofA": [], "ProofB": ["ProofA"], "ProofC": ["ProofB"]}
        present = {"ProofA": False, "ProofB": True, "ProofC": False}
        self.assertEqual(
            module.missing_upstream_oleans(
                graph, graph, {"ProofC"}, lambda m: present[m]),
            ["ProofB"])

    def test_cross_stage_accepts_exact_upstream_import_closure(self):
        graph = {"ProofA": [], "ProofB": ["ProofA"], "ProofC": ["ProofB"]}
        present = {"ProofA": True, "ProofB": True, "ProofC": False}
        self.assertEqual(
            module.missing_upstream_oleans(
                graph, graph, {"ProofC"}, lambda m: present[m]),
            [])

    def test_accepts_clean_lean_kernel_output(self):
        self.assertTrue(module.clean_kernel_compile_output(""))

    def test_accepts_standard_kernel_axioms(self):
        self.assertTrue(module.clean_kernel_compile_output(
            "'AEGIS.Example.t' depends on axioms: [propext, Classical.choice, Quot.sound]"))

    def test_rejects_sorry_axiom_even_if_lean_returns_zero(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "'AEGIS.Example.t' depends on axioms: [sorryAx]"))

    def test_rejects_sorry_warning_even_if_lean_returns_zero(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "warning: declaration uses 'sorry'"))

    def test_rejects_nonstandard_axiom_report(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "'AEGIS.Example.t' depends on axioms: [Classical.choice, User.cheat]"))

    def test_rejects_lean_error_in_stdout(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "Example.lean:18:9: error: unsolved goals"))

    def test_rejects_named_declaration_sorry_warning(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "warning: declaration 'AEGIS.SomeTheorem' uses 'sorry'"))

    def test_rejects_global_lean_error_without_file_location(self):
        self.assertFalse(module.clean_kernel_compile_output(
            "error(lean.unknownIdentifier): unknown identifier"))


if __name__ == "__main__":
    unittest.main()
