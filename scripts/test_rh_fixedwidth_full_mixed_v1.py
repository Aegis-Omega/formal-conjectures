# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").

"""Regression tests for the source-bound full mixed Weil entry."""
import unittest
from fractions import Fraction as Q

from rh_fixedwidth_prime_sign_v1 import smooth_transfer
from rh_fixedwidth_full_mixed_v1 import (
    PRIME_STRICT, ARCH_MAX, TOTAL_STRICT, actual_full_mixed_bound,
)


class FullWeilMixed(unittest.TestCase):
    def test_signed_prime_source_bound(self):
        signed, E, F, margin, terms = smooth_transfer()
        self.assertLess(signed.b, -Q(1, 10))
        self.assertGreater(margin, Q(1, 9))

    def test_arch_additive_bound(self):
        self.assertEqual(PRIME_STRICT-ARCH_MAX, TOTAL_STRICT)
        self.assertEqual(TOTAL_STRICT, Q(91, 900))

    def test_strict_positive_margin(self):
        self.assertGreater(TOTAL_STRICT, Q(1, 10))

    def test_negative_control_insufficient_arch(self):
        self.assertLess(PRIME_STRICT-Q(1, 8), Q(0))

    def test_actual_source_import_reuse(self):
        obj=actual_full_mixed_bound()
        self.assertIn('WeilSeparatedArchBridgeV31.lean', obj['v31_source']['path'])
        self.assertEqual(obj['full_strict_margin'], '91/900')
        self.assertEqual(obj['RH'], 'OPEN')

    def test_source_analytic_guard(self):
        self.assertLess(Q(1, 68)+Q(1, 100000), Q(1, 64))
        self.assertEqual(actual_full_mixed_bound()['prime_powers'],
                         [125, 127, 128, 131])


if __name__ == '__main__':
    unittest.main()
