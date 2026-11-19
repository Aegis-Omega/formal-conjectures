# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").
"""Independent exact-rational moment-operator correlation tests."""
import unittest
from fractions import Fraction as F
from rh_independent_moment_operator_oracle import (
    derivative, add, value, phi_correlation_q, h_correlation_s, verify,
)

class MomentOperatorOracle(unittest.TestCase):
    def test_untwisted_phi_correlation(self):
        p=phi_correlation_q()
        self.assertEqual(max(p),17)
        self.assertEqual(value(p,F(0)),F(65536,109395))
        self.assertEqual(value(p,F(2)),0)
    def test_exact_energy(self):
        coeff,E=h_correlation_s()
        self.assertEqual(E,F(53598236357632,4339335))
        self.assertEqual(value(coeff,F(2,68)),0)
    def test_two_derivative_operator(self):
        p=phi_correlation_q()
        from_r=add((F(68)**4,derivative(p,4)),
                   (-F(1,2)*F(68)**2,derivative(p,2)),(F(1,16),p))
        c,E=h_correlation_s()
        self.assertEqual(value(from_r,F(0))/68,E)
    def test_wrong_cross_term_sign_rejected(self):
        p=phi_correlation_q()
        flipped=add((F(68)**4,derivative(p,4)),
                    (F(1,2)*F(68)**2,derivative(p,2)),(F(1,16),p))
        c,E=h_correlation_s()
        self.assertNotEqual(value(flipped,F(0))/68,E)
    def test_independent_comparison_and_source_status(self):
        r=verify()
        self.assertEqual(r['status'],'EXACT_RATIONAL_INDEPENDENT_CORRELATION_PASS')
        self.assertEqual(r['RH'],'OPEN')
        self.assertEqual(r['Lean_kernel'],'OPEN')

if __name__=='__main__':
    unittest.main()
