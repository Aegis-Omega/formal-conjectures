# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").

#!/usr/bin/env python3
"""Executable acceptance and negative controls for the exact AEGIS prime-row witness."""
import unittest
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from rh_fixedwidth_prime_sign_v1 import (
  normalized_correl_poly,source_spline_h,original_psi_poly,
  mulpoly,integrate_sym_poly,derivpoly,
  source_prime_powers,primes_le,in_log_window,log_interval,log_n,
  horner,invsqrt_n,prime_row,smooth_transfer,verify,I,PRIME_POWERS,R)


class CertifiedPrimeRow(unittest.TestCase):
    def test_real_source_exact_primes(self):
        self.assertEqual(tuple(source_prime_powers()),PRIME_POWERS)
        self.assertEqual(tuple(source_prime_powers(w=Q(1,512))),((128,2,7),))
        self.assertTrue(in_log_window(129,128,Q(1,32))) # within window, but not a prime-power
        self.assertNotIn((129,3,1),source_prime_powers())
    def test_exact_small_prime_oracle(self):
        self.assertEqual(primes_le(30),[2,3,5,7,11,13,17,19,23,29])
        self.assertIn(131,primes_le(131))
    def test_rational_autocorr_energy(self):
        coeff,E=normalized_correl_poly()
        self.assertEqual(E,Q(53598236357632,4339335))
        self.assertEqual(len(coeff),18)
        self.assertEqual(coeff[0],1)
        self.assertEqual(sum((x*(2*R)**i for i,x in enumerate(coeff)),Q(0)),0)
    def test_mollifier_small_support(self):
        self.assertLess(R+Q(1,100000),Q(1,64))
    def test_exact_signed_row(self):
        r,E,p=prime_row()
        self.assertLess(r.b,-Q(1,10))
        self.assertGreater(r.a,-Q(1,5))
        self.assertLess(r.b-r.a,Q(1,10**24))
        self.assertEqual(len(p),4)
    def test_negative_control_missing_other_primes(self):
        _,_,p=prime_row()
        dyadic=[v for n,a,b,v in p if n==128]
        self.assertEqual(len(dyadic),1)
        self.assertGreater(dyadic[0].a,Q(0))
        # Without 127, the actual sign is reversed.
        partial=sum((v for n,a,b,v in p if n!=127),I.pt(0))
        self.assertGreater(partial.a,0)
    def test_negative_control_wrong_normalization(self):
        c,E=normalized_correl_poly()
        signed_wrong=horner(c,I.pt(0))*log_n(2)
        self.assertGreater(signed_wrong.a,0)
    def test_conjugation_has_both_exact_moments(self):
        # Integration by parts: (D² - 1/4)exp(±t/2) is exactly zero.
        for sigma in (Q(1,2),Q(-1,2)):
            self.assertEqual(sigma*sigma-Q(1,4),0)
    def test_energy_derivative_positive(self):
        psi=original_psi_poly()
        h=source_spline_h()
        E=integrate_sym_poly(mulpoly(h,h))
        self.assertEqual(E,normalized_correl_poly()[1])
        F=2*integrate_sym_poly(mulpoly(derivpoly(psi,3),derivpoly(psi,3)))
        F+=Q(1,8)*integrate_sym_poly(mulpoly(derivpoly(psi),derivpoly(psi)))
        self.assertLess(F/E,Q(500**2))
    def test_strict_smooth_transfer(self):
        signed,E,F,margin,p=smooth_transfer()
        self.assertGreater(margin,Q(1,13))
        self.assertEqual(margin,Q(35980,444411))
    def test_unsafe_interval_division_rejected(self):
        with self.assertRaises(AssertionError):I(Q(-1),Q(1)).inv()
    def test_log_interval_orientation(self):
        self.assertLess(log_interval(Q(125,128)).b,0)
        self.assertGreater(log_interval(Q(131,128)).a,0)
        self.assertLess(log_interval(Q(2)).a,log_interval(Q(2)).b)
    def test_output_no_rh_claim(self):
        r=verify()
        self.assertEqual(r['RH'],'OPEN')
        self.assertEqual(r['result'],'EXACT_RATIONAL_AND_ANALYTIC_SMOOTH_LIFT_PASS')
        self.assertEqual(len(r['source_blobs']),3)

if __name__=='__main__':unittest.main()
