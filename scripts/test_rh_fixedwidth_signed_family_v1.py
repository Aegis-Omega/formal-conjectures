#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").
"""Regression tests for source-bound signed Weil witness family."""
import unittest
from fractions import Fraction as Q
from rh_fixedwidth_signed_family_v1 import BUDGET, source_row, certify, verify
from rh_fixedwidth_prime_sign_v1 import I

class FixedWidthSignedFamily(unittest.TestCase):
    def test_k7_all_prime_powers(self):
        b,w,E,items=source_row(7)
        self.assertEqual([n for n,_,_,_ in items],[125,127,128,131])
        self.assertLess(b.b,-Q(124036,1000000))
    def test_k10_all_prime_powers(self):
        b,w,E,items=source_row(10)
        self.assertEqual([n for n,_,_,_ in items],
            [997,1009,1013,1019,1021,1024,1031,1033,1039,1049,1051])
        self.assertLess(b.b,-Q(59,250))
    def test_k11_all_prime_powers(self):
        b,w,E,items=source_row(11)
        self.assertEqual(len(items),18)
        self.assertLess(b.b,-Q(1,10))
    def test_three_full_weil_margins(self):
        for k,(_,_,floor) in BUDGET.items():
            with self.subTest(k=k):
                cert=certify(k)
                self.assertGreater(Q(cert["rational_full_margin"]),floor)
                self.assertEqual(cert["RH"],"OPEN")
    def test_dyadic_only_is_wrong_sign(self):
        b,w,E,items=source_row(10)
        dy=[v for n,p,e,v in items if n==1024]
        self.assertEqual(len(dy),1)
        self.assertGreater(dy[0].a,0)
        self.assertLess(b.b,0)
    def test_k8_not_promoted(self):
        b,w,E,items=source_row(8)
        self.assertGreater(b.a,0)
        with self.assertRaises(KeyError):certify(8)
    def test_invalid_weight_or_sign_budget_rejected(self):
        old=BUDGET[11]
        try:
            BUDGET[11]=(Q(1,5),old[1],old[2])
            with self.assertRaises(AssertionError):certify(11)
        finally:BUDGET[11]=old
    def test_no_global_rh_claim(self):
        rec=verify()
        self.assertEqual(len(rec["cases"]),3)
        self.assertEqual(rec["RH"],"OPEN")
        self.assertEqual(rec["LEAN_KERNEL"],"OPEN")

if __name__=="__main__":
    unittest.main()
