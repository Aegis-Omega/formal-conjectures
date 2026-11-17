#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").
"""Source-bound fixed-width signed Weil rows at multiple dyadic gaps.

For ONE existing AEGIS smooth compact two-moment packet, verify particular
negative OFF-DIAGONAL entries using the full von Mangoldt prime-power sum.
This is NOT a global Weil sign or a proof of RH.

AEGIS formal-conjectures source @ ce4868fd074879eb4e6bc8085fb67d28ff371e0c:
WeilCriterionCompactSmoothV1 (prime normalization);
WeilThreeBlockCrossPrimeV28 (mixed log correlation);
WeilSeparatedArchBridgeV31 (Arch <= E/100 for width <=1/32).

Arithmetic is exact rational intervals. The smooth mollifier is analytic:
h=(D^2-1/4)psi and ||h_eps-h||_2 <= eps ||h'||_2 < sqrt(E)/200.
"""
from __future__ import annotations
from fractions import Fraction as Q
from rh_fixedwidth_prime_sign_v1 import (
    R, EPS, I, source_prime_powers, normalized_correl_poly,
    log_interval, log_n, invsqrt_n, horner, original_psi_poly,
    derivpoly, mulpoly, integrate_sym_poly,
)

# Every claimed floor and weight ceiling MUST be checked against the actual
# source-computed rational interval, never passed to an unchecked helper.
BUDGET = {
    7: (Q(124036,1000000), Q(11,10), Q(1,10)),
    10: (Q(59,250), Q(11,5), Q(1,5)),
    11: (Q(1,10), Q(3), Q(1,20)),
}

def source_row(k:int):
    assert 1 <= k <= 16, "EXPLICIT_FINITE_ENUMERATION_ONLY"
    center=2**k
    width=2*R
    powers=source_prime_powers(centre=center,w=width)
    assert powers, "EMPTY_PRIME_SUPPORT"
    assert powers == source_prime_powers(centre=center,w=2*(R+EPS)), "SMOOTHING_ADDS_PRIME_POWER"
    # V31's permitted 1/32 log width is larger than the genuine support.
    # Extra primes in that larger window have zero mixed correlation.
    wider=source_prime_powers(centre=center,w=Q(1,32))
    assert set(powers).issubset(set(wider)), "SUPPORT_OUTSIDE_V31"
    assert 2*(R+EPS)<Q(1,32), "V31_WIDTH_NOT_PROVED"
    coeff,E=normalized_correl_poly()
    signed=I.pt(0)
    weights=I.pt(0)
    entries=[]
    for n,p,e in powers:
        assert p>=2 and e>=1 and p**e==n
        shift=I.pt(0) if n==center else log_interval(Q(center,n)).abs_known()
        assert shift.b<width, "CORRELATION_OUTSIDE_SUPPORT"
        weight=log_n(p)*invsqrt_n(n)
        term=weight*horner(coeff,shift)
        signed+=term
        weights+=weight
        entries.append((n,p,e,term))
    return signed,weights,E,entries

def certify(k:int):
    prime_floor, weight_ceil, target=BUDGET[k]
    signed,weights,E,entries=source_row(k)
    assert signed.b < -prime_floor, "NO_SIGN_CERTIFICATE"
    assert weights.b < weight_ceil, "UNBOUND_PRIME_WEIGHTS"
    psi=original_psi_poly()
    F=2*integrate_sym_poly(mulpoly(derivpoly(psi,3),derivpoly(psi,3)))
    F+=Q(1,8)*integrate_sym_poly(mulpoly(derivpoly(psi),derivpoly(psi)))
    assert F/E < 500**2, "UNBOUND_DERIVATIVE"
    assert R+EPS<Q(1,64), "WIDTH_FAIL"
    delta=500*EPS
    assert delta==Q(1,200)
    # |C_eps(s)-C(s)|<= (2*delta+delta^2)*E for EVERY real shift.
    smooth_floor=prime_floor-weight_ceil*(2*delta+delta**2)
    assert smooth_floor>0
    prime_margin=smooth_floor/(1+delta)**2
    # Existing V31: |Arch|<=E_eps/100; mixed center=0 by disjoint supports.
    full_margin=prime_margin-Q(1,100)
    assert full_margin>target, "STRICT_FULL_WEIL_SIGN_NOT_PROVED"
    return {
        "k":k,
        "strict_full_Weil_bound":f"Re B(g,T_({k}log2)g) < -({target})*energy(g)",
        "rational_full_margin":str(full_margin),
        "source_power_count":len(entries),
        "source_powers":[[n,p,e] for n,p,e,_ in entries],
        "prime_source_floor":str(prime_floor),
        "all_prime_weights_upper":str(weight_ceil),
        "smooth_prime_floor":str(prime_margin),
        "packet_full_log_width":str(2*(R+EPS)),
        "existing_arch_source":"AEGIS.WeilSeparatedArchBridgeV31.translated_arch_norm_bound",
        "arithmetic":"EXACT_RATIONAL_INTERVAL",
        "RH":"OPEN", "LEAN_KERNEL":"OPEN",
    }

def verify():
    cases=[certify(k) for k in sorted(BUDGET)]
    assert len(cases)==3
    return {"schema":"AEGIS_SIGNED_FIXED_WIDTH_WEIL_FAMILY_V1",
            "result":"EXACT_RATIONAL_INTERVAL_REPLAY_PASS",
            "packet":"ONE compact smooth packet with both moments zero",
            "cases":cases,"RH":"OPEN","LEAN_KERNEL":"OPEN"}

if __name__=="__main__":
    import json
    print(json.dumps(verify(),indent=2))
