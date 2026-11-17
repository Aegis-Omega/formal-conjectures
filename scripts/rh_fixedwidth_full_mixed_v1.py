# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").

"""Source-bound composition: a strict SIGNED mixed Weil entry at 7 log 2.

The already-source-bound rational sign certificate is in
rh_fixedwidth_prime_sign_v1.py. We combine it with the EXISTING theorem
AEGIS.WeilSeparatedArchBridgeV31.translated_arch_norm_bound.

Assumptions preserved from V31:
  g smooth compact on log-support width <= 1/32,
  two Weil moments zero, and separation d >= log 2.

For the constructed g, B(T_0 g,T_(7log2)g) has
  Re prime < -E/13, center = 0, |Arch| <= E/100,
hence Re B < -(87/1300) E.

NOT a proof of all-window Weil sign, a PSD Gram, or RH.
The combined theorem still needs Lean kernel replay.
"""
from fractions import Fraction as Q
from rh_fixedwidth_prime_sign_v1 import smooth_transfer

PRIME_STRICT = Q(1, 13)
ARCH_MAX = Q(1, 100)
TOTAL_STRICT = PRIME_STRICT - ARCH_MAX


def actual_full_mixed_bound():
    signed, original_E, derivative_F, prime_margin, terms = smooth_transfer()
    assert signed.b < -Q(1, 10)
    assert prime_margin > PRIME_STRICT
    assert [n for n, p, a, z in terms] == [125, 127, 128, 131]
    assert Q(1, 68) + Q(1, 100000) < Q(1, 64)
    assert TOTAL_STRICT == Q(87, 1300)
    return {
        "claim": "Exists smooth compact moment-zero g with Re B(g,T_(7log2)g) < -(87/1300)*energy(g)",
        "prime_margin": str(PRIME_STRICT),
        "arch_max": str(ARCH_MAX),
        "full_strict_margin": str(TOTAL_STRICT),
        "prime_powers": [125, 127, 128, 131],
        "center_term": "zero by disjoint log support",
        "v31_source": {
            "repo": "Aegis-Omega/formal-conjectures",
            "commit": "ce4868fd074879eb4e6bc8085fb67d28ff371e0c",
            "path": "AegisRH/PR606/WeilSeparatedArchBridgeV31.lean",
            "blob": "9143a15eb6124b8d7461b68ebb6bd89786988294",
            "theorem": "AEGIS.WeilSeparatedArchBridgeV31.translated_arch_norm_bound"
        },
        "full_Gram_positive": "NOT_ESTABLISHED",
        "RH": "OPEN",
        "kernel_replay": "OPEN"
    }


if __name__ == "__main__":
    import json
    print(json.dumps(actual_full_mixed_bound(), indent=2, sort_keys=True))
