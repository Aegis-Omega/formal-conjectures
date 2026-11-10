# Notes on `tools/cert43.py` (2026-11-10)

Two properties of the tool matter when it is used outside the 139-atom case.

1. It rejects an input when some exponent `dd = -e` is negative, that is, when some diagonal of
   `P` is below `1/2` in its units (`assert all(x >= 0 for x in dd)`). Multiplying `P` by `4^r`
   lowers every `e_i` by `r`, so the normalized matrix `P_ij 2^(e_i + e_j)` is exactly the same and
   the assertion passes. `rescale_pkl.py` does this. The operator reproduced the failure and the
   repair independently on a small positive definite matrix.

2. It writes `cert43_<q>.pkl` unconditionally, also when it prints `ok False`. The printed `ok` is
   the inequality `eta < eps`. A finished process and an output file are not a pass. Run
   `check_cert_pkl.py cert43_<q>.pkl`, which exits 0 only if `eta < eps` and no `dd` is negative.

The two certificates of `CERT_FEASIBILITY_32.log` pass that check:

    q 80  eps 6381974865710755  eta 109437308285859  min dd 0  eta < eps: True
    q 88  eps 1633785565621953385  eta 1778791743601083  min dd 0  eta < eps: True

This is still untrusted Python. The Lean kernel has to recheck the factor in a port.
