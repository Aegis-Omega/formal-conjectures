"""Smallest generalized eigenvalues of the receipts written by fixed_window_true_matrix_arb.py (PR #7):
min over x of x^T K x / x^T G x, with K the midpoints of the Arb matrix `K` and G the exact rational
`gram_exact_rational`, in mpmath at 110 digits. Floating-point analysis of the midpoints only; the
certified statement is the receipt's own `unshifted_verified` (Arb interval LDL or rational Gershgorin).
usage: python3 eig_fw.py RECEIPT.json [...]"""
import json
import sys
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 110
print('ell N dim lam_min lam_max max_rad unshifted_verified')
for path in sys.argv[1:]:
    p = json.load(open(path))
    for r in p['results']:
        K = mp.matrix([[mp.mpf(e['mid']) for e in row] for row in r['K']])
        rad = max(mp.mpf(e['rad']) for row in r['K'] for e in row)
        G = mp.matrix([[mp.mpf(Fraction(s).numerator) / Fraction(s).denominator for s in row]
                       for row in r['gram_exact_rational']])
        Li = mp.inverse(mp.cholesky(G))
        A = Li * K * Li.T
        ev = sorted(mp.eigsy((A + A.T) / 2, eigvals_only=True))
        print(p['ell'], r['N'], r['N'] - 2, mp.nstr(ev[0], 6), mp.nstr(ev[-1], 6), mp.nstr(rad, 3),
              r['claims'].get('single_N_unshifted_positive_definite_verified', r.get('unshifted_verified')))
