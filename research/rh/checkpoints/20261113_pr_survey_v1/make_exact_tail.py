"""Derive the exact-Gram-tail variant of feshbach_arb_v2/feshbach_blocks_arb.py.

The rows |n| > NP of the cutoff-free CvS matrix are entry(n, m) = pole(n, m) + (tau_n - tau_m)/(pi (n - m)) for m in the band,
so (Qv)_n = pole_n(v) + (tau_n Y_n - X_n)/pi with Y_n = sum v_m/(n - m), X_n = sum tau_m v_m/(n - m) and |tau_n| <= K2.
The order-K expansion of 1/(n - m) and its remainder Eco are replaced by the exact Gram
Gup(m, m') = sum_(|n| > NP) 1/((n - m)(n - m')) (digamma / trigamma, in Arb), as CvSGramTailV1.gram_tail_le does in Lean,
and a four-term weighted Cauchy-Schwarz (EXW=uniform: 1/4 each; EXW=mixed: half uniform, half sqrt-optimal for the bottom
Ritz vector; any fixed weights are valid). Everything else (rows |n| <= NP, moment basis, blocks, Schur input) is unchanged.
usage: python3 make_exact_tail.py V2/feshbach_blocks_arb.py OUT.py"""
import hashlib
import sys

V2_SHA256 = 'c8e5afe44f6fd8831611caf67ab7a6ecb9cba88c8bd74dd953962fdd7e51a0c0'
BLOCK = '''# Exact tail (as CvSGramTailV1.gramTail): for |n| > NP and m in the band, entry(n, m) = pole(n, m) + (tau_n - tau_m)/(pi (n - m)),
# tau_k = S_k (signed) + sum_q w_q sin(2 pi k y_q / L) = -alpha_k, |tau_n| <= K2 for |n| > NP. With Y_n = sum v_m/(n - m),
# X_n = sum tau_m v_m/(n - m): (Qv)_n = pole_n(v) + (tau_n Y_n - X_n)/pi, |pole_n| <= Cc|lb|/|n| + Cc beta^2 |la|/n^2.
# Weighted Cauchy-Schwarz over four terms; sum_{|n|>NP} |Y_n|^2 = v* Gup v, sum |X_n|^2 = (tau v)* Gup (tau v), with the exact
# Gup(m, m') = sum_{|n|>NP} 1/((n - m)(n - m')) = [psi(N0 - m') - psi(N0 - m) + psi(N0 + m) - psi(N0 + m')]/(m - m'),
# Gup(m, m) = psi'(N0 - m) + psi'(N0 + m), N0 = NP + 1.
N0 = NP + 1
psm = {m: arb(N0 - m).digamma() for m in band}; psp = {m: arb(N0 + m).digamma() for m in band}
tri = {m: acb(N0 - m).polygamma(acb(1)).real + acb(N0 + m).polygamma(acb(1)).real for m in band}
nb = len(band)
Gup = arb_mat(nb, nb)
for i, m in enumerate(band):
    for j, mp_ in enumerate(band):
        Gup[i, j] = tri[m] if m == mp_ else (psm[mp_] - psm[m] + psp[m] - psp[mp_]) / (m - mp_)
tauv = [-a_ for a_ in alpha]
Dt = arb_mat(nb, nb)
for i in range(nb): Dt[i, i] = tauv[i]
TX = acb_mat(Dt * Gup * Dt) * (1 / (pi * pi))
TY = acb_mat(Gup) * (K2 * K2 / (pi * pi))
Tb = outer(bvec) * (2 * Cc * Cc / NP)
Ta = outer(avec) * (2 * Cc * Cc * beta ** 4 / (3 * arb(NP) ** 3))
terms = [TX, TY, Tb, Ta]
Zh = Z.conjugate().transpose()
A11 = Zh * Qb * Z; G11 = Zh * Z
def mid(M): return [[complex(float(M[i, j].real.mid()), float(M[i, j].imag.mid())) for j in range(M.ncols())] for i in range(M.nrows())]
import numpy as np
from scipy.linalg import eigh
_, U0 = eigh(np.array(mid(A11)), np.array(mid(G11))); v0 = np.array(mid(Z)) @ U0[:, 0]
tt = [abs(v0.conj() @ np.array(mid(T)) @ v0) for T in terms]
rr_ = [math.sqrt(x) + 1e-300 for x in tt]
import os
WMODE = os.environ.get("EXW", "mixed")
pw = [fmpq(1, 4)] * 4 if WMODE == "uniform" else [fmpq(int(1e9 * (0.5 / 4 + 0.5 * x / sum(rr_))), 10 ** 9) for x in rr_]
assert sum(pw) <= 1 and all(x > 0 for x in pw)
print('exact-tail terms on bottom Ritz', ['%.3e' % x for x in tt], 'weights', [str(x) for x in pw])
Tail = acb_mat(nb, nb)
for T, p_ in zip(terms, pw): Tail += T * arb(1 / p_)
Eco = arb(0); K = 0; WEIGHTS = 'exact4'
'''
t = open(sys.argv[1]).read()
assert hashlib.sha256(t.encode()).hexdigest() == V2_SHA256, 'unexpected feshbach_blocks_arb.py'
a, b = t.index('# Order-K expansion'), t.index("print('K2', K2")
t = t[:a] + BLOCK + t[b:]
t = t.replace('"tail_order": K, "tail_weights": [str(x) for x in pw]', '"tail_order": "exact", "tail_weights": [str(x) for x in pw]')
open(sys.argv[2], 'w').write(t)
print('written', sys.argv[2])
