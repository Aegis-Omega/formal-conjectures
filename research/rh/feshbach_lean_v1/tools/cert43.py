"""Packed Gram certificate for the exact L = 4/3 check matrix P (untrusted).

Scales P by D = diag(2^-e_i) (P~ = D P D, P~_ii in [1/2, 2)), then finds eps and an integer L with
2^q P~ = L L^T + eps Id + E, |E| row sums <= eta < eps, exactly as CvSPackedGramV1.check does.
usage: python3 cert43.py q
"""
import pickle
import sys
import time
from fractions import Fraction as Fr

import mpmath as mp

t0 = time.time()
q = int(sys.argv[1])
d = pickle.load(open('rr43_data.pkl', 'rb'))
Pint = d['P']
PS = d['Pscale']
P = [[Fr(x, 2 ** PS) for x in r] for r in Pint]
n = len(P)
# e_i with P_ii 4^e_i in [1/2, 2): P~_ij = P_ij 2^(e_i + e_j)
e = []
for i in range(n):
    x = P[i][i]
    assert x > 0
    k = 0
    while x * Fr(4) ** k >= 2:
        k -= 1
    while x * Fr(4) ** k < Fr(1, 2):
        k += 1
    e.append(k)
Pt = [[P[i][j] * Fr(2) ** (e[i] + e[j]) for j in range(n)] for i in range(n)]
print('-- exponents e_i from %d to %d' % (min(e), max(e)), file=sys.stderr)
mp.mp.dps = 120
M = mp.matrix(n, n)
for i in range(n):
    for j in range(n):
        M[i, j] = mp.mpf(Pt[i][j].numerator) / Pt[i][j].denominator
ev = mp.eigsy(M, eigvals_only=True)
lmin, lmax = min(ev), max(ev)
print('-- scaled: lambda_min %s  lambda_max %s  cond %s  (%.1fs)' % (
    mp.nstr(lmin, 6), mp.nstr(lmax, 6), mp.nstr(lmax / lmin, 4), time.time() - t0), file=sys.stderr)
S = mp.mpf(2) ** q
eps = int(lmin / 2 * S)
Mc = M.copy()
for i in range(n):
    Mc[i, i] -= mp.mpf(eps) / S
C = mp.cholesky(Mc)
half = mp.mpf(2) ** (q // 2)
L = [[int(mp.nint(C[i, k] * half)) if k <= i else 0 for k in range(n)] for i in range(n)]
SI = 2 ** q
dd = [-x for x in e]
assert all(x >= 0 for x in dd)
lo = [[Pint[i][j] >> (PS - q + dd[i] + dd[j]) for j in range(n)] for i in range(n)]
hi = [[lo[i][j] + 1 for j in range(n)] for i in range(n)]
for i in range(n):
    for j in range(n):
        assert lo[i][j] <= Pt[i][j] * SI <= hi[i][j]
eta = 0
for i in range(n):
    row = 0
    for j in range(n):
        c = sum(L[i][k] * L[j][k] for k in range(n)) + (eps if i == j else 0)
        row += max(hi[i][j] - c, c - lo[i][j])
    eta = max(eta, row)
B = max(abs(v) for r in L for v in r)
K = (n * n * 4 * B * B).bit_length() + 1
print('-- q %d  eps %d  eta %d  ok %s  B bits %d  base 2^%d  (%.1fs)' % (
    q, eps, eta, eta < eps, B.bit_length(), K, time.time() - t0), file=sys.stderr)
chars = sum(len(str(v)) + 2 for r in L for v in r[:])
print('-- certL text ~ %d KB' % (chars // 1024), file=sys.stderr)
pickle.dump({'dd': dd, 'e': e, 'L': L, 'eps': eps, 'eta': eta, 'B': B, 'K': K, 'q': q}, open('cert43_%d.pkl' % q, 'wb'))
