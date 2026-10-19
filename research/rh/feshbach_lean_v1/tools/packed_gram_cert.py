"""Untrusted generator for `CvSPackedGramV1.check` certificates of the Hilbert matrix.

Usage: python3 packed_gram_cert.py N Q > HilbCert.lean

Prints a Lean file with `hilbL` and `hilb_check : check b B N eps eta hilbL (hilbIv Q N) = true`,
proved by `decide +kernel`; the kernel, not this script, decides. Standard library only.
"""
import sys
import textwrap
from decimal import Decimal, getcontext

n, q = int(sys.argv[1]), int(sys.argv[2])
assert q % 2 == 0
getcontext().prec = int(q * 0.30103) + 60
one = Decimal(1)
A = [[one / (i + j + 1) for j in range(n)] for i in range(n)]


def chol(M):
    C = [[Decimal(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = M[i][j] - sum(C[i][k] * C[j][k] for k in range(j))
            C[i][j] = s.sqrt() if i == j else s / C[j][j]
    return C


def solve(C, x):
    y = [Decimal(0)] * n
    for i in range(n):
        y[i] = (x[i] - sum(C[i][k] * y[k] for k in range(i))) / C[i][i]
    z = [Decimal(0)] * n
    for i in reversed(range(n)):
        z[i] = (y[i] - sum(C[k][i] * z[k] for k in range(i + 1, n))) / C[i][i]
    return z


# smallest eigenvalue by inverse iteration
C = chol(A)
x = [one] * n
for _ in range(60):
    y = solve(C, x)
    nrm = max(abs(t) for t in y)
    x = [t / nrm for t in y]
Ax = [sum(A[i][j] * x[j] for j in range(n)) for i in range(n)]
lam = sum(a * b for a, b in zip(Ax, x)) / sum(t * t for t in x)

S = 2 ** q
eps = int(lam / 2 * S)
C = chol([[A[i][j] - (Decimal(eps) / S if i == j else 0) for j in range(n)] for i in range(n)])
half = Decimal(2 ** (q // 2))
L = [[int((C[i][k] * half).to_integral_value()) if k <= i else 0 for k in range(n)]
     for i in range(n)]
eta = 0
for i in range(n):
    row = 0
    for j in range(n):
        lo = S // (i + j + 1)
        c = sum(L[i][k] * L[j][k] for k in range(n)) + (eps if i == j else 0)
        row += max(lo + 1 - c, c - lo)
    eta = max(eta, row)
B = max(abs(v) for r in L for v in r)
K = (n * n * 4 * B * B).bit_length() + 1
assert eta < eps, (eta, eps)
print('import CvSPackedGramV1')
print(f'-- n = {n}, q = {q}, lambda_min ~ {float(lam):.3e}, margin (eps - eta) / 2^q ~ '
      f'{float(Decimal(eps - eta) / S):.3e}')
print('namespace AEGIS.CvSPackedGramV1')
print('set_option maxRecDepth 100000')
print('set_option maxHeartbeats 0')
print('def hilbL : List (List ℤ) := [')
rows = ['\n'.join(textwrap.wrap('[' + ', '.join(str(v) for v in r) + ']', 96,
                                initial_indent='  ', subsequent_indent='   ',
                                break_long_words=False)) for r in L]
print(',\n'.join(rows) + ']')
print(f'theorem hilb_check : check (2 ^ {K}) {B} {n} {eps} {eta}\n'
      f'    hilbL (hilbIv {q} {n}) = true := by\n  decide +kernel')
print('end AEGIS.CvSPackedGramV1')
print('#print axioms AEGIS.CvSPackedGramV1.hilb_check')
