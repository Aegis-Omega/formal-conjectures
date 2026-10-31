"""Untrusted mirror of CvSTauL118V1.tauCheck: prints tauJ, tauLo, tauHi for k = KMIN..KMAX.

Port of feshbach_lean_v1/tools/gen_tau43.py to L = 11/8 (e^{-11/16}, omega_k = 16 pi k / 11), with
the arctan tail target TGT (box width about TGT / 3; 6e-8 gives boxes of radius about 1e-8).
Usage: python3 gen_tau118.py KMIN KMAX [TGT]. The kernel re-checks every box; this script only
proposes them.
"""
import math
import sys
from fractions import Fraction as F

piLo = F(314159265358979323846, 10**20); piHi = F(314159265358979323847, 10**20)
e1116Lo = F(155618835846819101613238945, 309485009821345068724781056)
e1116Hi = F(77809417923409550806619473, 154742504910672534362390528)
j0 = 12
cw = lambda j: 2 * j + F(1, 2)
Ehi = lambda j: e1116Hi ** (4 * min(j, j0) + 1)
Elo = lambda j: e1116Lo ** (4 * j + 1) if j < j0 else F(0)
R64 = 2 ** 64
def rdn(x): return F(math.floor(x * R64), R64)
def rup(x): return F(math.ceil(x * R64), R64)
def headLo(wl, wh, J):
    h = F(0)
    for j in range(J): h = rdn(h + 2 * wl * (1 - Ehi(j)) / (cw(j) ** 2 + wh ** 2))
    return h
def headHi(wl, wh, J):
    h = F(0)
    for j in range(J): h = rup(h + 2 * wh * (1 - Elo(j)) / (cw(j) ** 2 + wl ** 2))
    return h
def atP(x, n): return sum((-1) ** i * x ** (2 * i + 1) / (2 * i + 1) for i in range(n))
def box(k, J, K):
    wl, wh = 16 * piLo * k / 11, 16 * piHi * k / 11
    d = cw(J) - 1
    lo = headLo(wl, wh, J) + atP(wl / d, 2 * K) - wh / 3 * (1 / d ** 3) - Ehi(j0) * atP(wh / d, 2 * K + 1)
    hi = headHi(wl, wh, J) + atP(wh / d, 2 * K + 1)
    return wl, wh, d, lo, hi
P = 2 ** 48
TGT = float(sys.argv[3]) if len(sys.argv) > 3 else 6e-8
def pickJ(k):
    w = 16 * math.pi * k / 11
    return max(int(2 * w) + 2, int(((math.pi * w / TGT) ** (1 / 3)) / 2) + 2, 150)


if __name__ == '__main__':
    kmin, kmax = int(sys.argv[1]), int(sys.argv[2])
    rows = []
    for k in range(kmin, kmax + 1):
        J, K = pickJ(k), 20
        wl, wh, d, lo, hi = box(k, J, K)
        assert 1 <= wl and j0 <= J and 2 < cw(J) and wh ** 2 / 3 + 3 <= cw(J) ** 2 and wh / d < 1
        assert lo >= 0 and hi >= 0
        rows.append((J, math.floor(piLo * lo * P), math.ceil(piHi * hi * P)))
    print('-- max width %.3e' % max((b - a) / P for _, a, b in rows), file=sys.stderr)
    print('def tauJ : List ℕ := [' + ', '.join(str(r[0]) for r in rows) + ']')
    print('def tauLo : List ℚ := [\n  ' + ',\n  '.join(f'{r[1]} / {P}' for r in rows) + ']')
    print('def tauHi : List ℚ := [\n  ' + ',\n  '.join(f'{r[2]} / {P}' for r in rows) + ']')
