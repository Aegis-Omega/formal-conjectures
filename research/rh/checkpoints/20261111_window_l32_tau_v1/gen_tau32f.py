"""Untrusted exact mirror of CvSTauFastL32V1.tauF (window L = 3/2, prime powers 2, 3, 4): picks the
number J of head terms, computes the integer heads hLo/hHi, the source box, the prime part and the
outward-rounded tau box (scale 2^48). The kernel re-checks every box; this script only proposes them.
usage: as a module, box(k, tgt) -> (J, lo, hi); or  gen_tau32f.py K1 K2  (prints a summary)."""
import math
import sys
from fractions import Fraction as F
from math import floor, ceil, factorial

S64, S48 = 2 ** 64, 2 ** 48
D = 18446744073709551616
piLo = F(314159265358979323846, 10 ** 20); piHi = F(314159265358979323847, 10 ** 20)
pLoN, pHiN, Dk = 314159265358979323846, 314159265358979323847, 3 * 10 ** 20
l2Lo, l2Hi = F(12786308645202655659, D), F(12786308645202655660, D)
l3Lo, l3Hi = F(20265819725292939637, D), F(20265819725292939639, D)
s2Lo, s2Hi = F(13043817825332782212, D), F(13043817825332782213, D)
s3Lo, s3Hi = F(10650232656628343401, D), F(10650232656628343402, D)
e34Lo = F(146190367214327850032107338, 309485009821345068724781056)
e34Hi = F(73095183607163925016053672, 154742504910672534362390528)
j0 = 12
def Ehi(j): return e34Hi ** (4 * min(j, j0) + 1)
def Elo(j): return e34Lo ** (4 * j + 1) if j < j0 else F(0)
NEloT = [floor((1 - Ehi(j)) * S64) for j in range(13)]
NEhiT = [ceil((1 - Elo(j)) * S64) for j in range(13)]
assert NEloT == [9733119166315628212, 18012918234713208232, 18425145157003694732, 18445668726966845320, 18446690535347753337, 18446741408191472461, 18446743941001220773, 18446744067102392875, 18446744073380600552, 18446744073693174106, 18446744073708736227, 18446744073709511020, 18446744073709549594]
assert NEhiT[-1] == S64
def cw(j): return 2 * j + F(1, 2)
def hLo(a, b, J):
    h, Q = 0, None
    for j in range(J):
        h += 8 * a * NEloT[min(j, 12)] * Dk // ((4 * j + 1) ** 2 * Dk ** 2 + 4 * b ** 2)
    return h
def hHi(a, b, J):
    h = 0
    for j in range(J):
        h += 8 * b * NEhiT[min(j, 12)] * Dk // ((4 * j + 1) ** 2 * Dk ** 2 + 4 * a ** 2) + 1
    return h
def atP(x, n): return sum((-1) ** i * x ** (2 * i + 1) / (2 * i + 1) for i in range(n))
def omLo(k): return 4 * piLo * k / 3
def omHi(k): return 4 * piHi * k / 3
def src(k, J, K):
    a, b = 4 * pLoN * k, 4 * pHiN * k
    d = cw(J) - 1
    lo = F(hLo(a, b, J), S64) + atP(omLo(k) / d, 2 * K) - omHi(k) / 3 * (1 / d ** 3) - Ehi(j0) * atP(omHi(k) / d, 2 * K + 1)
    hi = F(hHi(a, b, J), S64) + atP(omHi(k) / d, 2 * K + 1)
    ok = (1 <= omLo(k) and j0 <= J and 2 < cw(J) and omHi(k) ** 2 / 3 + 3 <= cw(J) ** 2 and omHi(k) / d < 1
          and 0 <= lo and 0 <= hi)
    return ok, lo, hi
# sine machinery (mirror of CvSTauPrimeL12V1)
def rdn(x): return F(floor(x * S64), S64)
def sinPartial(x, n): return sum((-1) ** i * x ** (2 * i + 1) / factorial(2 * i + 1) for i in range(n))
def sinLoQ(x): return sinPartial(x, 14) if x >= 0 else -sinPartial(-x, 15)
def sinHiQ(x): return sinPartial(x, 15) if x >= 0 else -sinPartial(-x, 14)
def mid(ul): return floor(ul + F(1, 2))
def thLo(ul): d = ul - mid(ul); return rdn(min(piLo * d, piHi * d))
def thHi(ul, uh): d = uh - mid(ul); return max(piLo * d, piHi * d)
def baseLo(ul, uh): return sinLoQ(thLo(ul)) - (thHi(ul, uh) - thLo(ul))
def baseHi(ul, uh): return sinHiQ(thLo(ul)) + (thHi(ul, uh) - thLo(ul))
def sinPiLo(ul, uh): return baseLo(ul, uh) if mid(ul) % 2 == 0 else -baseHi(ul, uh)
def sinPiHi(ul, uh): return baseHi(ul, uh) if mid(ul) % 2 == 0 else -baseLo(ul, uh)
w2Lo, w2Hi = l2Lo * (2 * s2Lo), l2Hi * (2 * s2Hi)
w3Lo, w3Hi = l3Lo * (2 * s3Lo), l3Hi * (2 * s3Hi)
def args(k): return [(4 * k * l2Lo / 3, 4 * k * l2Hi / 3, w2Lo, w2Hi), (4 * k * l3Lo / 3, 4 * k * l3Hi / 3, w3Lo, w3Hi),
                     (8 * k * l2Lo / 3, 8 * k * l2Hi / 3, l2Lo, l2Hi)]
def primeLo(k):
    s = sum(min(wl * sinPiLo(ul, uh), wh * sinPiLo(ul, uh)) for ul, uh, wl, wh in args(k))
    return min(piLo * s, piHi * s)
def primeHi(k):
    s = sum(max(wl * sinPiHi(ul, uh), wh * sinPiHi(ul, uh)) for ul, uh, wl, wh in args(k))
    return max(piLo * s, piHi * s)
def pickJ(k, tgt):
    w = 4 * math.pi * k / 3
    return max(int(2 * w) + 2, int(((math.pi * w / tgt) ** (1 / 3)) / 2) + 2, 150)
def box(k, tgt, K=20):
    J = pickJ(k, tgt)
    ok, sl, sh = src(k, J, K)
    assert ok, k
    assert all(abs(thLo(ul)) <= 2 for ul, _, _, _ in args(k))
    a, b = piLo * sl + primeLo(k), piHi * sh + primeHi(k)
    lo, hi = F(floor(a * S48), S48), F(ceil(b * S48), S48)
    assert lo <= a and b <= hi
    return J, lo, hi
def tgt_of(k): return 3e-10 if k <= 150 else 3e-9

if __name__ == '__main__':
    k1, k2 = int(sys.argv[1]), int(sys.argv[2])
    import mpmath as mp
    mp.mp.dps = 40
    for k in range(k1, k2 + 1):
        J, lo, hi = box(k, tgt_of(k))
        w = 4 * mp.pi * k / 3; L = mp.mpf(3) / 2
        # sum_j 2w/(c_j^2 + w^2) = Im psi(1/4 + i w/2); the exponential part converges fast
        s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2)) - mp.fsum(2 * w * mp.e ** (-(2 * j + mp.mpf(1) / 2) * L) / ((2 * j + mp.mpf(1) / 2) ** 2 + w ** 2) for j in range(80))
        p = (mp.sqrt(2) * mp.log(2) * mp.sin(mp.pi * 4 * k * mp.log(2) / 3) + 2 * mp.log(3) / mp.sqrt(3) * mp.sin(mp.pi * 4 * k * mp.log(3) / 3)
             + mp.log(2) * mp.sin(mp.pi * 8 * k * mp.log(2) / 3))
        v = mp.pi * s + mp.pi * p
        inside = lo <= F(mp.nstr(v, 25)) <= hi
        print(f'k={k} J={J} width={float(hi - lo):.3e} tau~{mp.nstr(v, 15)} inside={inside}')
