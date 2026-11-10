"""Float mirror of the trace cell bound of CvSTraceCellL118V1.lean / CvSTraceIntegralL118V1.lean,
with the window LT, the atom range K and the prime powers as parameters.  Untrusted; no outward rounding.
  TD = (1 + eps) Aup + (1 + 1/eps) G2 (tb0 + tb1),   total = sum 2 (b - a) s TD,   s = max(0, m + W - h+(a)).
usage: trace_cells_k.py LT K m1,m2,... [TOP|0] [D1,D2,D3,D4]
(cell widths 1/D1 on [0,4], 1/D2 on [4,20], 1/D3 on [20,100], 1/D4 above; default 150,30,6,3)
"""
import sys
from fractions import Fraction as F
import mpmath as mp
import numpy as np

LTq, K = F(sys.argv[1]), int(sys.argv[2])
ms = [float(x) for x in sys.argv[3].split(',')]
LT = float(LTq)
h = 2 * np.pi / LT
x, y = np.exp(-LT / 2), np.exp(LT / 2)


def mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            q = n
            while q % p == 0:
                q //= p
            return np.log(p) if q == 1 else 0.0
    return 0.0


W = sum(2 * mangoldt(n) / np.sqrt(n) for n in range(2, int(np.floor(np.exp(LT))) + 1))
nG00, nG11 = 1 - x ** 2, y ** 2 - 1
Dlo = x ** 2 + y ** 2 - 2 - LT ** 2
tb0 = (1 - x) ** 2 / LT * (2 / (h * (h * K)))
tb1 = (y - 1) ** 2 / LT * (2 / (h * (h * K)))
rho0, rho1 = np.sqrt(tb0), np.sqrt(tb1)
r00, r11, r01 = rho0 ** 2, rho1 ** 2, rho0 * rho1
Den = Dlo - (nG00 * r11 + nG11 * r00 + 2 * LT * r01 + r00 * r11 + r01 * r01)
Yb0, Yb1 = 2 * (x + 1), 2 * (y + 1)
A1, A2 = 1 + LT, LT - 1


def nc(u1, u2, v1, v2):
    return dict(p0=u1 * u1 + v1 * v1, p2=u2 * u2 + v2 * v2, q0=u1 * v1, q2=u2 * v2, r=u2 * v1 - u1 * v2)


nc0 = nc((A1 * y - x) / 2, -A2 * y - x, (y * y + A2) / 2, y * y - A1)
nc1 = nc((-A2 * x - y) / 2, y - A1 * x, (x * x - A1) / 2, -A2 - x * x)


def rng(f, a, b):
    """The Lipschitz enclosure of sinPiLo / sinPiHi: value at the left end, plus or minus the angular width."""
    w = (b - a) * LT
    return f(a * LT) - w, f(a * LT) + w


def prodmax(xl, xh, yl, yh):
    return np.maximum(np.maximum(xl * yl, xl * yh), np.maximum(xh * yl, xh * yh))


def Pup(k, a, b, cl, ch, sl, sh):
    c1, c2 = -2 * (k['q0'] + k['q2'] * a * a), -2 * (k['q0'] + k['q2'] * b * b)
    r1, r2 = 2 * k['r'] * a, 2 * k['r'] * b
    return (k['p0'] + k['p2'] * b * b + prodmax(np.minimum(c1, c2), np.maximum(c1, c2), cl, ch)
            + prodmax(np.minimum(r1, r2), np.maximum(r1, r2), sl, sh))


hp = lambda t: float(mp.re(mp.digamma(mp.mpf(1) / 4 + 0.5j * t))) - float(mp.log(mp.pi))
mp.mp.dps = 20
print('LT=%s K=%d W=%.4f hK=%.2f tb0=%.3e tb1=%.3e Den=%.4f' % (LTq, K, W, h * K, tb0, tb1, Den))
for m in ms:
    tstar = float(mp.findroot(lambda t: hp(t) - (m + W), 2 * np.pi * np.exp(m + W)))
    top = float(sys.argv[4]) if len(sys.argv) > 4 and float(sys.argv[4]) > 0 else np.ceil(tstar)
    assert top < h * K, 'slack passes the atom range: t*=%.1f, hK=%.1f' % (tstar, h * K)
    dn = [int(v) for v in (sys.argv[5] if len(sys.argv) > 5 else '150,30,6,3').split(',')]
    edges = np.concatenate([np.arange(0, 4 * dn[0]) / dn[0], np.arange(4 * dn[1], 20 * dn[1]) / dn[1],
                            np.arange(20 * dn[2], 100 * dn[2]) / dn[2], np.arange(100 * dn[3], top * dn[3]) / dn[3],
                            [top]])
    edges = edges[edges <= top]
    a, b = edges[:-1], edges[1:]
    cl, ch = rng(np.cos, a, b)
    sl, sh = rng(np.sin, a, b)
    tail = 1 / (h * (h * K - b)) + 1 / (h * (h * K + a))
    Aup = (2 - 2 * cl) / LT * tail
    al = np.sqrt(Aup)
    n0 = np.sqrt(Pup(nc0, a, b, cl, ch, sl, sh)) / (a * a + 0.25)
    n1 = np.sqrt(Pup(nc1, a, b, cl, ch, sl, sh)) / (a * a + 0.25)
    d0 = nG11 * al * rho0 + r11 * Yb0 + r11 * al * rho0 + LT * al * rho1 + r01 * Yb1 + r01 * al * rho1
    d1 = nG00 * al * rho1 + r00 * Yb1 + r00 * al * rho1 + LT * al * rho0 + r01 * Yb0 + r01 * al * rho0
    G2 = ((n0 + d0) ** 2 + (n1 + d1) ** 2) / Den ** 2
    eps = np.sqrt(G2 * (tb0 + tb1) / np.maximum(Aup, 1e-300)) + 2.0 ** -20
    TD = (1 + eps) * Aup + (1 + 1 / eps) * G2 * (tb0 + tb1)
    s = np.maximum(0.0, m + W - np.array([hp(t) for t in a]))
    part = 2 * (b - a) * s * TD
    seg = [part[(a >= lo) & (a < hi)].sum() for lo, hi in ((0, 4), (4, 20), (20, 100), (100, 1e9))]
    T = part.sum()
    print('m=%.2f t*=%.1f cells=%d  segments %s  T=%.4f  gap=%.4f  kappa_max=%.2f'
          % (m, tstar, len(a), ' '.join('%.4f' % v for v in seg), T, m - T / (2 * np.pi),
             (2 * np.pi) ** 2 * LT * (m - T / (2 * np.pi))))
