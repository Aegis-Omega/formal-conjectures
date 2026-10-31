"""Float mirror of the cell bound in gen_lt.py, for fast sweeps over L, m and the grid.

Per cell [a, b]: A = (2 - 2 min cos(tL))/L * (1/(h(70h - b)) + 1/(h(70h + a))), h = 2 pi / L;
|gamma|^2 <= ((n0 + d0)^2 + (n1 + d1)^2) / Den^2 with the closed-form numerators N_sigma and the
Cauchy-Schwarz perturbation; TD = (sqrt A + sqrt B)^2, B = |gamma|^2 (tau0 + tau1);
s = m + ppw_2 + ppw_3 - h+(a). T = sum 2 (b - a) s TD over cells up to t*, where h+(t*) >= m + w23.
Untrusted numerics, no outward rounding.
usage: python3 trace_cells.py L_num L_den m [m ...]
"""
import math
import sys

import mpmath as mp

L = int(sys.argv[1]) / int(sys.argv[2])
MS = [float(x) for x in sys.argv[3:]] or [1.5]
h = 2 * math.pi / L
x, y = math.exp(-L / 2), math.exp(L / 2)
W23 = 2 * math.log(2) / math.sqrt(2) + 2 * math.log(3) / math.sqrt(3)
nG00, nG11 = 1 - x * x, y * y - 1
tb0 = (1 - x) ** 2 / L * 2 / (70 * h * h)
tb1 = (y - 1) ** 2 / L * 2 / (70 * h * h)
r00, r11, r01 = tb0, tb1, math.sqrt(tb0 * tb1)
Den = (x * x + y * y - 2 - L * L) - (nG00 * r11 + nG11 * r00 + 2 * L * r01 + r00 * r11 + r01 * r01)
Yb0, Yb1 = 2 * (x + 1), 2 * (y + 1)


def nc(u1, u2, v1, v2):
    return dict(p0=u1 * u1 + v1 * v1, p2=u2 * u2 + v2 * v2, q0=u1 * v1, q2=u2 * v2, r=u2 * v1 - u1 * v2)


NC0 = nc(((1 + L) * y - x) / 2, -(L - 1) * y - x, (y * y + (L - 1)) / 2, y * y - (1 + L))
NC1 = nc((-(L - 1) * x - y) / 2, y - (1 + L) * x, (x * x - (1 + L)) / 2, -(L - 1) - x * x)


import os
CRUDE = os.environ.get('CRUDE', '1') == '1'  # the Lipschitz enclosure of CvSTauPrimeL12V1.sinPi_bounds


def sinpi(ul, uh):  # enclosure of sin(pi u) over [ul, uh]
    if not CRUDE:
        v = [math.sin(math.pi * (ul + (uh - ul) * i / 8)) for i in range(9)]
        return min(v), max(v)
    mid = math.floor(ul + 0.5)
    tl, th = math.pi * (ul - mid), math.pi * (uh - mid)
    lo, hi = math.sin(tl) - (th - tl), math.sin(tl) + (th - tl)
    return (lo, hi) if mid % 2 == 0 else (-hi, -lo)


def cos_rng(a, b):
    return sinpi(a * L / math.pi + 0.5, b * L / math.pi + 0.5)


def sin_rng(a, b):
    return sinpi(a * L / math.pi, b * L / math.pi)


def Pmax(k, a, b):  # interval bound as in gen_lt.py: cos and sin ranges taken independently
    cl, ch = cos_rng(a, b)
    sl, sh = sin_rng(a, b)
    qs = [k['q0'] + k['q2'] * a * a, k['q0'] + k['q2'] * b * b]
    rs = [k['r'] * a, k['r'] * b]
    return (k['p0'] + k['p2'] * b * b + max(-2 * q * c for q in qs for c in (cl, ch))
            + max(2 * r * s for r in rs for s in (sl, sh)))


def hplus(t):
    return float(mp.re(mp.digamma(0.25 + 0.5j * t))) - float(mp.log(mp.pi))


def cell(a, b, m):
    cl = cos_rng(a, b)[0]
    A = (2 - 2 * cl) / L * (1 / (h * (70 * h - b)) + 1 / (h * (70 * h + a)))
    al = math.sqrt(A)
    n0, n1 = (math.sqrt(max(Pmax(k, a, b), 0)) / (a * a + 0.25) for k in (NC0, NC1))
    f0, f1 = al * math.sqrt(r00), al * math.sqrt(r11)
    d0 = nG11 * f0 + r11 * Yb0 + r11 * f0 + L * f1 + r01 * Yb1 + r01 * f1
    d1 = nG00 * f1 + r00 * Yb1 + r00 * f1 + L * f0 + r01 * Yb0 + r01 * f0
    B = ((n0 + d0) ** 2 + (n1 + d1) ** 2) / Den ** 2 * (tb0 + tb1)
    TD = (math.sqrt(A) + math.sqrt(B)) ** 2
    s = max(0.0, m + W23 - hplus(a))
    return 2 * (b - a) * s * TD


def tstar(m):
    lo, hi = 1.0, 5000.0
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if hplus(mid) >= m + W23 else (mid, hi)
    return hi


def grid(top):
    g = float(os.environ.get('GRID', '1'))  # step divisor
    spec = [(0, 4, 0.02 / g), (4, 20, 0.1 / g), (20, 100, 0.5 / g), (100, top, 1.0 / g)]
    pts = []
    for lo, hi, st in spec:
        t = lo
        while t < min(hi, top) - 1e-12:
            pts.append(t); t += st
    pts.append(top)
    return list(zip(pts[:-1], pts[1:]))


if __name__ == '__main__':
    print('L=%.4f 70h=%.1f det=%.4f Den=%.4f tau0+tau1=%.2e' % (L, 70 * h, x * x + y * y - 2 - L * L, Den, tb0 + tb1))
    for m in MS:
        ts = tstar(m)
        if ts >= 70 * h:
            print('  m=%.3f t*=%.0f beyond 70h: tail bound does not apply' % (m, ts)); continue
        cells = grid(math.ceil(ts))
        T = sum(cell(a, b, m) for a, b in cells)
        print('  m=%.3f t*=%.1f cells=%d T=%.3f gap=%.4f  max kappa=(2pi)^2 L gap=%.1f'
              % (m, ts, len(cells), T, m - T / (2 * math.pi), (2 * math.pi) ** 2 * L * (m - T / (2 * math.pi))))
