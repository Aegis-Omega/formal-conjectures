"""Untrusted-input, validated check of a Krein LP solution for hcert (M = 3, LT = 6/5) on all t >= 0.

usage: python3 -I validate_krein_l12.py sol.npz     (sol.npz from krein_gap_l12.py)
Node values of ScertM use mpmath digamma; all other bounds are explicit (see below).

F(t) = Wt (S - m + s) + K,  S = ScertM 3 t,  K = F(H)(t/2pi) + d-terms,  s piecewise linear.
On each cell [a, b] of width w:  F >= min(F(a), F(b)) - w^2/8 * sup|F''|  with
  F'' = Wt'' (S - m + s) + 2 Wt' (S' + s') + Wt S'' + K'',
  |K''| <= max(|K''(a)|, |K''(b)|) + w * M3,  M3 = sum|a_j| 2h (u_j+h)^3 + sum_j |d_j| |(t^j phi(tL))'''|,
  |S'| <= (4/t^2 + pi/t)/2 + 2.08 (t >= 2), 10.7 (t < 2);  |S''| <= (16/t^3 + 8/t^2)/4 + 2.01 (t >= 2),
  34.4 (t < 2);  |S - m + s| <= max over the ends + w (|S'| + |s'|).
Cells failing the bound are bisected. Tail t >= tmax: as in the LP (Re psi increasing, envelopes).
Also returns a rigorous upper bound for T = 2 int s trialDist (trialDist' <= 2 sqrt(LT^4/3) < 1.67).
"""
import math
import sys

import mpmath as mp
import numpy as np

z = np.load(sys.argv[1])
m, c, s_nodes, ts = float(z["m"]), z["c"], z["s"], z["ts"]
L, h, J, TMAX = float(z["L"]), float(z["h"]), int(z["J"]), float(z["TMAX"])
uj = L + h + 2 * h * np.arange(J)
a_c, d_c = c[:J], c[J:]
L2, L3 = math.log(2), math.log(3)
P1, P2 = math.sqrt(2) * L2, 2 * L3 / math.sqrt(3)
LT = 1.2


def scert(t):
    return float(mp.re(mp.digamma(0.25 + 0.5j * t))) - math.log(math.pi) - P1 * math.cos(t * L2) - P2 * math.cos(t * L3)


def kern(t, der=0):
    """K and its derivatives (der = 0, 1, 2) at points t (numpy)."""
    t = np.asarray(t, dtype=float)
    # H part: sum a_j 2 cos(t u_j) b(t),  b(t) = 2 (1 - cos(th)) / (h t^2) = 2h sum_k (-1)^(k+1) (th)^(2k-2)/(2k)!
    bd = []
    x = t * h
    small = np.abs(x) < 0.5
    ser = [np.zeros_like(t) for _ in range(3)]
    for kk in range(1, 16):
        coef = 2 * h * (-1) ** (kk + 1) * h ** (2 * kk - 2) / math.factorial(2 * kk)
        p = 2 * kk - 2
        ser[0] += coef * t ** p
        if p >= 1:
            ser[1] += coef * p * t ** (p - 1)
        if p >= 2:
            ser[2] += coef * p * (p - 1) * t ** (p - 2)
    ts_ = np.where(small, 1.0, t)
    q, q1, q2 = 1 - np.cos(ts_ * h), h * np.sin(ts_ * h), h * h * np.cos(ts_ * h)
    cl = [(2 / h) * q / ts_ ** 2,
          (2 / h) * (q1 / ts_ ** 2 - 2 * q / ts_ ** 3),
          (2 / h) * (q2 / ts_ ** 2 - 4 * q1 / ts_ ** 3 + 6 * q / ts_ ** 4)]
    bd = [np.where(small, ser[i], cl[i]) for i in range(3)]
    ct = np.cos(np.outer(t, uj)); st = np.sin(np.outer(t, uj))
    if der == 0:
        g = ct * bd[0][:, None]
    elif der == 1:
        g = -uj * st * bd[0][:, None] + ct * bd[1][:, None]
    else:
        g = -(uj ** 2) * ct * bd[0][:, None] - 2 * uj * st * bd[1][:, None] + ct * bd[2][:, None]
    fh = 2 * (g @ a_c)
    # d-terms: sum_j d_j t^j phi_j(tL), phi = cos, sin, cos, sin, cos
    out = fh
    for j in range(5):
        f = [np.cos, np.sin][j % 2]
        fp = [lambda y: -np.sin(y), np.cos][j % 2]
        fpp = [lambda y: -np.cos(y), lambda y: -np.sin(y)][j % 2]
        y = t * L
        tj = t ** j
        if der == 0:
            v = tj * f(y)
        elif der == 1:
            v = (j * t ** (j - 1) if j else 0) * f(y) + tj * L * fp(y)
        else:
            v = ((j * (j - 1) * t ** (j - 2)) if j >= 2 else 0) * f(y) + \
                2 * (j * t ** (j - 1) if j else 0) * L * fp(y) + tj * L * L * fpp(y)
        out = out + d_c[j] * v
    return out


def m3(tb):
    """Upper bound of |K'''| on [0, tb]."""
    mh = np.sum(np.abs(a_c) * 2 * h * (uj + h) ** 3)
    md = 0.0
    for j in range(5):
        md += abs(d_c[j]) * sum(math.comb(3, i) * math.perm(j, i) * tb ** max(j - i, 0) * L ** (3 - i)
                                for i in range(0, min(j, 3) + 1))
    return mh + md


def s_at(t):
    return np.interp(t, ts, s_nodes)


def bounds_S(t):
    t = np.asarray(t)
    s1 = np.where(t >= 2, (4 / np.maximum(t, 1e-9) ** 2 + math.pi / np.maximum(t, 1e-9)) / 2 + 2.08, 10.7)
    s2 = np.where(t >= 2, (16 / np.maximum(t, 1e-9) ** 3 + 8 / np.maximum(t, 1e-9) ** 2) / 4 + 2.01, 34.4)
    return np.minimum(s1, 10.7), np.minimum(s2, 34.4)


def check():
    cells = [(ts[i], ts[i + 1]) for i in range(len(ts) - 1)]
    total_cells, worst, depth = 0, np.inf, 0
    while cells:
        a = np.array([x for x, _ in cells]); b = np.array([y for _, y in cells])
        w = b - a
        Sa = np.array([scert(t) for t in a]); Sb = np.array([scert(t) for t in b])
        sa, sb = s_at(a), s_at(b)
        sl = (s_at(b - 1e-12) - s_at(a + 1e-12)) / w
        wa, wb = (a * a + .25) ** 2, (b * b + .25) ** 2
        Fa = wa * (Sa - m + sa) + kern(a); Fb = wb * (Sb - m + sb) + kern(b)
        S1, S2 = bounds_S(a)
        absS = np.maximum(np.abs(Sa - m + sa), np.abs(Sb - m + sb)) + w * (S1 + np.abs(sl))
        Wpp = 12 * b * b + 1; Wp = 4 * b * (b * b + .25); Wb = wb
        K2 = np.maximum(np.abs(kern(a, 2)), np.abs(kern(b, 2))) + w * m3(b.max() if len(b) else 0)
        F2 = Wpp * absS + 2 * Wp * (S1 + np.abs(sl)) + Wb * S2 + K2
        lb = np.minimum(Fa, Fb) - w * w / 8 * F2
        ok = lb >= 0
        total_cells += int(ok.sum())
        if ok.any():
            worst = min(worst, float((lb[ok] / np.minimum(wa, wb)[ok]).min()))
        bad = [(x, y) for x, y, o in zip(a, b, ok) if not o]
        neg = [(x, y) for x, y, fa, fb in zip(a, b, Fa, Fb) if min(fa, fb) < 0]
        if neg:
            print("NEGATIVE node value at", neg[:3]); return False
        depth += 1
        if depth > 18:
            print("refinement depth exceeded;", len(bad), "cells left, e.g.", bad[:3]); return False
        cells = [(x, (x + y) / 2) for x, y in bad] + [((x + y) / 2, y) for x, y in bad]
        print("level %d: %d cells verified so far, %d to bisect" % (depth, total_cells, len(bad)))
    print("hcert verified on [0, %g]: %d cells, min lower bound / Wt = %.3e" % (TMAX, total_cells, worst))
    return True


def tail():
    psi_lo = float(mp.re(mp.digamma(0.25 + 0.5j * TMAX))) - math.log(math.pi) - P1 - P2
    wt0 = (TMAX ** 2 + .25) ** 2
    env = np.sum(np.abs(a_c)) * 2 * min(h, 4 / (h * TMAX ** 2)) / wt0 + \
        sum(abs(d_c[j]) * max(TMAX ** j / wt0, 1.0 if j == 4 else 0.0) for j in range(5))
    marg = psi_lo - m - env
    print("tail t >= %g: psi_lo - m - envelope = %.4f (must be >= 0)" % (TMAX, marg))
    return marg >= 0


def trace_upper():
    K = np.arange(-70, 71); W = 2 * np.pi * K / LT
    QO, _ = np.linalg.qr(np.stack([1 / (W ** 2 + 0.25), K / (W ** 2 + 0.25)], axis=1))
    tg = np.arange(0, TMAX, 0.002)
    d = tg[:, None] - W[None, :]
    small = np.abs(d) < 1e-12
    v = np.where(small, LT, (np.exp(1j * d * LT) - 1) / (1j * np.where(small, 1, d)))
    pv = v @ QO.conj()
    td = np.clip(LT - ((np.abs(v) ** 2).sum(1) - (np.abs(pv) ** 2).sum(1)) / LT, 0, None)
    td_up = np.minimum(LT, td + 1.67 * 0.002)          # sup on [t, t + 0.002]
    sv = s_at(tg)
    sv_up = np.maximum(sv, s_at(tg + 0.002))
    T_up = 2 * np.sum(sv_up * td_up) * 0.002
    print("T upper bound = %.4f ; gap m - T/(2 pi) >= %.4f" % (T_up, m - T_up / (2 * math.pi)))
    return T_up


if __name__ == "__main__":
    ok1 = tail()
    T_up = trace_upper()
    ok2 = check()
    print("RESULT:", "PASS" if ok1 and ok2 else "FAIL", "gap >= %.4f" % (m - T_up / (2 * math.pi)))
