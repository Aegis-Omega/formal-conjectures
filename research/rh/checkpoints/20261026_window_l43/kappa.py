"""Untrusted float model of the row budget kappa(LT) = max B / Q_CvS for the window [0, LT].

Same model as feshbach_lean_v1/tools/hfin_tail_l12.py, with LT a parameter:
  tau_k  = pi (Im psi(1/4 + i w/2) - sum_j 2w e^{-c_j LT}/(c_j^2 + w^2)) + pi sum_p ppw_p sin(w log p),
  diag_n = LT h+(w) + 2 D(w) - LT sum_p ppw_p (1 - log p / LT) cos(w log p),   w = 2 pi n / LT,
  h+(w)  = Re psi(1/4 + i w/2) - log pi,
  D(w)   = sum_k (1 - e^{-c_k LT}) (c_k^2 - w^2) / (c_k^2 + w^2)^2,  c_k = 2k + 1/2,
  entry(n, m) = LT/(2 pi^2) (tau_n - tau_m)/(n - m) off the diagonal.
B = rows 70 < |m| <= NP plus the exact Gram tail with |tau| <= TF beyond NP (CvSGramTailV1).
usage: python3 kappa.py LT_num LT_den [NP] [TF]
With LT = 6/5 it also compares tau and diag with the certified boxes (path in argv or env FESH).
"""
import os
import re
import sys
from fractions import Fraction as F

import mpmath as mp
import numpy as np

mp.mp.dps = 30
LTq = F(int(sys.argv[1]), int(sys.argv[2]))
NP = int(sys.argv[3]) if len(sys.argv) > 3 else 150
TF = float(sys.argv[4]) if len(sys.argv) > 4 else 13.0
LT = mp.mpf(LTq.numerator) / LTq.denominator
lf = float(LT)
PRIMES = [(2, 2 * mp.log(2) / mp.sqrt(2)), (3, 2 * mp.log(3) / mp.sqrt(3))]
assert LT < mp.log(4), 'prime power 4 would enter the window'


def cw(k):
    return 2 * k + mp.mpf(1) / 2


def tau(k):
    if k == 0:
        return mp.mpf(0)
    w = 2 * mp.pi * k / LT
    s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2))
    s -= mp.nsum(lambda j: 2 * w * mp.exp(-cw(j) * LT) / (cw(j) ** 2 + w ** 2), [0, mp.inf])
    return mp.pi * s + mp.pi * sum(pw * mp.sin(w * mp.log(p)) for p, pw in PRIMES)


def diag(n):
    w = 2 * mp.pi * n / LT
    hp = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2)) - mp.log(mp.pi)
    # sum_k Re (c_k + i w)^-2 = Re psi'(1/4 + i w/2) / 4; the damped part converges fast
    dser = mp.re(mp.psi(1, mp.mpf(1) / 4 + 1j * w / 2)) / 4 - mp.nsum(
        lambda k: mp.exp(-cw(k) * LT) * mp.re(1 / (cw(k) + 1j * w) ** 2), [0, mp.inf])
    pr = sum(pw * (1 - mp.log(p) / LT) * mp.cos(w * mp.log(p)) for p, pw in PRIMES)
    return LT * hp + 2 * dser - LT * pr


def grab(path, name):
    src = open(path).read()
    body = re.search(r"def " + name + r" : List ℚ := \[(.*?)\]", src, re.S).group(1)
    return [F(int(a), int(b)) for a, b in re.findall(r"(-?\d+) / (\d+)", body)]


def main():
    top = NP + 71
    t = {k: float(tau(k)) for k in range(top)}
    t.update({-k: -t[k] for k in range(1, top)})
    dg = [float(diag(n)) for n in range(71)]
    fesh = os.environ.get('FESH')
    if LTq == F(6, 5) and fesh:
        tlo, thi = grab(f'{fesh}/CvSTauPrimeL12V1.lean', 'tauFLo'), grab(f'{fesh}/CvSTauPrimeL12V1.lean', 'tauFHi')
        dlo, dhi = grab(f'{fesh}/CvSDiagL12V1.lean', 'diagLo'), grab(f'{fesh}/CvSDiagL12V1.lean', 'diagHi')
        print('tau misses', [k for k in range(1, 71) if not (float(tlo[k - 1]) - 1e-9 <= t[k] <= float(thi[k - 1]) + 1e-9)])
        print('diag max |model - mid|', max(abs(dg[n] - float((dlo[n] + dhi[n]) / 2)) for n in range(71)))
    print('LT = %s  max|tau_k| for 70<k<=%d: %.2f' % (LTq, top - 1, max(abs(t[k]) for k in range(71, top))))

    def entry(n, m):
        return dg[abs(n)] if n == m else lf / (2 * np.pi ** 2) * (t[n] - t[m]) / (n - m)

    fr = np.arange(-70, 71)
    a = np.zeros((141, 139))
    for i in range(139):
        for k, b in ((i - 70, -0.25), (i - 69, 0.5), (i - 68, -0.25)):
            wk = 2 * np.pi * k / lf
            a[k + 70, i] = b * (-(wk * wk) - 0.25)
    g = np.array([[entry(x, y) for y in fr] for x in fr])
    q = a.T @ g @ a
    w, v = np.linalg.eigh((q + q.T) / 2)
    print('Q_CvS eig min %.3e max %.3e' % (w[0], w[-1]))
    if w[0] <= 0:
        print('Q_CvS NOT positive definite'); return
    qih = v @ np.diag(w ** -0.5) @ v.T
    x_in = 2 * np.pi * (np.eye(141) - a @ np.linalg.pinv(a)) @ g @ a
    ms = [m for m in range(-NP, NP + 1) if abs(m) > 70]
    xo = np.array([[2 * np.pi * entry(n, m) for n in fr] for m in ms]) @ a
    br = xo.T @ xo + x_in.T @ x_in
    gm = np.zeros((141, 141))
    for i, n in enumerate(fr):
        for j, n2 in enumerate(fr):
            s = mp.mpf(0)
            for sg in (1, -1):
                x, y = NP + 1 - sg * int(n), NP + 1 - sg * int(n2)
                s += mp.psi(1, x) if x == y else (mp.digamma(x) - mp.digamma(y)) / (x - y)
            gm[i, j] = float(s)
    dm = np.diag([t[int(n)] for n in fr])
    scale = (2 * np.pi) ** 2 * lf
    rel = lambda bm: np.linalg.eigvalsh(qih @ bm @ qih)[-1]
    print('rows only kappa %.2f' % rel(br))
    for e in (0.5, 0.7, 1, 1.4, 2):
        k = rel(br + (lf / np.pi) ** 2 * a.T @ ((1 + e) * dm @ gm @ dm + (1 + 1 / e) * TF * TF * gm) @ a)
        print('NP=%d TF=%.1f eps=%g kappa %.2f -> gap needed %.4f' % (NP, TF, e, k, k / scale))


if __name__ == '__main__':
    main()
