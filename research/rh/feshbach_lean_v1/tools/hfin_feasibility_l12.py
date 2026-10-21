"""Untrusted float model of the L = 6/5 cross-row budget (`hfin`). Numerics only, no certificate.

usage: python3 -I hfin_feasibility_l12.py <feshbach_lean_v1 dir> [NP ...]

tau_k = pi (Im psi(1/4 + i w/2) - sum_j 2w e^{-c_j L} / (c_j^2 + w^2))
        + pi (ppw_1 sin(2 pi k log2 / L) + ppw_2 sin(2 pi k log3 / L)),   w = 2 pi k / L,
and is checked against the certified boxes tauFLo/tauFHi (k = 1..70). Diagonal entries are the
midpoints of diagLo/diagHi. Off the diagonal, cvsEntry n m = L/(2 pi^2) (tau_n - tau_m)/(n - m).
The script prints the best possible row budget relative to |c|^2 and relative to Q_CvS, and the
Schur gap m - T/(2 pi) that each one requires. Rows |m| > NP (rowTail) are not included.
"""
import re
import sys
from fractions import Fraction as F

import mpmath as mp
import numpy as np

mp.mp.dps = 30
L = mp.mpf(6) / 5
LOG2, LOG3 = mp.log(2), mp.log(3)
PPW1, PPW2 = 2 * LOG2 / mp.sqrt(2), 2 * LOG3 / mp.sqrt(3)


def grab(d, path, name):
    src = open(f"{d}/{path}").read()
    body = re.search(r"def " + name + r" : List ℚ := \[(.*?)\]", src, re.S).group(1)
    return [F(int(a), int(b)) for a, b in re.findall(r"(-?\d+) / (\d+)", body)]


def tau(k):
    if k == 0:
        return mp.mpf(0)
    w = 2 * mp.pi * k / L
    s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2))
    s -= mp.nsum(lambda j: 2 * w * mp.exp(-(2 * j + mp.mpf(1) / 2) * L) /
                 ((2 * j + mp.mpf(1) / 2) ** 2 + w ** 2), [0, mp.inf])
    return mp.pi * s + mp.pi * (PPW1 * mp.sin(2 * mp.pi * k * LOG2 / L) +
                                PPW2 * mp.sin(2 * mp.pi * k * LOG3 / L))


def main():
    d = sys.argv[1]
    nps = [int(x) for x in sys.argv[2:]] or [100, 400, 2000]
    tlo, thi = grab(d, "CvSTauPrimeL12V1.lean", "tauFLo"), grab(d, "CvSTauPrimeL12V1.lean", "tauFHi")
    misses = [k for k in range(1, 71) if not (tlo[k - 1] <= F(str(tau(k))) <= thi[k - 1])]
    print("tau model vs certified boxes k = 1..70, misses:", misses)
    dlo, dhi = grab(d, "CvSDiagL12V1.lean", "diagLo"), grab(d, "CvSDiagL12V1.lean", "diagHi")
    diag = [float((a + b) / 2) for a, b in zip(dlo, dhi)]

    top = max(nps) + 71
    t = {k: float(tau(k)) for k in range(top)}
    t.update({-k: -t[k] for k in range(1, top)})
    lf = float(L)

    def entry(n, m):
        return diag[abs(n)] if n == m else lf / (2 * np.pi ** 2) * (t[n] - t[m]) / (n - m)

    fr = list(range(-70, 71))
    a = np.zeros((141, 139))
    for i in range(139):
        for k, b in ((i - 70, -0.25), (i - 69, 0.5), (i - 68, -0.25)):
            wk = 2 * np.pi * k / lf
            a[k + 70, i] = b * (-(wk * wk) - 0.25)
    g = np.array([[entry(x, y) for y in fr] for x in fr])
    q = a.T @ g @ a
    q = (q + q.T) / 2
    w, v = np.linalg.eigh(q)
    qih = v @ np.diag(w ** -0.5) @ v.T
    print("Q_CvS on atoms: eigenvalues %.3e .. %.3e, condition %.2e" % (w[0], w[-1], w[-1] / w[0]))
    x_in = 2 * np.pi * (np.eye(141) - a @ np.linalg.pinv(a)) @ g @ a
    scale = (2 * np.pi) ** 2 * lf
    for np_ in nps:
        rows = [m for m in range(-np_, np_ + 1) if abs(m) > 70]
        x_out = np.array([[2 * np.pi * entry(n, m) for n in fr] for m in rows]) @ a
        bmat = x_out.T @ x_out + x_in.T @ x_in
        beta = np.linalg.eigvalsh(bmat)[-1]
        kappa = np.linalg.eigvalsh(qih @ bmat @ qih)[-1]
        print("NP=%d  beta/|c|^2 = %.3e (gap >= %.2e with delta = %.3e)   kappa = max B/Q = %.4f "
              "(gap >= %.4f)" % (np_, beta, beta / (scale * w[0]), w[0], kappa, kappa / scale))


if __name__ == "__main__":
    main()
