"""Validated check of kappa* Q_CvS - B >= 0 at L = 6/5 with the Lean Gram row tail
(CvSWindowGramL12V1.window_L12_gram).

B = residual Gram of the finite rows |m| <= NP (lam = rounded projection, any lam is admissible)
  + the Lean `gramTail M (6/5) F a 13 eps NP` as a matrix in c:
    (L/pi)^2 ((1 + eps) (D A)^T G (D A) + (1 + 1/eps) 13^2 A^T G A),
  G = CvSGramTailV1.gramUp NP (exact rationals from harmonic numbers), D = diag(tau_n), |n| <= 70.
Inputs: tau_k from the digamma closed form at 40 digits (k <= 70 also checked against the certified
boxes), diagonal entries = midpoints of the certified diagLo/diagHi. All matrix products are exact
integer arithmetic at scale 2^100; the final LDL^T runs in mpmath at 80 digits.
usage: python3 -I validate_rows_gram_l12.py <feshbach_lean_v1 dir> NP eps kappa [dG]
With dG > 0 the check is robust to any error of operator norm <= dG in the low-block entries and in
the outside-row entries (tau and diagonal boxes, including the boxes for 70 < |m| <= NP that are not
yet certified in Lean), and to the certified tau box radii in D (inflated by 1 + 1/100 and
(1 + 100) |G|_1 rho^2 A^T A, |G|_1 the max row sum of |G|).
e.g. python3 -I validate_rows_gram_l12.py . 150 1 40 0.0000003
"""
import re
import sys
from fractions import Fraction as Fr

import mpmath as mp
import numpy as np

D, NP, EPS, KAPPA = sys.argv[1], int(sys.argv[2]), Fr(sys.argv[3]), Fr(sys.argv[4])
# robustness: entries of the low block known only up to |dG| <= DG (operator norm); 0 = midpoints
DG = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(0)
TF = Fr(13)
ETA = Fr(1, 100)
mp.mp.dps = 40
L = mp.mpf(6) / 5
SC = 2 ** 100


def grab(path, name):
    src = open(f"{D}/{path}").read()
    body = re.search(r"def " + name + r" : List ℚ := \[(.*?)\]", src, re.S).group(1)
    return [Fr(int(a), int(b)) for a, b in re.findall(r"(-?\d+) / (\d+)", body)]


def tau(k):
    if k == 0:
        return mp.mpf(0)
    w = 2 * mp.pi * k / L
    s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2))
    s -= mp.nsum(lambda j: 2 * w * mp.exp(-(2 * j + mp.mpf(1) / 2) * L) /
                 ((2 * j + mp.mpf(1) / 2) ** 2 + w ** 2), [0, mp.inf])
    return mp.pi * s + mp.pi * (2 * mp.log(2) / mp.sqrt(2) * mp.sin(2 * mp.pi * k * mp.log(2) / L) +
                                2 * mp.log(3) / mp.sqrt(3) * mp.sin(2 * mp.pi * k * mp.log(3) / L))


def toint(x, scale=SC):
    return int(mp.nint(x * scale))


def main():
    tlo, thi = grab("CvSTauPrimeL12V1.lean", "tauFLo"), grab("CvSTauPrimeL12V1.lean", "tauFHi")
    top = NP + 1
    t = {k: tau(k) for k in range(top)}
    miss = [k for k in range(1, 71) if not (tlo[k - 1] <= Fr(mp.nstr(t[k], 35)) <= thi[k - 1])]
    print("tau vs certified boxes (k <= 70): misses", miss)
    t.update({-k: -t[k] for k in range(1, top)})
    dlo, dhi = grab("CvSDiagL12V1.lean", "diagLo"), grab("CvSDiagL12V1.lean", "diagHi")
    diag = [(a + b) / 2 for a, b in zip(dlo, dhi)]
    cE = L / (2 * mp.pi ** 2)

    def entry(n, m):
        if n == m:
            return mp.mpf(diag[abs(n)].numerator) / diag[abs(n)].denominator
        return cE * (t[n] - t[m]) / (n - m)

    fr = list(range(-70, 71))
    # A (141 x 139), exact up to the rounding of pi^2 at scale SC
    A = np.zeros((141, 139), dtype=object)
    for i in range(139):
        for k, b in ((i - 70, mp.mpf(-1) / 4), (i - 69, mp.mpf(1) / 2), (i - 68, mp.mpf(-1) / 4)):
            wk = 2 * mp.pi * k / L
            A[k + 70, i] = toint(b * (-(wk * wk) - mp.mpf(1) / 4))
    G = np.array([[toint(entry(a, b)) for b in fr] for a in fr], dtype=object)       # scale SC
    G2 = np.array([[toint(2 * mp.pi * entry(a, b)) for b in fr] for a in fr], dtype=object)
    Q = A.T.dot(G).dot(A)                                                            # SC^3
    # inside rows: R = (2 pi G) A - A Lam, Lam = rounded least squares solution (scale SC)
    Af = np.array(A, dtype=float) / SC
    G2f = np.array(G2, dtype=float) / SC
    Lam = np.linalg.lstsq(Af, G2f @ Af, rcond=None)[0]
    LamI = np.array([[int(round(x * SC)) for x in row] for row in Lam], dtype=object)
    Rin = G2.dot(A) - A.dot(LamI)                                                    # SC^2
    Bin = Rin.T.dot(Rin)                                                             # SC^4
    rows = [mm for mm in range(-NP, NP + 1) if abs(mm) > 70]
    E2 = np.array([[toint(2 * mp.pi * entry(n, mm)) for n in fr] for mm in rows], dtype=object)
    Xo = E2.dot(A)                                                                   # SC^2
    Bout = Xo.T.dot(Xo)                                                              # SC^4
    print("rows: %d outside, built B_rows" % len(rows))
    # Gram tail (exact rationals): G = gramUp NP from harmonic numbers
    up = lambda x: Fr(int(mp.ceil(x * 2 ** 120)), 2 ** 120)
    LP2 = up((L / mp.pi) ** 2)
    Hn = [Fr(0)]
    for j in range(1, NP + 72):
        Hn.append(Hn[-1] + Fr(1, j))
    def gup(n, n2):
        if n == n2:
            return 1 / (NP - n + Fr(1, 2)) + 1 / (NP + n + Fr(1, 2))
        return (Hn[NP - n2] - Hn[NP - n] + Hn[NP + n] - Hn[NP + n2]) / (n - n2)
    Gq = [[gup(a, b) for b in fr] for a in fr]
    g1 = max(sum(abs(x) for x in row) for row in Gq)
    Ar = [[Fr(int(A[n, i]), SC) for i in range(139)] for n in range(141)]
    taur = [Fr(toint(t[n]), SC) for n in fr]
    rho = max(max(abs(hi - lo) / 2 + abs((hi + lo) / 2 - taur[70 + k]) for k, (lo, hi) in
                  enumerate(zip(tlo, thi), start=1)), Fr(0))
    DA = [[taur[n] * Ar[n][i] for i in range(139)] for n in range(141)]
    def congr(X):
        GX = [[sum(Gq[n][n2] * X[n2][i] for n2 in range(141)) for i in range(139)] for n in range(141)]
        return [[sum(X[n][i] * GX[n][i2] for n in range(141)) for i2 in range(139)] for i in range(139)]
    TDA, TA = congr(DA), congr(Ar)
    AtA = [[sum(Ar[n][i] * Ar[n][i2] for n in range(141)) for i2 in range(139)] for i in range(139)]
    # D known up to rho entrywise: (1 + eta) G(Dv) + (1 + 1/eta) |G|_1 rho^2 |Av|^2
    cr = LP2 * (1 + EPS) * (1 + 1 / ETA) * g1 * rho * rho if DG else Fr(0)
    infl = (1 + ETA) if DG else Fr(1)
    Bt = [[infl * LP2 * (1 + EPS) * TDA[i][i2] + LP2 * (1 + 1 / EPS) * TF * TF * TA[i][i2]
           for i2 in range(139)] for i in range(139)]
    print("Gram tail built: |G|_1 = %.4e, tau box radius rho <= %.3e" % (float(g1), float(rho)))
    # M = kappa Q - B  (as mpmath at 80 digits)
    mp.mp.dps = 80
    S4 = mp.mpf(SC) ** 4
    M = mp.matrix(139, 139)
    for i in range(139):
        for i2 in range(139):
            v = mp.mpf(int(KAPPA.numerator)) / KAPPA.denominator * mp.mpf(int(Q[i, i2])) * SC / S4
            v -= (1 + (mp.mpf(1) / 100 if DG else 0)) * mp.mpf(int(Bout[i, i2]) + int(Bin[i, i2])) / S4
            # two perturbed residuals (inside rows via dG, outside rows via dE with |dE| <= DG):
            # (X + dX)^T (X + dX) <= (1 + eta) X^T X + (1 + 1/eta) (2 pi)^2 DG^2 A^T A
            rob = (KAPPA * DG + 2 * (1 + 1 / ETA) * 4 * Fr(314159265358979323847, 10 ** 20) ** 2 * DG * DG) if DG else Fr(0)
            bt = Bt[i][i2] + (cr + rob) * AtA[i][i2]
            v -= mp.mpf(bt.numerator) / bt.denominator
            M[i, i2] = v
    # LDL^T
    piv = []
    Mw = M.copy()
    for k in range(139):
        dk = Mw[k, k]
        piv.append(dk)
        if dk <= 0:
            print("pivot %d <= 0: %s" % (k, mp.nstr(dk, 10)))
            print("RESULT: FAIL")
            return
        for i in range(k + 1, 139):
            f = Mw[i, k] / dk
            if f != 0:
                for i2 in range(k + 1, i + 1):
                    Mw[i, i2] -= f * Mw[i2, k]
        for i in range(k + 1, 139):
            Mw[k, i] = Mw[i, k]
    print("all 139 LDL pivots > 0; min pivot %s, max pivot %s" % (mp.nstr(min(piv), 6), mp.nstr(max(piv), 6)))
    print("RESULT: PASS  NP = %d  eps = %s  kappa* = %s  robust |dG| <= %s  ->  needs Schur gap >= %s"
          % (NP, EPS, KAPPA, float(DG), mp.nstr(mp.mpf(KAPPA.numerator) / KAPPA.denominator / ((2 * mp.pi) ** 2 * L), 6)))


if __name__ == "__main__":
    main()
