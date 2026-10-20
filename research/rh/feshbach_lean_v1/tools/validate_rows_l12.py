"""Validated check of the relative row budget kappa* Q_CvS - B >= 0 at L = 6/5 (existing Lean rowTail).

B = residual Gram of the finite rows |m| <= NP (lam = rounded projection, any lam is admissible)
  + quadratic majorant of rowTail M (6/5) F a K (tauBound 3) 70 NP:
    (x + T y)^2 <= (1+eps) x^2 + (1+1/eps) T^2 y^2,  (sum |a_n|)^2 <= 141 sum |a_n|^2.
Inputs: tau_k from the digamma closed form at 40 digits (k <= 70 also checked against the certified
boxes), diagonal entries = midpoints of the certified diagLo/diagHi. All matrix products are exact
integer arithmetic at scale 2^100; the final LDL^T runs in mpmath at 80 digits.
usage: python3 -I validate_rows_l12.py <feshbach_lean_v1 dir> NP K eps kappa [dG]
With dG > 0 the check is robust to any error of operator norm <= dG in the low-block entries and in
the outside-row entries (both come from the tau and diagonal boxes): kappa A^T dG A >= -kappa dG A^T A,
and both residual Grams are inflated by (1 + 1/100) plus (1 + 100) (2 pi)^2 dG^2 A^T A each.
The certified boxes give |dG| <= 2 lambda_max(rho) = 2.3e-7 inside and <= 2.6e-7 (Frobenius) outside.
e.g. python3 -I validate_rows_l12.py . 2000 2 3 50 0.0000003
"""
import re
import sys
from fractions import Fraction as Fr

import mpmath as mp
import numpy as np

D, NP, KK, EPS, KAPPA = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), Fr(sys.argv[4]), Fr(sys.argv[5])
# robustness: entries of the low block known only up to |dG| <= DG (operator norm); 0 = midpoints
DG = Fr(sys.argv[6]) if len(sys.argv) > 6 else Fr(0)
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
    top = NP + 71
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
    # tail majorant (exact rationals, constants rounded up)
    up = lambda x: Fr(int(mp.ceil(x * 2 ** 120)), 2 ** 120)
    Tb = 4 * mp.pi * (1 + mp.pi / 4) + mp.pi * (2 * mp.log(2) / mp.sqrt(2) + 2 * mp.log(3) / mp.sqrt(3))
    Tb2 = up(Tb ** 2)
    LP2 = up((L / mp.pi) ** 2)
    Ar = [[Fr(int(A[n, i]), SC) for i in range(139)] for n in range(141)]
    taur = [Fr(toint(t[n]), SC) for n in fr]
    Bt = [[Fr(0)] * 139 for _ in range(139)]
    for j in range(KK):
        p = [sum(taur[n] * Fr(fr[n]) ** j * Ar[n][i] for n in range(141)) for i in range(139)]
        q = [sum(Fr(fr[n]) ** j * Ar[n][i] for n in range(141)) for i in range(139)]
        cp = LP2 * 2 * KK * (1 + EPS) * 2 / Fr(NP) ** (2 * j + 1)
        cq = LP2 * 2 * KK * (1 + 1 / EPS) * Tb2 * 2 / Fr(NP) ** (2 * j + 1)
        for i in range(139):
            for i2 in range(139):
                Bt[i][i2] += cp * p[i] * p[i2] + cq * q[i] * q[i2]
    AtA = [[sum(Ar[n][i] * Ar[n][i2] for n in range(141)) for i2 in range(139)] for i in range(139)]
    cr = LP2 * 2 * 4 * Tb2 * Fr(70) ** (2 * KK) * 141 * 2 / (Fr(NP) ** (2 * KK) * (NP - 70))
    print("tail majorant built")
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
    print("RESULT: PASS  kappa* = %s  robust |dG| <= %s  ->  needs Schur gap >= %s"
          % (KAPPA, float(DG), mp.nstr(mp.mpf(KAPPA.numerator) / KAPPA.denominator / ((2 * mp.pi) ** 2 * L), 6)))


if __name__ == "__main__":
    main()
