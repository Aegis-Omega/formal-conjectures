"""Untrusted generator for the L = 4/3 relative row certificate (integer mirror of the Lean defs).

All quantities are integers at fixed scales, combined with Euclidean division `ediv` exactly as
Lean's `Int./`. The kernel recomputes everything except the packed factor `certL`.

Scales: tau, D at 2^-49; tables at 2^-R (R = 128); f_n = phi_n / 2^72; P at 2^-488.
usage: python3 gen_rr43.py   (writes rr43_data.pkl)
"""
import math
import pickle
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import boxes43  # noqa: E402

t0 = time.time()
R = 128
NP = 200
ETA = Fr(1, 1000)
EPS = Fr(7, 10)
SI = 11651972255721781414236          # round(pi^2 2^70)
piLo = Fr(314159265358979323846, 10 ** 20)
piHi = Fr(314159265358979323847, 10 ** 20)


def ediv(a, b):
    """Lean `Int./` (Euclidean): remainder in [0, |b|)."""
    r = a % abs(b)
    return (a - r) // b


def cup(x, s):  # ceil(x 2^s) for a Fraction x
    return -((-x.numerator * 2 ** s) // x.denominator)


tau, diag = boxes43.load()
P48 = 2 ** 48
tLit = [0] + [int((tau[k][0] + tau[k][1]) * P48) for k in range(1, 201)]
rtLit = [0] + [int((tau[k][1] - tau[k][0]) * P48) for k in range(1, 201)]
dLit = [int((diag[n][0] + diag[n][1]) * P48) for n in range(71)]
rdLit = [int((diag[n][1] - diag[n][0]) * P48) for n in range(71)]
for k in range(1, 201):
    assert Fr(tLit[k]) == (tau[k][0] + tau[k][1]) * P48 and Fr(rtLit[k]) == (tau[k][1] - tau[k][0]) * P48
for n in range(71):
    assert Fr(dLit[n]) == (diag[n][0] + diag[n][1]) * P48


def tq(k):
    return tLit[k] if k >= 0 else -tLit[-k]


def phi(n):
    return -(9 * SI * n * n + 2 ** 70)


FL = list(range(-70, 71))
HL = list(range(71, 201)) + [-k for k in range(71, 201)]
# constants (dyadic, 2^-64)
Cq = round(Fr(2 ** 64) * 2 * 2 ** 70 / (3 * SI))
piq = round(Fr(2 ** 64) * (piLo + piHi) / 2)
LPq = cup((1 + ETA) * Fr(16, 9) / (piLo * piLo), 64) + 1
T1q = cup((1 + EPS) * Fr(16, 9) / (piLo * piLo), 64) + 1
T2q = cup((1 + 1 / EPS) * 169 * Fr(16, 9) / (piLo * piLo), 64) + 1


def Et(n, m):
    if n == m:
        return dLit[abs(n)] * 2 ** 79
    if m > n:
        n, m = m, n
    return ediv(Cq * (tq(n) - tq(m)) * 2 ** 15, n - m)


def pw(j, m):
    return [2 ** 128, tq(m) * 2 ** 79, tq(m) * tq(m) * 2 ** 30][j]


S = [[sum(ediv(pw(j, m), m - n) for m in HL) for n in FL] for j in range(3)]
T = [[sum(ediv(pw(j, m), (m - n) * (m - n)) for m in HL) for n in FL] for j in range(3)]
hLit = [0]
for k in range(1, 272):
    hLit.append(hLit[-1] + ediv(2 ** 128, k))
print('-- tables %.1fs' % (time.time() - t0), file=sys.stderr)


def Kj(j, n, m):
    if n == m:
        return T[j][n + 70]
    if m > n:
        n, m = m, n
    return ediv(S[j][n + 70] - S[j][m + 70], n - m)


def Kt(n, m):
    return Kj(2, n, m) - ediv((tq(n) + tq(m)) * Kj(1, n, m), 2 ** 49) + ediv(tq(n) * tq(m) * Kj(0, n, m), 2 ** 98)


def Gt(n, m):
    if n == m:
        return ediv(2 ** 129, 2 * NP - 2 * n + 1) + ediv(2 ** 129, 2 * NP + 2 * n + 1)
    if m > n:
        n, m = m, n
    return ediv(hLit[NP - m] - hLit[NP - n] + hLit[NP + n] - hLit[NP + m], n - m)


def Zt(n, m, Kq):
    z = 52 * Et(n, m) - ediv(LPq * Kt(n, m), 2 ** 64) - ediv(T1q * ediv(tq(n) * tq(m) * Gt(n, m), 2 ** 98), 2 ** 64) \
        - ediv(T2q * Gt(n, m), 2 ** 64)
    if n == m:
        z -= Kq * 2 ** 64
    return z


# ---- perturbation constants (closed forms of kernel-checked maxima) -------------------------------
rho = Fr(max(rtLit[1:71]), 2 ** 49)            # tau radius, |n| <= 70
rhoH = Fr(max(rtLit[71:201]), 2 ** 49)         # tau radius, 70 < |m| <= 200
rhoD = Fr(max(rdLit), 2 ** 49)
tmax = Fr(max(abs(x) for x in tLit[0:71]), 2 ** 49)
tmaxH = Fr(max(abs(x) for x in tLit[71:201]), 2 ** 49)
Dmax = Fr(max(abs(x) for x in dLit), 2 ** 49)
Chat = Fr(Cq, 2 ** 64)
Clo, Chi = Fr(2) / (3 * piHi * piHi), Fr(2) / (3 * piLo * piLo)

dC = max(abs(Chat - Clo), abs(Chi - Chat))
H70 = sum(Fr(1, k) for k in range(1, 71))
H140 = sum(Fr(1, k) for k in range(1, 141))
amax = Chi * rho + dC * tmax
ulp = Fr(1, 2 ** R)
RE = rhoD + 2 * amax * 2 * H70 + 140 * ulp                       # rows of |E - Et|
RA = Dmax + rhoD + 2 * Chi * tmax * 2 * H70 + RE                 # rows of |E| (crude)
theta = Fr(1, 10 ** 19)                                           # |f/fh - 1|, SI rounding
assert Fr(2 ** 70) * abs(Fr(SI, 2 ** 70) - piLo * piLo) <= 2 ** 7  # sanity (pi^2 vs SI)
epsQ = RA * (2 * theta + theta ** 2) + RE
# B_in (dyadic g-vectors, Vt rounded at 2^-138)
gam = Fr(1, 10 ** 15)
Delta = 2 * piHi * (RA * theta + RE) + 2 * (piHi - piLo) * RA + 2 * dC  # crude
dj = Delta * (1 + gam) + 2 * piHi * RA * gam
epsIn = 2 * (1 + 1 / ETA) * (dj + Fr(12, 2 ** 138) * 0) ** 2 / (1 - gam) ** 2 + Fr(1, 10 ** 12)
# B_out (crude Schur: rows sum over n in F, columns over m in H)
wmax = 2 * (rhoH + rho) * (1 + theta) + 2 * (tmaxH + tmax) * theta
Rrow = wmax * 141
Rcol = wmax * 2 * sum(Fr(1, k) for k in range(1, 131))
LP2c = Fr(LPq, 2 ** 64)
epsOut = LP2c * (1 + 1 / ETA) * Rrow * Rcol + LP2c * 141 * 600 * ulp * 3
# tail with the PSD (1+eta) split: crude |G| <= 2/130 entries
Gmax = Fr(2, 130)
RG = 141 * Gmax
rhox = rho * (1 + theta) + tmax * theta
epsT = Fr(T1q, 2 ** 64) * (1 + 1 / ETA) * RG * rhox ** 2 + Fr(T2q, 2 ** 64) * (1 + 1 / ETA) * RG * theta ** 2 \
    + (Fr(T1q, 2 ** 64) * tmax ** 2 + Fr(T2q, 2 ** 64)) * 141 * 2000 * ulp
Kneed = 52 * epsQ + epsIn + epsOut + epsT
Kq = cup(Kneed, 64) + 1
print('-- RE %.4e epsQ %.4e epsIn %.3e epsOut %.3e epsT %.3e K\' %.5e' % (
    RE, epsQ, epsIn, epsOut, epsT, Kq / 2 ** 64), file=sys.stderr)
# NOTE: the tail split inflates T1q, T2q by (1 + eta): T1q, T2q above are without it; use inflated
T1q = cup((1 + ETA) * (1 + EPS) * Fr(16, 9) / (piLo * piLo), 64) + 1
T2q = cup((1 + ETA) * (1 + 1 / EPS) * 169 * Fr(16, 9) / (piLo * piLo), 64) + 1
# ---- Z rows, Zf, P0 -------------------------------------------------------------------------------
Zf = [[phi(n) * phi(m) * Zt(n, m, Kq) for m in FL] for n in FL]
print('-- Z %.1fs' % (time.time() - t0), file=sys.stderr)
w = (-1, 2, -1)
Y = [[w[0] * Zf[i][b] + w[1] * Zf[i + 1][b] + w[2] * Zf[i + 2][b] for b in range(141)] for i in range(139)]
P0 = [[w[0] * Y[i][j] + w[1] * Y[i][j + 1] + w[2] * Y[i][j + 2] for j in range(139)] for i in range(139)]
# ---- rank two ------------------------------------------------------------------------------------
g1 = [ediv(2 ** 172, phi(m)) for m in FL]
gs = [g1, [m * g1[m + 70] for m in FL]]
Ub, Gam = [], []
for g in gs:
    Vt = [ediv(2 * piq * sum(Et(n, m) * g[m + 70] for m in FL), 2 ** 154) for n in FL]
    U = [sum(w[s] * phi(i - 70 + s) * Vt[i + s] for s in range(3)) for i in range(139)]
    Gj = sum(x * x for x in g)                                   # 2^-200
    cin = (1 + ETA) / (1 - gam) ** 2
    Gm = cup(cin * Fr(2 ** 200, Gj), 64) + 1
    Ub.append((Vt, U))
    Gam.append(Gm)
P = [[2 ** 212 * P0[i][j] - sum(Gam[k] * Ub[k][1][i] * Ub[k][1][j] for k in range(2)) for j in range(139)]
     for i in range(139)]
assert all(P[i][j] == P[j][i] for i in range(139) for j in range(i))
print('-- P %.1fs, max bits %d' % (time.time() - t0, max(abs(x).bit_length() for r in P for x in r)), file=sys.stderr)
pickle.dump(dict(R=R, tLit=tLit, rtLit=rtLit, dLit=dLit, rdLit=rdLit, S=S, T=T, hLit=hLit, g1=g1,
                 Vt=[u[0] for u in Ub], Gam=Gam, Cq=Cq, piq=piq, LPq=LPq, T1q=T1q, T2q=T2q, Kq=Kq,
                 P=P, Pscale=488), open('rr43_data.pkl', 'wb'))
print('-- saved %.1fs' % (time.time() - t0), file=sys.stderr)
