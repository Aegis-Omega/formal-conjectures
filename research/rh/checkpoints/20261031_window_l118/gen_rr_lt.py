"""Feasibility mirror of tools/gen_rr43.py with the window, NP, eps and kappa as parameters and
synthetic tau / diagonal boxes (mpmath midpoint +- radius). Untrusted; only for choosing the
parameters of a port. Writes rr_lt_data.pkl in the format cert43.py reads.
usage: python3 gen_rr_lt.py LT NP EPS KAPPA RHO_LOW RHO_HIGH RHO_DIAG   (LT, EPS as fractions)
"""
import math
import pickle
import sys
import time
from fractions import Fraction as Fr

import mpmath as mp

t0 = time.time()
LTQ, NP, EPS, KAPPA = Fr(sys.argv[1]), int(sys.argv[2]), Fr(sys.argv[3]), int(sys.argv[4])
RL, RH, RDG = (float(x) for x in sys.argv[5:8])
R = 128
ETA = Fr(1, 1000)
TF = 13
SI = 11651972255721781414236          # round(pi^2 2^70)
piLo = Fr(314159265358979323846, 10 ** 20)
piHi = Fr(314159265358979323847, 10 ** 20)
pL, qL = LTQ.numerator, LTQ.denominator


def ediv(a, b):
    r = a % abs(b)
    return (a - r) // b


def cup(x, s):
    return -((-x.numerator * 2 ** s) // x.denominator)


# ---- synthetic boxes from the closed forms (as in kappa.py) ----------------------------------------
mp.mp.dps = 40
LT = mp.mpf(pL) / qL
assert LT < mp.log(4)
PRIMES = [(2, 2 * mp.log(2) / mp.sqrt(2)), (3, 2 * mp.log(3) / mp.sqrt(3))]
cw = lambda j: 2 * j + mp.mpf(1) / 2


def tau(k):
    w = 2 * mp.pi * k / LT
    s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2))
    s -= mp.nsum(lambda j: 2 * w * mp.exp(-cw(j) * LT) / (cw(j) ** 2 + w ** 2), [0, mp.inf])
    return mp.pi * s + mp.pi * sum(pw * mp.sin(w * mp.log(p)) for p, pw in PRIMES)


def diag(n):
    w = 2 * mp.pi * n / LT
    hp = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2)) - mp.log(mp.pi)
    dser = mp.re(mp.psi(1, mp.mpf(1) / 4 + 1j * w / 2)) / 4 - mp.nsum(
        lambda k: mp.exp(-cw(k) * LT) * mp.re(1 / (cw(k) + 1j * w) ** 2), [0, mp.inf])
    pr = sum(pw * (1 - mp.log(p) / LT) * mp.cos(w * mp.log(p)) for p, pw in PRIMES)
    return LT * hp + 2 * dser - LT * pr


P48 = 2 ** 48


def box(x, r):
    return Fr(math.floor((x - r) * P48), P48), Fr(math.ceil((x + r) * P48), P48)


tb = {k: box(tau(k), RL if k <= 70 else RH) for k in range(1, NP + 1)}
db = [box(diag(n), RDG) for n in range(71)]
tLit = [0] + [int((tb[k][0] + tb[k][1]) * P48) for k in range(1, NP + 1)]
rtLit = [0] + [int((tb[k][1] - tb[k][0]) * P48) for k in range(1, NP + 1)]
dLit = [int((db[n][0] + db[n][1]) * P48) for n in range(71)]
rdLit = [int((db[n][1] - db[n][0]) * P48) for n in range(71)]
print('-- boxes %.1fs' % (time.time() - t0), file=sys.stderr)


def tq(k):
    return tLit[k] if k >= 0 else -tLit[-k]


# f_n = -(2 pi n / LT)^2 - 1/4 = phi_n / (pL^2 2^72)
DEN = pL * pL


def phi(n):
    return -(16 * qL * qL * SI * n * n + pL * pL * 2 ** 70)


FL = list(range(-70, 71))
HL = list(range(71, NP + 1)) + [-k for k in range(71, NP + 1)]
Cq = round(Fr(2 ** 64) * LTQ * 2 ** 70 / (2 * SI))
piq = round(Fr(2 ** 64) * (piLo + piHi) / 2)
LT2 = LTQ * LTQ
LPq = cup((1 + ETA) * LT2 / (piLo * piLo), 64) + 1
T1q = cup((1 + ETA) * (1 + EPS) * LT2 / (piLo * piLo), 64) + 1
T2q = cup((1 + ETA) * (1 + 1 / EPS) * TF * TF * LT2 / (piLo * piLo), 64) + 1


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
for k in range(1, NP + 72):
    hLit.append(hLit[-1] + ediv(2 ** 128, k))


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


# ---- perturbation constants (same crude closed forms as gen_rr43.py) ---------------------------
rho = Fr(max(rtLit[1:71]), 2 ** 49)
rhoH = Fr(max(rtLit[71:]), 2 ** 49)
rhoD = Fr(max(rdLit), 2 ** 49)
tmax = Fr(max(abs(x) for x in tLit[0:71]), 2 ** 49)
tmaxH = Fr(max(abs(x) for x in tLit[71:]), 2 ** 49)
Dmax = Fr(max(abs(x) for x in dLit), 2 ** 49)
Chat = Fr(Cq, 2 ** 64)
Clo, Chi = LTQ / (2 * piHi * piHi), LTQ / (2 * piLo * piLo)
dC = max(abs(Chat - Clo), abs(Chi - Chat))
H70 = sum(Fr(1, k) for k in range(1, 71))
amax = Chi * rho + dC * tmax
ulp = Fr(1, 2 ** R)
RE = rhoD + 2 * amax * 2 * H70 + 140 * ulp
RA = Dmax + rhoD + 2 * Chi * tmax * 2 * H70 + RE
theta = Fr(1, 10 ** 19)
epsQ = RA * (2 * theta + theta ** 2) + RE
gam = Fr(1, 10 ** 15)
Delta = 2 * piHi * (RA * theta + RE) + 2 * (piHi - piLo) * RA + 2 * dC
dj = Delta * (1 + gam) + 2 * piHi * RA * gam
epsIn = 2 * (1 + 1 / ETA) * dj ** 2 / (1 - gam) ** 2 + Fr(1, 10 ** 12)
wmax = 2 * (rhoH + rho) * (1 + theta) + 2 * (tmaxH + tmax) * theta
Rrow = wmax * 141
Rcol = wmax * 2 * sum(Fr(1, k) for k in range(1, NP - 69))
LP2c = Fr(LPq, 2 ** 64)
epsOut = LP2c * (1 + 1 / ETA) * Rrow * Rcol + LP2c * 141 * 600 * ulp * 3
Gmax = Fr(2, NP - 70)
RG = 141 * Gmax
rhox = rho * (1 + theta) + tmax * theta
epsT = Fr(T1q, 2 ** 64) * (1 + 1 / ETA) * RG * rhox ** 2 + Fr(T2q, 2 ** 64) * (1 + 1 / ETA) * RG * theta ** 2 \
    + (Fr(T1q, 2 ** 64) * tmax ** 2 + Fr(T2q, 2 ** 64)) * 141 * 2000 * ulp
Kneed = KAPPA * epsQ + epsIn + epsOut + epsT
Kq = cup(Kneed, 64) + 1
print("-- rho %.2e rhoH %.2e rhoD %.2e RE %.3e epsIn %.2e epsOut %.2e epsT %.2e K' %.4e  max|tau|>70 %.2f" % (
    rho, rhoH, rhoD, RE, epsIn, epsOut, epsT, Kq / 2 ** 64, tmaxH), file=sys.stderr)


def Zt(n, m):
    z = KAPPA * Et(n, m) - ediv(LPq * Kt(n, m), 2 ** 64) - ediv(T1q * ediv(tq(n) * tq(m) * Gt(n, m), 2 ** 98), 2 ** 64) \
        - ediv(T2q * Gt(n, m), 2 ** 64)
    if n == m:
        z -= Kq * 2 ** 64
    return z


Zf = [[phi(n) * phi(m) * Zt(n, m) for m in FL] for n in FL]
w = (-1, 2, -1)
Y = [[w[0] * Zf[i][b] + w[1] * Zf[i + 1][b] + w[2] * Zf[i + 2][b] for b in range(141)] for i in range(139)]
P0 = [[w[0] * Y[i][j] + w[1] * Y[i][j + 1] + w[2] * Y[i][j + 2] for j in range(139)] for i in range(139)]
g1 = [ediv(DEN * 2 ** 172, phi(m)) for m in FL]
gs = [g1, [m * g1[m + 70] for m in FL]]
Ub, Gam = [], []
for g in gs:
    Vt = [ediv(2 * piq * sum(Et(n, m) * g[m + 70] for m in FL), 2 ** 154) for n in FL]
    U = [sum(w[s] * phi(i - 70 + s) * Vt[i + s] for s in range(3)) for i in range(139)]
    Gj = sum(x * x for x in g)
    cin = (1 + ETA) / (1 - gam) ** 2
    Gm = cup(cin * Fr(2 ** 200, Gj), 64) + 1
    Ub.append((Vt, U))
    Gam.append(Gm)
P = [[2 ** 212 * P0[i][j] - sum(Gam[k] * Ub[k][1][i] * Ub[k][1][j] for k in range(2)) for j in range(139)]
     for i in range(139)]
assert all(P[i][j] == P[j][i] for i in range(139) for j in range(i))
pickle.dump(dict(P=P, Pscale=488 + 4 * (DEN.bit_length() + 2)), open('rr43_data.pkl', 'wb'))
# smallest eigenvalue of the diagonally scaled P (same scaling as cert43.py)
n = 139
e = []
for i in range(n):
    x = Fr(P[i][i])
    assert x > 0, ('nonpositive diagonal', i)
    k = 0
    while x * Fr(4) ** k >= 2:
        k -= 1
    while x * Fr(4) ** k < Fr(1, 2):
        k += 1
    e.append(k)
mp.mp.dps = 60
M = mp.matrix(n, n)
for i in range(n):
    for j in range(n):
        M[i, j] = mp.mpf(P[i][j]) * mp.mpf(2) ** (e[i] + e[j])
ev = mp.eigsy(M, eigvals_only=True)
print('LT %s NP %d eps %s kappa %d: scaled lambda_min %s  lambda_max %s  (%.0fs)' % (
    LTQ, NP, EPS, KAPPA, mp.nstr(min(ev), 6), mp.nstr(max(ev), 6), time.time() - t0))
