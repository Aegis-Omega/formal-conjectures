"""Untrusted float model of the window certificate at window LT with 2K-1 atoms (frequencies |k| <= K).
Row side: kappa = max B / Q_CvS (as kappa.py, K a parameter, atom columns scaled to unit norm).
Trace side: T(m) = int s(t) dist^2(e_t, V) dt, s = max(0, m + W - h+(t)), W = worst-case prime sum,
V = atoms + exp(+-x/2).  Feasible when  m - T/(2 pi)  >=  kappa / ((2 pi)^2 LT).
usage: feas.py LT K NP TF
"""
import sys
from fractions import Fraction as F
import mpmath as mp
import numpy as np

LTq, K, NP, TF = F(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
mp.mp.dps = 30
LT = mp.mpf(LTq.numerator) / LTq.denominator
lf = float(LT)


def mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            q = n
            while q % p == 0:
                q //= p
            return mp.log(p) if q == 1 else mp.mpf(0)
    return mp.mpf(0)


PRIMES = [(n, 2 * mangoldt(n) / mp.sqrt(n)) for n in range(2, int(mp.floor(mp.exp(LT))) + 1) if mangoldt(n) > 0]
W = float(sum(pw for _, pw in PRIMES))
cw = lambda j: 2 * j + mp.mpf(1) / 2


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
    dser = mp.re(mp.psi(1, mp.mpf(1) / 4 + 1j * w / 2)) / 4 - mp.nsum(
        lambda k: mp.exp(-cw(k) * LT) * mp.re(1 / (cw(k) + 1j * w) ** 2), [0, mp.inf])
    pr = sum(pw * (1 - mp.log(p) / LT) * mp.cos(w * mp.log(p)) for p, pw in PRIMES)
    return LT * hp + 2 * dser - LT * pr


top = NP + K + 2
tv = np.array([float(tau(k)) for k in range(top)])
tfun = lambda n: np.sign(n) * tv[np.abs(n)]
dg = np.array([float(diag(n)) for n in range(K + 1)])
fr = np.arange(-K, K + 1)
nm, na = 2 * K + 1, 2 * K - 1
a = np.zeros((nm, na))
for i in range(na):
    for k, b in ((i - K, -0.25), (i - K + 1, 0.5), (i - K + 2, -0.25)):
        wk = 2 * np.pi * k / lf
        a[k + K, i] = b * (-(wk * wk) - 0.25)
a /= np.linalg.norm(a, axis=0)


def ent(rows, cols):
    n, m = np.meshgrid(rows, cols, indexing='ij')
    d = (n - m).astype(float)
    off = lf / (2 * np.pi ** 2) * (tfun(n) - tfun(m)) / np.where(d == 0, 1, d)
    return np.where(d == 0, dg[np.minimum(np.abs(n), K)], off)


g = ent(fr, fr)
q = a.T @ g @ a
w, v = np.linalg.eigh((q + q.T) / 2)
print('LT=%s K=%d atoms=%d primes<=%d W=%.4f  max|tau|>K: %.2f  Q(unit atoms) eig min %.3e max %.3e'
      % (LTq, K, na, PRIMES[-1][0], W, np.abs(tv[K + 1:]).max(), w[0], w[-1]))
if w[0] <= 0:
    print('Q_CvS NOT positive definite'); sys.exit(0)
qih = v @ np.diag(w ** -0.5) @ v.T
x_in = 2 * np.pi * (np.eye(nm) - a @ np.linalg.pinv(a)) @ g @ a
ms = np.array([m for m in range(-NP, NP + 1) if abs(m) > K])
xo = 2 * np.pi * ent(ms, fr) @ a
br = xo.T @ xo + x_in.T @ x_in
N1 = NP + K + 3
j = np.arange(1, N1)
psi = np.concatenate(([0.0, -np.euler_gamma], -np.euler_gamma + np.cumsum(1 / j)))[:N1 + 1]
tri = np.concatenate(([0.0, np.pi ** 2 / 6], np.pi ** 2 / 6 - np.cumsum(1 / j ** 2)))[:N1 + 1]
gm = np.zeros((nm, nm))
for sg in (1, -1):
    x, y = np.meshgrid(NP + 1 - sg * fr, NP + 1 - sg * fr, indexing='ij')
    d = (x - y).astype(float)
    gm += np.where(d == 0, tri[x], (psi[x] - psi[y]) / np.where(d == 0, 1, d))
dm = np.diag(tfun(fr))
scale = (2 * np.pi) ** 2 * lf
rel = lambda bm: np.linalg.eigvalsh(qih @ bm @ qih)[-1]
best = min((rel(br + (lf / np.pi) ** 2 * a.T @ ((1 + e) * dm @ gm @ dm + (1 + 1 / e) * TF * TF * gm) @ a), e)
           for e in (0.3, 0.5, 0.7, 1, 1.4))
print('rows: NP=%d rows-only kappa %.2f  best kappa %.2f (eps=%g) -> gap needed %.4f'
      % (NP, rel(br), best[0], best[1], best[0] / scale))

# ---- trace side ----
hp = lambda t: float(mp.re(mp.digamma(mp.mpf(1) / 4 + 0.5j * t))) - float(mp.log(mp.pi))
mp.mp.dps = 15
qa, _ = np.linalg.qr(a)
wk = 2 * np.pi * fr / lf
ge = np.array([[np.exp(lf) - 1, lf], [lf, 1 - np.exp(-lf)]])
gei = np.linalg.inv(ge)


def dist2(t):
    d = t[:, None] - wk[None, :]
    ds = np.where(np.abs(d) < 1e-12, 1.0, d)
    c = np.where(np.abs(d) < 1e-12, lf, (np.exp(1j * d * lf) - 1) / (1j * ds)) / np.sqrt(lf)
    pa = (np.abs(c @ qa) ** 2).sum(axis=1)
    b = np.stack([(np.exp((1j * t + 0.5) * lf) - 1) / (1j * t + 0.5),
                  (np.exp((1j * t - 0.5) * lf) - 1) / (1j * t - 0.5)], axis=1)
    pe = np.einsum('ti,ij,tj->t', b.conj(), gei, b).real
    return lf - pa - pe


out = []
for m in [float(x) for x in sys.argv[5].split(',')]:
    tstar = float(mp.findroot(lambda t: hp(t) - (m + W), 2 * np.pi * np.exp(m + W)))
    grid = np.concatenate([np.arange(0, 4, 0.002), np.arange(4, 20, 0.01), np.arange(20, tstar, 0.02), [tstar]])
    s = np.maximum(0.0, m + W - np.array([hp(t) for t in grid]))
    d2 = np.concatenate([dist2(grid[i:i + 4000]) for i in range(0, len(grid), 4000)])
    T = 2 * np.trapezoid(s * d2, grid)
    out.append('m=%.2f t*=%.0f T=%.3f gap=%.4f' % (m, tstar, T, m - T / (2 * np.pi)))
print('trace: ' + ' | '.join(out))
