"""Weil quadratic form QW on L^2(-a,a) (additive coords), Legendre basis.
QW(v) = W(v * v~),  W(f) = int f (e^{x/2}+e^{-x/2}) - sum_n Lambda(n)/sqrt(n) (f(log n)+f(-log n))
        - (log 4pi + gamma) f(0) - int_0^inf {f(x)+f(-x)-2e^{-x/2} f(0)} e^{x/2}/(2 sinh x) dx
(Suzuki arXiv 2606.09096 (1.1); Connes-Consani-Moscovici arXiv 2511.22755 (3.10)-(3.19)).
Under RH: QW(v) = sum over zeros gamma of |v^(gamma)|^2 >= 0."""
import numpy as np
from numpy.polynomial import legendre as L
from scipy.linalg import eigh, null_space

EG = 0.5772156649015329
def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return np.log(p) if m == 1 else 0.0
    return 0.0

def basis_vals(N, a, s):
    return np.array([L.legval(s / a, np.eye(N)[k]) for k in range(N)])  # (N, len(s))

def qw_matrices(a, N, M=240):
    Q = N + 12
    xs, ws = L.leggauss(Q)
    s = a * xs; w = a * ws
    V = basis_vals(N, a, s)
    G = (V * w) @ V.T
    mp_ = V @ (w * np.exp(s / 2)); mm_ = V @ (w * np.exp(-s / 2))
    W02 = np.outer(mp_, mm_) + np.outer(mm_, mp_)
    def S(t):  # R_jk(t)+R_kj(t), R_jk(t)=int_{-a}^{a-t} v_j(s) v_k(s+t) ds, 0<=t<=2a
        lo, hi = -a, a - t
        u = (hi - lo) / 2 * xs + (hi + lo) / 2; wu = (hi - lo) / 2 * ws
        A = basis_vals(N, a, u); B = basis_vals(N, a, u + t)
        R = (A * wu) @ B.T
        return R + R.T
    tx, tw = L.leggauss(M); t = a * (tx + 1); wt = a * tw
    I = np.zeros((N, N))
    for ti, wi in zip(t, wt):
        I += wi * (S(ti) - 2 * np.exp(-ti / 2) * G) * np.exp(ti / 2) / (2 * np.sinh(ti))
    WR = (np.log(4 * np.pi) + EG) * G + I + G * np.log(np.tanh(a))
    P = np.zeros((N, N))
    for n in range(2, int(np.floor(np.exp(2 * a))) + 1):
        lam = vonmangoldt(n)
        if lam: P += lam / np.sqrt(n) * S(np.log(n))
    return W02 - WR - P, G, np.vstack([mp_, mm_])

def lowest(a, N, moment_zero=False):
    QW, G, Mom = qw_matrices(a, N)
    if moment_zero:
        Z = null_space(Mom); QW = Z.T @ QW @ Z; G = Z.T @ G @ Z
    return eigh(QW, G, eigvals_only=True)[0]
