"""Untrusted float LP for the Schur gap m - T/(2 pi) of a Krein certificate at LT = 6/5.

Numerics only, no certificate. The `hcert` premise of `CvSRowTailV1.window_of_certificate_tail`
with M = 3 is imposed on a grid of t >= 0 (everything is even in t):

  Wt (ScertM 3 t - m) + F(H)(t/2pi) + sum_l 2 Re(d_l (it)^j_l e^{itL}) + Wt s >= MU * Wt,

H = sum_j a_j (hat(u - u_j) + hat(u + u_j)) with support in |u| >= L, d-terms in the even forms
cos(tL), t sin(tL), t^2 cos(tL), t^3 sin(tL), t^4 cos(tL), slack s >= 0, and T = 2 int s trialDist,
where trialDist is the exact distance^2 of e^{ixt} on [0, LT] from the 139 moment atoms. For
t >= tmax the constraint is replaced by an envelope bound (ScertM >= Re psi(1/4 + i tmax/2) -
log pi - 2.25, |F(hat)| <= min(h, 4/(h t^2))). The optimum is re-checked on a 5x finer grid up
to 2 tmax.

usage: python3 -I krein_gap_l12.py L h J tmax dt MU [out.npz]   e.g. 1.25 0.05 40 500 0.02 0.05 sol.npz
The optional out.npz stores the solution for validate_krein_l12.py.
"""
import sys

import mpmath as mp
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, diags, hstack, vstack

LT = 1.2
L, h, J = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
TMAX, DT, MU = float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
K = np.arange(-70, 71)
W = 2 * np.pi * K / LT
# the atoms span the orthogonal complement of these two moment vectors in span{e_k : |k| <= 70}
QO, _ = np.linalg.qr(np.stack([1 / (W ** 2 + 0.25), K / (W ** 2 + 0.25)], axis=1))
L2, L3 = np.log(2), np.log(3)
AMP = np.sqrt(2) * L2 + 2 * L3 / np.sqrt(3)


def scert(t):
    return float(mp.re(mp.digamma(0.25 + 0.5j * t))) - np.log(np.pi) - \
        np.sqrt(2) * L2 * np.cos(t * L2) - 2 * L3 / np.sqrt(3) * np.cos(t * L3)


def trial(t):
    d = t - W
    small = np.abs(d) < 1e-12
    v = np.where(small, LT, (np.exp(1j * d * LT) - 1) / (1j * np.where(small, 1, d)))
    pv = QO.conj().T @ v
    return max(0.0, LT - (np.vdot(v, v).real - np.vdot(pv, pv).real) / LT)


def features(t):
    wt = (t * t + 0.25) ** 2
    uj = L + h + 2 * h * np.arange(J)
    bh = h * np.sinc(t * h / (2 * np.pi)) ** 2
    fh = 2 * np.cos(np.outer(t, uj)) * bh[:, None]
    dd = np.stack([np.cos(t * L), t * np.sin(t * L), t ** 2 * np.cos(t * L),
                   t ** 3 * np.sin(t * L), t ** 4 * np.cos(t * L)], axis=1)
    return np.hstack([fh, dd]) / wt[:, None]


def main():
    ts = np.arange(0, TMAX + DT / 2, DT)
    S = np.array([scert(t) for t in ts])
    TD = np.array([trial(t) for t in ts])
    wq = np.full(len(ts), DT)
    wq[0] = wq[-1] = DT / 2
    phi = features(ts)
    n, p = phi.shape
    psi_lo = float(mp.re(mp.digamma(0.25 + 0.5j * TMAX))) - np.log(np.pi) - AMP
    wt0 = (TMAX ** 2 + 0.25) ** 2
    env = np.concatenate([np.full(J, 2 * min(h, 4 / (h * TMAX ** 2)) / wt0),
                          [max(TMAX ** j / wt0, 1.0 if j == 4 else 0.0) for j in range(5)]])
    # x = [m, c (p), s (n), z (p)], z >= |c|
    eye = csr_matrix(np.eye(p))
    a = vstack([
        hstack([csr_matrix(np.ones((n, 1))), csr_matrix(-phi), diags(-np.ones(n)), csr_matrix((n, p))]),
        hstack([csr_matrix((p, 1)), eye, csr_matrix((p, n)), -eye]),
        hstack([csr_matrix((p, 1)), -eye, csr_matrix((p, n)), -eye]),
        hstack([csr_matrix(np.ones((1, 1))), csr_matrix((1, p)), csr_matrix((1, n)), csr_matrix(env[None, :])]),
    ]).tocsr()
    b = np.concatenate([S - MU, np.zeros(2 * p), [psi_lo - MU]])
    cost = np.concatenate([[-1.0], np.zeros(p), wq * TD / np.pi, np.zeros(p)])
    bounds = [(None, None)] * (1 + p) + [(0, None)] * (n + p)
    res = linprog(cost, A_ub=a, b_ub=b, bounds=bounds, method="highs")
    print("L=%g h=%g J=%d tmax=%g dt=%g MU=%g: %s" % (L, h, J, TMAX, DT, MU, res.message))
    if res.status != 0:
        return
    m, c, s = res.x[0], res.x[1:1 + p], res.x[1 + p:1 + p + n]
    T = 2 * np.sum(wq * s * TD)
    print("m = %.4f  T = %.4f  gap m - T/(2 pi) = %.4f" % (m, T, m - T / (2 * np.pi)))
    if len(sys.argv) > 7:
        np.savez(sys.argv[7], m=m, c=c, s=s, ts=ts, L=L, h=h, J=J, TMAX=TMAX, DT=DT, MU=MU)
    tv = np.arange(0, 2 * TMAX, DT / 5)
    sv_ = np.interp(tv, ts, S, right=np.nan)
    near = (tv < 60) | np.isnan(sv_)
    sv_[near] = [scert(t) for t in tv[near]]
    lhs = sv_ - m + features(tv) @ c + np.interp(tv, ts, s, right=0.0)
    print("re-check on [0, %g] step %g: min = %.3e, points below 0: %d"
          % (2 * TMAX, DT / 5, lhs.min(), int(np.sum(lhs < 0))))


if __name__ == "__main__":
    main()
