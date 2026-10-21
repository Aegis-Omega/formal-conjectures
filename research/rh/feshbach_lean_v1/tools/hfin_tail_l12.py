"""Untrusted float comparison of row-tail bounds for `hfin` at L = 6/5 (numerics only).

Reuses the model of hfin_feasibility_l12.py. For each NP it prints kappa = max Brow / Q_CvS with
  (a) the existing Lean bound `rowTail M L F a K (tauBound 3) 70 NP`, with the quadratic majorant
      (x + T y)^2 <= (1 + eps) x^2 + (1 + 1/eps) T^2 y^2 and (sum |a_n|)^2 <= 141 sum |a_n|^2;
  (b) an exact tail Gram bound, sum_{|m|>NP} |row_m|^2 <= (L/pi)^2 a^* ((1+eps) D G D +
      (1+1/eps) T^2 G) a, with G(n,n') = sum_{|m|>NP} 1/((m-n)(m-n')) and D = diag(tau_n).
The Schur gap needed is kappa / ((2 pi)^2 * 6/5).

usage: python3 -I hfin_tail_l12.py <feshbach_lean_v1 dir>
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, "hfin_feasibility_l12.py")).read().split("\nif __name__")[0]
G_ = {}
exec(compile(SRC, "hfin_feasibility_l12.py", "exec"), G_)
np, mp, tau, grab = G_["np"], G_["mp"], G_["tau"], G_["grab"]


def main():
    d = sys.argv[1]
    top = 2000 + 71
    t = {k: float(tau(k)) for k in range(top)}
    t.update({-k: -t[k] for k in range(1, top)})
    dlo, dhi = grab(d, "CvSDiagL12V1.lean", "diagLo"), grab(d, "CvSDiagL12V1.lean", "diagHi")
    diag = [float((a + b) / 2) for a, b in zip(dlo, dhi)]
    lf = 1.2

    def entry(n, m):
        return diag[abs(n)] if n == m else lf / (2 * np.pi ** 2) * (t[n] - t[m]) / (n - m)

    fr = np.arange(-70, 71)
    frf = fr.astype(float)
    a = np.zeros((141, 139))
    for i in range(139):
        for k, b in ((i - 70, -0.25), (i - 69, 0.5), (i - 68, -0.25)):
            wk = 2 * np.pi * k / lf
            a[k + 70, i] = b * (-(wk * wk) - 0.25)
    g = np.array([[entry(x, y) for y in fr] for x in fr])
    q = a.T @ g @ a
    w, v = np.linalg.eigh((q + q.T) / 2)
    qih = v @ np.diag(w ** -0.5) @ v.T
    x_in = 2 * np.pi * (np.eye(141) - a @ np.linalg.pinv(a)) @ g @ a
    b_in = x_in.T @ x_in
    taun = np.array([t[int(n)] for n in fr])
    tb = 4 * math.pi * (1 + math.pi / 4) + math.pi * (2 * math.log(2) / math.sqrt(2) +
                                                      2 * math.log(3) / math.sqrt(3))
    scale = (2 * np.pi) ** 2 * lf

    def rel(bm):
        return np.linalg.eigvalsh(qih @ bm @ qih)[-1]

    def rows(np_):
        ms = [m for m in range(-np_, np_ + 1) if abs(m) > 70]
        xo = np.array([[2 * np.pi * entry(n, m) for n in fr] for m in ms]) @ a
        return xo.T @ xo + b_in

    def lean_tail(np_, kk, eps):
        bt = np.zeros((139, 139))
        for j in range(kk):
            pj, qj = (taun * frf ** j) @ a, (frf ** j) @ a
            bt += (lf / np.pi) ** 2 * 2 * kk * ((1 + eps) * np.outer(pj, pj) +
                                                (1 + 1 / eps) * tb * tb * np.outer(qj, qj)) * 2 / np_ ** (2 * j + 1)
        bt += (lf / np.pi) ** 2 * 2 * (2 * tb * 70 ** kk) ** 2 * 141 * (a.T @ a) * 2 / (np_ ** (2 * kk) * (np_ - 70))
        return bt

    def gram(np_):
        gm = np.zeros((141, 141))
        for i, n in enumerate(fr):
            for j, n2 in enumerate(fr):
                s = mp.mpf(0)
                for sg in (1, -1):
                    x, y = np_ + 1 - sg * int(n), np_ + 1 - sg * int(n2)
                    s += mp.psi(1, x) if x == y else (mp.digamma(x) - mp.digamma(y)) / (x - y)
                gm[i, j] = float(s)
        return gm

    print("tauBound 3 = %.3f" % tb)
    for np_ in (400, 1000, 2000):
        br = rows(np_)
        best = min((rel(br + lean_tail(np_, kk, e)), kk, e) for kk in (2, 3, 4) for e in (0.3, 1, 3, 10))
        print("NP=%d rows %.2f | Lean rowTail best kappa %.1f (K=%d, eps=%g) -> gap >= %.3f"
              % (np_, rel(br), best[0], best[1], best[2], best[0] / scale))
    for np_ in (200, 400):
        br, gm, dm = rows(np_), gram(np_), np.diag(taun)
        for tt in (tb, 12.0):
            best = min((rel(br + (lf / np.pi) ** 2 * a.T @ ((1 + e) * dm @ gm @ dm +
                                                             (1 + 1 / e) * tt * tt * gm) @ a), e)
                       for e in (0.3, 1, 3, 10))
            print("NP=%d exact Gram tail, T=%.1f: best kappa %.1f (eps=%g) -> gap >= %.3f"
                  % (np_, tt, best[0], best[1], best[0] / scale))


if __name__ == "__main__":
    main()
