"""Which off-line zeros a window of support length l can see. The zero side of the window form (see
explicit.py) with every zero on the critical line except one pair: the two adjacent zeros nearest to a
height H are replaced by the pair 1/2 +- d + i*g0 at their mean height g0 (with the conjugates); d = 0 is
a double zero on the line. For f = G * G~ the term of a zero
1/2 + i*tau is Ghat(tau) conj(Ghat(conj tau)). The form is restricted to the moment-zero functions
in span{e_m : |m| <= B or |m - m0| <= B} (m0 = round(g0 l / 2 pi)), and its lowest
eigenvalue is printed; a negative value means a window theorem at l would exclude that zero.
usage: inject.py l zeros_<n>.npy B H1 H2 ...  (deltas 0.05, 0.1, 0.2, 0.3, 0.5)"""
import sys
import numpy as np
from scipy.linalg import eigh, null_space
l = float(sys.argv[1]); gam = np.load(sys.argv[2]); B = int(sys.argv[3])
def run(m0, k, ds):
    g0 = (gam[k] + gam[k + 1]) / 2
    m = np.union1d(np.arange(-B, B + 1), np.arange(m0 - B, m0 + B + 1)); w = 2 * np.pi * m / l
    mom = lambda s: (np.exp((s + 1j * w) * l) - 1) / (s + 1j * w)
    Q = null_space(np.vstack([mom(0.5), mom(-0.5)]))
    ghat = lambda tau: (((np.exp(-1j * tau * l) - 1) / 1j)[:, None] / (w[None, :] - tau[:, None]) / np.sqrt(l)) @ Q
    def gram(t, wt):
        M = 0
        for s in (1, -1):
            for a in range(0, len(t), 5000):
                F = ghat(s * t[a:a + 5000]); M = M + (F.conj() * wt[a:a + 5000, None]).T @ F
        return M
    z = np.delete(gam, [k, k + 1])
    M = gram(z, np.ones(len(z)))
    tt = np.exp(np.linspace(np.log(gam[-1]), np.log(1e8), 200001)); h = np.diff(np.log(tt))[0]
    wt = np.log(tt / (2 * np.pi)) / (2 * np.pi) * tt * h; wt[0] /= 2; wt[-1] /= 2
    M = M + gram(tt, wt)
    out = []
    for d in [0] + ds:
        X = 0
        for s in (1, -1):
            u = ghat(np.array([s * g0 - 1j * d]))[0]; v = ghat(np.array([s * g0 + 1j * d]))[0]
            X = X + np.outer(v.conj(), u) + np.outer(u.conj(), v)   # two zeros 1/2 +- d + i s g0
        Mx = M + X
        out.append(eigh((Mx + Mx.conj().T) / 2, eigvals_only=True)[0])
    return out
ds = [0.05, 0.1, 0.2, 0.3, 0.5]
print(f'l = {l}, band 2B+1 = {2 * B + 1}; lowest eigenvalue for d = 0, ' + ', '.join(map(str, ds)))
for Hs in sys.argv[4:]:
    k = min(int(np.argmin(np.abs(gam - float(Hs)))), len(gam) - 2); g0 = (gam[k] + gam[k + 1]) / 2
    m0 = int(round(g0 * l / (2 * np.pi)))
    r = run(m0, k, ds)
    print(f'  zeros {k + 1}, {k + 2}: g0 = {g0:10.3f} (m0 = {m0:6d}): ' + ' '.join('%+.2e' % x for x in r), flush=True)
