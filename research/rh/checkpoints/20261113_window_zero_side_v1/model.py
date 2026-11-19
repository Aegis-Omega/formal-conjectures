"""A zero-side model of the window floor: on the moment-zero subspace of span{e_m, |m| <= N} in L^2[0, l]
(the Z of sweep.py), the form sum_{gamma < T0} |Ghat(gamma)|^2 + int_{T0}^inf |Ghat(t)|^2 dN0(t) with the exact
zeros below T0 and the Riemann-von Mangoldt density dN0 = log(t / 2 pi) dt / (2 pi) above (gamma, t of both
signs), and its lowest generalized eigenvalues next to those of the Weil matrix (vec_<l>.pkl).
usage: model.py vec_<l>.pkl zeros_<n>.npy T0_1 T0_2 ...  (T0 = 'star' for 2 pi e^l)"""
import pickle, sys
import numpy as np
from scipy.linalg import eigh, null_space
d = pickle.load(open(sys.argv[1], 'rb')); l, N, V, ev = d['l'], d['N'], d['V'], d['ev']
gam = np.load(sys.argv[2]); w = 2 * np.pi * np.arange(-N, N + 1) / l
# moment-zero subspace: int_0^l G e^{+-x/2} = 0 for G = sum c_m e_m / sqrt(l)
mom = lambda s: (np.exp((s + 1j * w) * l) - 1) / (s + 1j * w)
B = null_space(np.vstack([mom(0.5), mom(-0.5)]))          # orthonormal basis, 2N - 1 columns
def gram(t, wt):  # sum_t wt(t) [g(t) g(t)^H + g(-t) g(-t)^H] on the subspace
    M = np.zeros((B.shape[1], B.shape[1]), complex)
    for s in (1, -1):
        for a in range(0, len(t), 5000):
            u = s * t[a:a + 5000]
            F = (((np.exp(-1j * u * l) - 1) / 1j)[:, None] / (w[None, :] - u[:, None]) / np.sqrt(l)) @ B
            M += (F.conj() * wt[a:a + 5000, None]).T @ F
    return M
Ts = 2 * np.pi * np.exp(l)
print(f'l = {l}, N = {N}, T* = {Ts:.2f}; Weil matrix: ' + ' '.join('%.3e' % x for x in ev[:6]))
for a in sys.argv[3:]:
    T0 = Ts * float(a[4:] or 1) if a.startswith('star') else float(a)
    z = gam[gam < T0]; M = gram(z, np.ones(len(z)))
    tt = np.exp(np.linspace(np.log(T0), np.log(1e7), 200001)); h = np.diff(np.log(tt))[0]
    wt = np.log(tt / (2 * np.pi)) / (2 * np.pi) * tt * h; wt[0] /= 2; wt[-1] /= 2
    M += gram(tt, wt)
    mu = eigh((M + M.conj().T) / 2, eigvals_only=True)
    print(f'  T0 = {T0:9.2f} ({len(z):5d} exact zeros): ' + ' '.join('%.3e' % x for x in mu[:6]), flush=True)
