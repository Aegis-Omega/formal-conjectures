"""Zero side of the explicit formula for the saved eigenvectors (see sweep.py, SAVE_VEC=1): for
G = sum_m V_m e^{2 pi i m x / l} / sqrt(l) on [0, l] (moment-zero), Ghat(t) = int_0^l G(x) e^{-itx} dx and
Z(G) = sum over zeros rho = 1/2 + i gamma of |Ghat(gamma)|^2 (gamma of both signs), from the first n
ordinates (zeros.py) plus the Riemann-von Mangoldt density integral above them. Prints the form value
lambda = <G, A G> next to Z(G) and the share of Z(G) from the zeros below T* = 2 pi e^l.
usage: explicit.py vec_<l>.pkl zeros_<n>.npy"""
import pickle, sys
import numpy as np
d = pickle.load(open(sys.argv[1], 'rb')); l, N, V, ev = d['l'], d['N'], d['V'], d['ev']
gam = np.load(sys.argv[2]); K = V.shape[1]
w = 2 * np.pi * np.arange(-N, N + 1) / l
def f(t):  # |Ghat(t)|^2 + |Ghat(-t)|^2 for each of the K vectors, t a 1-d array
    out = np.zeros((len(t), K))
    for s in (1, -1):
        u = s * t
        for a in range(0, len(u), 4000):
            uu = u[a:a + 4000]
            g = ((np.exp(-1j * uu * l) - 1) / 1j)[:, None] * ((1 / (w[None, :] - uu[:, None])) @ V) / np.sqrt(l)
            out[a:a + 4000] += np.abs(g) ** 2
    return out
T = gam[-1]; Ts = 2 * np.pi * np.exp(l)
fz = f(gam)
tt = np.exp(np.linspace(np.log(T), np.log(1e7), 400001)); ft = f(tt) * (np.log(tt / (2 * np.pi)) / (2 * np.pi))[:, None]
tail = np.trapezoid(ft * tt[:, None], np.log(tt), axis=0)
c = (np.abs(V.sum(axis=0)) ** 2) * 4 / l   # f(t) ~ c / t^2 on average
tail += c * (np.log(1e7 / (2 * np.pi)) + 1) / 1e7 / (2 * np.pi)
Z = fz.sum(axis=0) + tail; low = fz[gam < Ts].sum(axis=0)
print(f'l = {l}, N = {N}, zeros: {len(gam)} (to {T:.1f}), T* = {Ts:.2f} ({(gam < Ts).sum()} zeros below)')
print(' k   lambda (form)   Z (zeros)       Z/lambda - 1   tail share   share below T*')
for k in range(K):
    print(f'{k + 1:2d}   {ev[k]:.6e}   {Z[k]:.6e}   {Z[k] / ev[k] - 1:+.2e}       {tail[k] / Z[k]:.2e}     {low[k] / Z[k]:.2e}')
