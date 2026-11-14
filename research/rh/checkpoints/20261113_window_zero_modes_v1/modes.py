"""Fourier zeros of the low eigenvectors of the moment-zero window form (sweep_vec.py output).
For G(x) = sum_m v_m e^{i w_m x} on [0, l], w_m = 2 pi m / l, G^(t) = int_0^l G(x) e^{-i t x} dx
= (e^{-i t l} - 1) sum_m v_m / (i (w_m - t)). Prints the nine deepest local minima of |G^| on
(5, 60) away from the sampling points 2 pi k / l, for the ten lowest eigenvectors.
usage: modes.py vec_<l>.pkl   (untrusted float64; evidence kind numerical)"""
import pickle, sys
import numpy as np
d = pickle.load(open(sys.argv[1], 'rb')); l, N, V, ev = d['l'], d['N'], d['V'], d['ev']
w = 2 * np.pi * np.arange(-N, N + 1) / l
t = np.linspace(0.5, 60, 119001)
samp = 2 * np.pi * np.arange(1, 40) / l
for j in range(10):
    f = np.abs((np.exp(-1j * t * l) - 1) * (V[None, :, j] / (w[None, :] - t[:, None])).sum(axis=1))
    mins = [i for i in range(1, len(t) - 1) if f[i] < f[i - 1] and f[i] <= f[i + 1] and t[i] > 5 and np.min(np.abs(samp - t[i])) > 0.05]
    deep = sorted(sorted(mins, key=lambda i: f[i])[:9])
    print(f'eigenvalue {j + 1} ({ev[j]:.2e}): minima of |G^| at ' + ' '.join('%.2f' % t[i] for i in deep))
