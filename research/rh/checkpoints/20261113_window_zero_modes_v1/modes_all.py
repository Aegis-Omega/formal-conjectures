"""All local minima of |G^(t)| on (5, 60) for the lowest eigenvector (see modes.py), with depth
relative to the median of |G^| and the nearest zeta zero.  usage: modes_all.py vec_<l>.pkl"""
import pickle, sys
import numpy as np
d = pickle.load(open(sys.argv[1], 'rb')); l, N, V = d['l'], d['N'], d['V']
w = 2 * np.pi * np.arange(-N, N + 1) / l
gam = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073,
       48.005151, 49.773832, 52.970321, 56.446248, 59.347044]
t = np.linspace(0.5, 60, 119001)
f = np.abs((np.exp(-1j * t * l) - 1) * (V[None, :, 0] / (w[None, :] - t[:, None])).sum(axis=1))
med = np.median(f[t > 5])
samp = 2 * np.pi * np.arange(1, 40) / l
print(f'l = {l}, N = {N}; local minima of |G^| for the lowest eigenvector (depth = |G^| / median)')
for i in range(1, len(t) - 1):
    if f[i] < f[i - 1] and f[i] <= f[i + 1] and t[i] > 5:
        g = min(gam, key=lambda x: abs(x - t[i])); s = min(samp, key=lambda x: abs(x - t[i]))
        tag = f'zeta zero {g:.4f} (diff {t[i] - g:+.4f})' if abs(t[i] - g) < 0.3 else (f'sampling point {s:.3f}' if abs(t[i] - s) < 0.1 else '-')
        print(f'  t = {t[i]:8.4f}  depth {f[i] / med:.1e}  {tag}')
