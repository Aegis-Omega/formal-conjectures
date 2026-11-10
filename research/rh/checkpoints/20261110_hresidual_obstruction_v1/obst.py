"""Untrusted float check of a necessary condition of `hresidual` on the near-kernel packet of a window.
See README.md for the derivation.  usage: obst.py LT K   (uses ../20261110_window_l32_feasibility_v1/feas.py)
"""
import os
import runpy
import sys
import numpy as np

LTs, Ks = sys.argv[1], sys.argv[2]
feas = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '20261110_window_l32_feasibility_v1', 'feas.py')
sys.argv = ['feas.py', LTs, Ks, str(int(Ks) + 180), '13', '1.65']
ns = runpy.run_path(feas)
a, g, lf, fr = ns['a'], ns['g'], ns['lf'], ns['fr']
G = a.T @ a
Q = a.T @ g @ a
w, v = np.linalg.eigh(G)
gih = v @ np.diag(w ** -0.5) @ v.T
lam, vec = np.linalg.eigh(gih @ ((Q + Q.T) / 2) @ gih / lf)
c = a @ (gih @ vec[:, 0])
x = np.linspace(0, lf, 4001)
dens = np.abs(np.exp(1j * np.outer(x, 2 * np.pi * fr / lf)) @ c) ** 2
tot = np.trapezoid(dens, x)
print('Rayleigh quotient -B(g,g)/||g||^2 of the near-kernel packet: %.3e (next %.3e)' % (lam[0], lam[1]))
cLF = 676 / 65536
theta = np.exp(-(0.5 - 2 / 128) / 2) / (1 - np.exp(-2 * (0.5 - 2 / 128))) / 128
const = 2 * (2 * cLF - theta)
mass = lambda lo, hi: np.sqrt(np.trapezoid(np.where((x >= lo) & (x <= hi), dens, 0), x) / tot)
best = max((mass(x0, x0 + 0.09) * mass(x0 + 0.59, x0 + 0.675), x0) for x0 in np.arange(0, lf - 0.675, 0.005))
print('2cLF=%.6f theta=%.6f const=%.5f  A=[%.3f,%.3f] B=[%.3f,%.3f]  ||g 1_A|| ||g 1_B|| / ||g||^2 = %.4f'
      % (2 * cLF, theta, const, best[1], best[1] + 0.09, best[1] + 0.59, best[1] + 0.675, best[0]))
print('hresidual would force -B(g,g)/||g||^2 >= %.3e ; model value %.3e ; factor %.0f'
      % (const * best[0], lam[0], const * best[0] / lam[0]))
