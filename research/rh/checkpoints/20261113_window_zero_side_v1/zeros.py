"""The first n zeta-zero ordinates (Arb, python-flint acb.zeta_zeros) as float64, cached in zeros_<n>.npy.
usage: zeros.py n"""
import sys, numpy as np
from flint import acb, ctx
ctx.prec = 64
n = int(sys.argv[1]); out = []
for s in range(1, n + 1, 2000):
    out += [float(z.imag.mid()) for z in acb.zeta_zeros(s, min(2000, n + 1 - s))]
np.save(f'zeros_{n}.npy', np.array(out)); print(len(out), out[0], out[-1])
