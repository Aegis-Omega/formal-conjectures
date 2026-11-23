# Independent check: moment-zero basis of feshbach_arb_v2 (piv = [0, 1], mom(m,s) = (e^{(s+i w_m)L}-1)/(s+i w_m))
import numpy as np, sympy as sp
# closed form: c_p(m) = -((m-q)/(p-q)) (1/4 + k p^2)/(1/4 + k m^2),  k = (2 pi/L)^2, {p,q} = {0,1}
m, k = sp.symbols('m k', positive=True)
w = lambda j: sp.sqrt(k) * j
def momr(j, s): return 1 / (s + sp.I * w(j))           # the factor e^{sL}-1 cancels row-wise
Cp = sp.Matrix([[momr(p, s) for p in (0, 1)] for s in (sp.Rational(1, 2), -sp.Rational(1, 2))])
sol = -Cp.inv() * sp.Matrix([momr(m, sp.Rational(1, 2)), momr(m, -sp.Rational(1, 2))])
cf = [-(m - 1) / (0 - 1) * (sp.Rational(1, 4)) / (sp.Rational(1, 4) + k * m**2),
      -(m - 0) / (1 - 0) * (sp.Rational(1, 4) + k) / (sp.Rational(1, 4) + k * m**2)]
print('closed form residuals:', [sp.simplify(sol[i] - cf[i]) for i in range(2)])
# numeric: the actual k = 799 basis at L = 9/5, N = 400 (float), Woodbury vs direct inverse
L, N = 1.8, 400
band = list(range(-N, N + 1)); piv = [0, 1]; rest = [x for x in band if x not in piv]
def mom(x, s): a = s + 2j * np.pi * x / L; return (np.exp(a * L) - 1) / a
Cpn = np.array([[mom(p, s) for p in piv] for s in (0.5, -0.5)])
U = np.array([np.linalg.solve(Cpn, -np.array([mom(x, 0.5), mom(x, -0.5)])) for x in rest]).T  # 2 x k
kk = (2 * np.pi / L) ** 2
Ucf = np.array([[-(x - 1) / (-1) * 0.25 / (0.25 + kk * x * x) for x in rest], [-x * (0.25 + kk) / (0.25 + kk * x * x) for x in rest]])
print('max |U - closed form| =', np.abs(U - Ucf).max(), ' max |Im U| =', np.abs(U.imag).max())
G = np.eye(len(rest)) + U.conj().T @ U
Gi_w = np.eye(len(rest)) - U.conj().T @ np.linalg.inv(np.eye(2) + U @ U.conj().T) @ U
print('k =', len(rest), ' ||G Gi_w - I||_max =', np.abs(G @ Gi_w - np.eye(len(rest))).max())
ev = np.linalg.eigvalsh(G); print('eig(G) in [%.6f, %.6f], cond = %.4f, ||U||^2 = %.4f' % (ev[0], ev[-1], ev[-1] / ev[0], np.linalg.norm(U, 2) ** 2))
