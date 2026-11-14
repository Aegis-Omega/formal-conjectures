import numpy as np, mpmath, time, sys
from numpy.polynomial import legendre as L, polynomial as P
sys.path.insert(0, '.')
from qw import qw_matrices
t0 = time.time()
gam = np.array([float(mpmath.zetazero(k).imag) for k in range(1, 301)])
print('zeros', round(time.time() - t0, 1), 's, last', gam[-1])
xs, ws = L.leggauss(4000)
for a in (1.7, 2.5):
    for k in (6, 10):
        N = 2 * k + 1
        c = L.poly2leg(P.polypow([1, 0, -1], k))   # (1-x^2)^k in x = t/a
        QW, G, _ = qw_matrices(a, N)
        lhs = c @ QW @ c
        t = a * xs; v = (1 - (t / a) ** 2) ** k
        vh = np.array([np.sum(a * ws * v * np.cos(g * t)) for g in gam])
        rhs = 2 * np.sum(vh ** 2)
        print(f'a={a} k={k}  matrix QW={lhs:.12e}  zeros-sum={rhs:.12e}  rel.diff={abs(lhs-rhs)/abs(rhs):.2e}')
