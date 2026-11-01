import sys; sys.path.insert(0, '.')
import mpmath as mp
from qwhp import qw_hp
N = 32
for a in (0.3, 0.5, 0.6, 0.6875):
    Q, G, _, _ = qw_hp(a, N, 120)
    d = [1 / mp.sqrt(g) for g in G]
    B = mp.matrix(N, N)
    for j in range(N):
        for k in range(N): B[j, k] = d[j] * Q[j, k] * d[k]
    E, V = mp.eigsy(B)
    idx = sorted(range(N), key=lambda i: E[i])
    l1, l2 = E[idx[0]], E[idx[1]]
    v = [V[k, idx[0]] for k in range(N)]
    odd = mp.sqrt(mp.fsum(v[k] ** 2 for k in range(1, N, 2)))
    print(f'a={a}: lam1={mp.nstr(l1,6)} lam2={mp.nstr(l2,6)} gap ratio lam2/lam1={mp.nstr(l2/l1,4)}  odd part of eigvec={mp.nstr(odd,3)}', flush=True)
