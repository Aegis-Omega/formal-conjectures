"""High-precision QW on L^2(-a,a), Legendre basis P_k(s/a).
R_jk(t) = a * rho_jk(t/a), rho_jk(tau) = int_{-1}^{1-tau} P_j(x) P_k(x+tau) dx  (exact rationals, a-independent)."""
import flint, mpmath as mp, pickle, os, sys
from flint import fmpq_poly, fmpq

def legendre_polys(N):
    P = [fmpq_poly([1]), fmpq_poly([0, 1])]
    for n in range(1, N):
        P.append((fmpq_poly([0, 2 * n + 1]) * P[n] - n * P[n - 1]) / (n + 1))
    return P[:N]

def rho_table(N):
    fn = f'rho_{N}.pkl'
    if os.path.exists(fn): return pickle.load(open(fn, 'rb'))
    P = legendre_polys(N)
    one_minus = fmpq_poly([1, -1])            # 1 - tau
    # derivatives P_k^{(i)}
    D = [[P[k]] for k in range(N)]
    for k in range(N):
        for i in range(1, k + 1): D[k].append(D[k][-1].derivative())
    fact = [1]
    for i in range(1, N + 1): fact.append(fact[-1] * i)
    rho = {}
    for j in range(N):
        for k in range(N):
            tot = fmpq_poly([0])
            for i in range(0, k + 1):
                F = (P[j] * D[k][i]).integral()
                val = F(one_minus) - F(fmpq(-1))     # polynomial in tau
                tot += val * fmpq_poly([0] * i + [fmpq(1, fact[i])])
            rho[(j, k)] = [tot[m] for m in range(tot.degree() + 1)]
    pickle.dump(rho, open(fn, 'wb'))
    return rho

def vm(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)
    return mp.mpf(0)

def qw_hp(a, N, dps=150):
    mp.mp.dps = dps
    a = mp.mpf(a)
    rho = rho_table(N)
    sig = {}
    for j in range(N):
        for k in range(N):
            r1, r2 = rho[(j, k)], rho[(k, j)]
            L = max(len(r1), len(r2))
            sig[(j, k)] = [(mp.mpf(int(r1[m].p)) / int(r1[m].q) if m < len(r1) else 0) +
                           (mp.mpf(int(r2[m].p)) / int(r2[m].q) if m < len(r2) else 0) for m in range(L)]
    G = [a * 2 / (2 * k + 1) for k in range(N)]
    K = lambda t: mp.exp(t / 2) / (2 * mp.sinh(t))
    deg = max(len(s) for s in sig.values())
    mu = [None] + [a * mp.quad(lambda x, m=m: x ** m * K(a * x), [0, 1, 2]) for m in range(1, deg)]
    nu = mp.quad(lambda t: (1 - mp.exp(-t / 2)) * K(t), [0, a, 2 * a])
    leg = legendre_polys(N)
    def mom(c):
        return [a * mp.quad(lambda x, k=k: mp.mpf(1) * sum(mp.mpf(int(leg[k][i].p)) / int(leg[k][i].q) * x ** i for i in range(leg[k].degree() + 1)) * mp.exp(c * a * x), [-1, 0, 1]) for k in range(N)]
    mplus, mminus = mom(mp.mpf(1) / 2), mom(-mp.mpf(1) / 2)
    primes = [(n, vm(n)) for n in range(2, int(mp.floor(mp.exp(2 * a))) + 1)]
    primes = [(n, l) for n, l in primes if l != 0]
    Q = mp.matrix(N, N)
    for j in range(N):
        for k in range(j, N):
            s = sig[(j, k)]
            arch = sum(a * s[m] * mu[m] for m in range(1, len(s))) + (2 * G[j] * nu if j == k else 0)
            WR = ((mp.log(4 * mp.pi) + mp.euler + mp.log(mp.tanh(a))) * G[j] if j == k else 0) + arch
            pr = sum(l / mp.sqrt(n) * a * mp.polyval(s[::-1], mp.log(n) / a) for n, l in primes)
            W02 = mplus[j] * mminus[k] + mminus[j] * mplus[k]
            Q[j, k] = Q[k, j] = W02 - WR - pr
    return Q, G, mplus, mminus

def lowest_hp(a, N, dps=150, moment_zero=False):
    Q, G, mpl, mmi = qw_hp(a, N, dps)
    d = [1 / mp.sqrt(g) for g in G]
    B = mp.matrix(N, N)
    for j in range(N):
        for k in range(N): B[j, k] = d[j] * Q[j, k] * d[k]
    if moment_zero:
        U = [[mpl[k] * d[k] for k in range(N)], [mmi[k] * d[k] for k in range(N)]]
        basis = []
        vecs = U + [[mp.mpf(1) if i == r else mp.mpf(0) for i in range(N)] for r in range(N)]
        for v in vecs:
            w = list(v)
            for b in basis:
                c = mp.fsum(x * y for x, y in zip(w, b)); w = [x - c * y for x, y in zip(w, b)]
            nrm = mp.sqrt(mp.fsum(x * x for x in w))
            if nrm > mp.mpf(10) ** (-dps // 3): basis.append([x / nrm for x in w])
        Z = mp.matrix([b for b in basis[2:]]).T      # N x (N-2), orthogonal to constraints
        B = Z.T * B * Z
    E = mp.eigsy(B, eigvals_only=True)
    return min(E)
