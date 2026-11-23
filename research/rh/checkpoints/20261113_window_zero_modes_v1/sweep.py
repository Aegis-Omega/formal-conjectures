"""Low spectrum of the moment-zero Weil (CvS) form on L^2[0, l] in the basis e_m, |m| <= N
(A11, G11 of feshbach_blocks_arb.py of feshbach_arb_v2, band rows only, no tail, no C_B);
untrusted float64 eigenvalues of the Arb midpoints; with SAVE_VEC=1 also the twelve lowest
eigenvectors in the band basis (vec_<l>.pkl).  usage: sweep.py DIR N l1 l2 ...  (DIR holds cvs_entries.py)"""
import sys, os
sys.path.insert(0, sys.argv[1])
from flint import arb, acb, arb_mat, acb_mat, ctx
import cvs_entries as gw
import numpy as np
from scipy.linalg import eigh
ctx.prec = 192
N = int(sys.argv[2])
for ls in sys.argv[3:]:
    L = arb(ls)
    pi = arb.pi(); quarter = arb('0.25'); psi_q = quarter.digamma()
    def seqs(n):
        omega = 2 * pi * n / L; z = acb(quarter, pi * n / L)
        psi = z.digamma(); g_s, g_cc, g_x1, g_x2 = gw._geometric_remainders(n, L, ctx.prec)
        S = arb('0.5') * psi.imag - omega * g_s if n else arb(0)
        CC = -arb('0.5') * (psi.real - psi_q) + g_cc if n else arb(0)
        XC = arb('0.25') * z.polygamma(acb(1)).real - L * g_x1 - g_x2
        return S, CC, XC
    import math
    cmax = int(math.exp(float(L.mid())))
    primes = [(q, p) for q, p in gw.prime_powers_up_to(max(cmax, 2)) if arb(q).log() < L]
    W = [arb(p).log() * arb(q) ** arb('-0.5') for q, p in primes]; Y = [arb(q).log() for q, _ in primes]
    beta = L / (4 * pi); Cc = L * ((L.exp()).sqrt() + 1 / (L.exp()).sqrt() - 2) / (2 * pi * pi)
    kappa = gw._kappa(L); jc = gw._J(L)
    band = list(range(-N, N + 1))
    Sb = {m: seqs(abs(m)) for m in band}
    sS = lambda m, Sm: Sm if m >= 0 else -Sm
    def entry(n, m):
        Sn, CCn, XCn = Sb[n]; Sns = sS(n, Sn)
        pole = Cc * (beta * beta - n * m) / ((n * n + beta * beta) * (m * m + beta * beta))
        if n == m:
            wr = kappa + 2 * CCn + jc - (2 / L) * XCn
            wp = sum((w * 2 * (1 - y / L) * (2 * pi * n * y / L).cos() for w, y in zip(W, Y)), arb(0))
        else:
            wr = (sS(m, Sb[m][0]) - Sns) / (pi * (n - m))
            wp = sum((w * ((2 * pi * m * y / L).sin() - (2 * pi * n * y / L).sin()) / (pi * (n - m)) for w, y in zip(W, Y)), arb(0))
        return pole - wr - wp
    def mom(m, s):
        a = acb(s, 2 * pi * m / L); return ((a * L).exp() - 1) / a
    piv = [0, 1]; rest = [m for m in band if m not in piv]
    Cpinv = acb_mat([[mom(m, s) for m in piv] for s in (arb('0.5'), arb('-0.5'))]).inv()
    Z = acb_mat(2 * N + 1, len(rest))
    for j, m in enumerate(rest):
        Z[band.index(m), j] = 1
        sol = Cpinv * acb_mat([[-mom(m, arb('0.5'))], [-mom(m, arb('-0.5'))]])
        for t, p in enumerate(piv): Z[band.index(p), j] = sol[t, 0]
    Qb = acb_mat(arb_mat([[entry(n, m) for m in band] for n in band]))
    Zh = Z.conjugate().transpose()
    A11 = Zh * Qb * Z; G11 = Zh * Z
    mid = lambda M: np.array([[complex(float(M[i, j].real.mid()), float(M[i, j].imag.mid())) for j in range(M.ncols())] for i in range(M.nrows())])
    A, G = mid(A11), mid(G11); A = (A + A.conj().T) / 2; G = (G + G.conj().T) / 2
    ev = eigh(A, G, eigvals_only=True)
    if os.environ.get('SAVE_VEC'):
        ev2, U = eigh(A, G)
        import pickle
        pickle.dump(dict(l=float(ls), N=N, ev=ev2, V=mid(Z) @ U[:, :12]), open(f'vec_{ls}.pkl', 'wb'))
    Tstar = 2 * math.pi * math.exp(float(ls))
    print(f'l={ls} T*={Tstar:.3f} N={N}: ' + ' '.join('%.2e' % x for x in ev[:12]), flush=True)
