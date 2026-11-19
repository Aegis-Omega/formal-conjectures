"""V7 candidate: the blocks of feshbach_blocks_arb.py (A11, G11, C_B >= ||P_perp A v||^2 on V = moment-zero part of
span{e_m : |m| <= N}), with the same row model, tail bound and output format, in real Arb.

Changes against the V6 candidate (each is the same function of the true inputs, so each enclosure is valid):
 1. Rows. For n != m, pole - wr - wp = pole + (alpha_m - alpha_n) / (pi (n - m)) with
    alpha_n = -(sS(n) + sum_q w_q sin(2 pi n y_q / L)), the alpha of the tail bound. The sines are evaluated once per
    index, not twice per entry, and seqs once per |n|.
 2. V-perp = span{avec, bvec}: for v = e_m + v_0 e_0 + v_1 e_1, sum v_j/(j^2+beta^2) = 0 and sum v_j j/(j^2+beta^2) = 0.
    With M = [avec, bvec], P_V = I - M (M^T M)^{-1} M^T, and RR = Qb^T Qb + Rout^T Rout (Rout: rows N < |n| <= NP):
        C_B = Z^T (RR + Tail + Ib) Z - A11 G11^{-1} A11 = Z^T (Rout^T Rout + Tail + Ib) Z + W^T (M^T M)^{-1} W,
        W = M^T Qb Z  (2 x k).
    No k x k product A11 A11, no inverse, no subtraction of two large blocks.
 3. Z^T X Z, A11 = Z^T Qb Z and G11 = I + U^T U by the rank-two congruence of the V6 candidate.
 4. Tail = sum_i (c_i / p_i) u_i u_i^T is formed as one product; the 2K + 2 dense outer products are not stored.
Z, Qb, M and the tail are real, so everything is arb_mat (the imaginary parts of the output are 0)."""
import sys, math, json, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, arb_mat, acb, fmpq, ctx
import cvs_entries as gw
ctx.prec = 192
T0 = time.perf_counter()
def tick(s): print('T', s, round(time.perf_counter() - T0, 2), flush=True)
L = arb(sys.argv[1]); N = int(sys.argv[2]); NP = int(sys.argv[3])
pi = arb.pi(); quarter = arb('0.25'); psi_q = quarter.digamma()
def seqs(n):
    omega = 2 * pi * n / L; z = acb(quarter, pi * n / L)
    psi = z.digamma(); g_s, g_cc, g_x1, g_x2 = gw._geometric_remainders(n, L, ctx.prec)
    S = arb('0.5') * psi.imag - omega * g_s if n else arb(0)
    CC = -arb('0.5') * (psi.real - psi_q) + g_cc if n else arb(0)
    XC = arb('0.25') * z.polygamma(acb(1)).real - L * g_x1 - g_x2
    return S, CC, XC
cmax = int(math.exp(float(L.mid())))
primes = [(q, p) for q, p in gw.prime_powers_up_to(max(cmax, 2)) if arb(q).log() < L]
W = [arb(p).log() * arb(q) ** arb('-0.5') for q, p in primes]; Y = [arb(q).log() for q, _ in primes]
beta = L / (4 * pi); Cc = L * ((L.exp()).sqrt() + 1 / (L.exp()).sqrt() - 2) / (2 * pi * pi)
kappa = gw._kappa(L); jc = gw._J(L)
band = list(range(-N, N + 1))
# per |n| <= NP: S_n (signed below), and CC, XC for the diagonal (|n| <= N)
Sabs = {}; CXb = {}
for n in range(NP + 1):
    S_, CC_, XC_ = seqs(n); Sabs[n] = S_
    if n <= N: CXb[n] = (CC_, XC_)
sS = lambda m: Sabs[m] if m >= 0 else -Sabs[-m]
def sig(n): return sum((w * (2 * pi * n * y / L).sin() for w, y in zip(W, Y)), arb(0))
alph = {}
for n in range(NP + 1):
    a_ = -(Sabs[n] + sig(n)); alph[n] = a_; alph[-n] = -a_
invd = {n: 1 / (n * n + beta * beta) for n in range(-NP, NP + 1)}
tick('seqs')
def diag_entry(n):
    CCn, XCn = CXb[abs(n)]
    pole = Cc * (beta * beta - n * n) / ((n * n + beta * beta) * (n * n + beta * beta))
    wr = kappa + 2 * CCn + jc - (2 / L) * XCn
    wp = sum((w * 2 * (1 - y / L) * (2 * pi * n * y / L).cos() for w, y in zip(W, Y)), arb(0))
    return pole - wr - wp
def row(n):
    an = alph[n]; dn = Cc * invd[n]; b2 = beta * beta
    return [diag_entry(n) if n == m else
            dn * (b2 - n * m) * invd[m] + (alph[m] - an) / (pi * (n - m)) for m in band]
Qb = arb_mat([row(n) for n in band])
tick('Qb')
# Rout^T Rout = sum over blocks of CH rows (the same sum, without storing the (2 NP - 2 N) x (2N+1) matrix)
outs = [n for n in range(-NP, NP + 1) if abs(n) > N]
CH = int(os.environ.get('ROW_CHUNK', '2000'))
RRout = arb_mat(2 * N + 1, 2 * N + 1)
for s in range(0, len(outs), CH):
    Rc = arb_mat([row(n) for n in outs[s:s + CH]])
    RRout += Rc.transpose() * Rc
del Rc
tick('rows+RRout')
# tail |n| > NP: the bound of feshbach_blocks_arb.py, unchanged.
KS = arb(0)
for kk in range(200):
    ck = 2 * kk + arb('0.5'); KS += (-ck * L).exp() / (2 * ck)
ymin = pi * NP / L
K2 = pi / 4 + 1 / (2 * ymin) + KS + sum(W, arb(0))
alpha = [alph[m] for m in band]
avec = [1 / (m * m + beta * beta) for m in band]; bvec = [m / (m * m + beta * beta) for m in band]
TAIL_ORDER = int(os.environ.get('TAIL_ORDER', '1'))
Amax = max(abs(a_) for a_ in alpha).upper()
K = TAIL_ORDER; f = 2 * K + 3
vecs = []; coefs = []
for j in range(K):
    cj = 2 / ((2 * j + 1) * pi * pi * arb(NP) ** (2 * j + 1))
    vecs.append([a_ * arb(m) ** j for a_, m in zip(alpha, band)]); coefs.append(cj)
    vecs.append([arb(m) ** j for m in band]); coefs.append(cj * K2 * K2)
vecs.append(bvec); coefs.append(2 * Cc * Cc / NP)
vecs.append(avec); coefs.append(2 * Cc * Cc * beta ** 4 / (3 * arb(NP) ** 3))
Eco1 = 2 * (Amax + K2) ** 2 * arb(N) ** (2 * K) * (2 * N + 1) / ((2 * K + 1) * pi * pi * arb(NP - N) ** (2 * K + 1))
# moment-zero basis: Z = e_m + v_0(m) e_0 + v_1(m) e_1, m not in {0, 1}
piv = [0, 1]; rest = [m for m in band if m not in piv]; k = len(rest)
fi = [band.index(m) for m in rest]; pii = [band.index(p) for p in piv]
omega2 = (2 * pi / L) ** 2
U2 = arb_mat(2, k)
for jj, m in enumerate(rest):
    d = arb(m * m) * omega2 + quarter
    U2[0, jj] = (arb(m) - 1) * quarter / d
    U2[1, jj] = -arb(m) * (omega2 + quarter) / d
U2t = U2.transpose()
def sub(X, I, J): return arb_mat([[X[i, j] for j in J] for i in I])
def proj(X):  # Z^T X Z for Z = [I_free; U2] after reordering rows
    return sub(X, fi, fi) + sub(X, fi, pii) * U2 + U2t * sub(X, pii, fi) + (U2t * sub(X, pii, pii)) * U2
A11 = proj(Qb)
G11 = U2t * U2
for i in range(k): G11[i, i] += 1
tick('A11G11')
def mid(M): return [[float(M[i, j].mid()) for j in range(M.ncols())] for i in range(M.nrows())]
import numpy as np
from scipy.linalg import eigh
WEIGHTS = os.environ.get('TAIL_WEIGHTS', 'uniform'); RITZ = os.environ.get('RITZ', '')
if RITZ or WEIGHTS != 'uniform':
    _, U0 = eigh(np.array(mid(A11)), np.array(mid(G11)))
if RITZ:  # diagnostic only: bottom pair of (A11, G11) by inverse iteration at working precision, from the float64 start
    u1 = arb_mat([[float(x)] for x in U0[:, 0]])
    for it in range(6):
        u1 = A11.solve(G11 * u1, nonstop=True, algorithm='approx')
        nrm = max(abs(float(u1[i, 0].mid())) for i in range(k)); u1 = u1 * arb(1 / nrm)
    def rq(Mx): return (u1.transpose() * Mx * u1)[0, 0] / (u1.transpose() * G11 * u1)[0, 0]
    lam1 = rq(A11); print('ritz lam1', lam1.str(12), 'float64 eigh lam1', _[0], flush=True)
    tick('ritz')
if WEIGHTS == 'uniform':
    pw = [fmpq(1, f)] * f
else:
    Zf = np.zeros((2 * N + 1, k)); Zf[fi, np.arange(k)] = 1; Zf[pii, :] = np.array(mid(U2))
    v0 = Zf @ (np.array([float(u1[i, 0].mid()) for i in range(k)]) if RITZ == 'weights' else U0[:, 0])
    t = [abs(float(c.mid())) * float(np.dot(np.array([float(x.mid()) for x in u]), v0)) ** 2 for u, c in zip(vecs, coefs)]
    t.append(float(Eco1.mid()) * float(np.dot(v0, v0)))
    r = [math.sqrt(x) + 1e-300 for x in t]
    pw = [fmpq(int(1e9 * (0.5 / f + 0.5 * x / sum(r))), 10 ** 9) for x in r]
assert sum(pw) <= 1 and all(x > 0 for x in pw)
Ut = arb_mat([list(col) for col in zip(*vecs)])                       # (2N+1) x (2K+2)
Us = arb_mat([[Ut[i, j] * (coefs[j] / arb(pw[j])) for j in range(Ut.ncols())] for i in range(Ut.nrows())])
Tail = Us * Ut.transpose()
Eco = Eco1 / arb(pw[-1])
print('K2', K2, 'Amax', Amax, 'Eco', Eco, 'weights', WEIGHTS, [str(x) for x in pw])
Xout = RRout + Tail
for i in range(2 * N + 1): Xout[i, i] += Eco
tick('Tail')
M = arb_mat([[avec[i], bvec[i]] for i in range(2 * N + 1)])
Wt = M.transpose() * Qb                                               # 2 x (2N+1)
Wm = sub(Wt, [0, 1], fi) + sub(Wt, [0, 1], pii) * U2                   # M^T Qb Z
CB = proj(Xout) + Wm.transpose() * ((M.transpose() * M).inv() * Wm)
tick('CB')
if RITZ:
    WtMi = Wm.transpose() * ((M.transpose() * M).inv() * Wm)
    parts = [('Rout', proj(RRout)), ('Tail', proj(Tail)), ('Eco*G11', G11 * Eco), ('inband_rank2', WtMi)]
    tot = rq(CB); print('C_B(u1)', tot.str(12), ' lam1 - C_B(u1)/0.98', (lam1 - tot / arb('0.98')).str(8))
    for nm, Mx in parts: print('  part', nm, rq(Mx).str(10), flush=True)
    del parts, WtMi, Mx
del RRout, Tail, Xout, Qb, Wt, Wm, Us, Ut, M
# the JSON of feshbach_blocks_arb.py (same keys and entry strings), written one row at a time
head = {"L": str(L), "N": N, "NP": NP, "K2": K2.str(30), "Amax": Amax.str(30), "tail_order": K,
        "tail_weights": [str(x) for x in pw], "Eco": Eco.str(30)}
with open(f"blocks_N{N}_NP{NP}.json", "w") as fo:
    fo.write(json.dumps(head)[:-1])
    for nm, Mx in (("A11", A11), ("G11", G11), ("CB", CB)):
        fo.write(f', "{nm}": [\n')
        for i in range(k):
            fo.write(('' if i == 0 else ',\n') + json.dumps([(Mx[i, j].str(70), "0") for j in range(k)]))
        fo.write(']')
    fo.write('}\n')
A = np.array(mid(A11)); G = np.array(mid(G11)); C = np.array(mid(CB))
ev, U = eigh(A, G); print("A11 gen eig:", ev[:4])
u0 = U[:, 0]; print("C_B on bottom:", (u0 @ C @ u0))
print("max radius A11:", max(float(A11[i, j].rad()) for i in range(k) for j in range(k)),
      " CB:", max(float(CB[i, j].rad()) for i in range(k) for j in range(k)))
tick('end')
