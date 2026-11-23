"""Certified upper bound for lambda0_a: an explicit moment-zero v with QW(v)/||v||^2 <= bound.

certify.py with one change: the printed CERTIFIED_UPPER_BOUND is the upper endpoint of the enclosure R
rounded UP to six significant decimal digits, in exact rational arithmetic (certify.py printed
R.upper().str(6), which rounds to nearest and at a = 3/4 and a = 3/2 lies below the enclosure).

v = D0 psi = psi/4 - psi'' with psi(x) = (1 - (x/a)^2)^2 p(x/a), p a polynomial, so psi and psi'
vanish at +-a and both log moments of v vanish exactly (integration by parts). Every term of
QW(v) (pole, archimedean, primes n <= e^{2a}) is evaluated in arb ball arithmetic: exact rational
Legendre data, rigorous integrals (acb.integral) of analytic integrands. The coefficients of p are
rationals chosen numerically; any choice gives a valid upper bound for the infimum.
Usage: python3 certify.py a_num a_den K"""
import sys, pickle, mpmath as mp
from flint import arb, acb, fmpq, fmpq_poly, ctx
sys.path.insert(0, '.')
from qwhp import legendre_polys, rho_table

ctx.prec = 800
an, ad, K = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
aq = fmpq(an, ad); A = arb(an) / ad
N = K + 4
P = legendre_polys(N)
rho = rho_table(48 if N <= 48 else N)

def legendre_coeffs(poly):
    out = []
    for j in range(N):
        F = (poly * P[j]).integral()
        out.append(fmpq(2 * j + 1, 2) * (F(fmpq(1)) - F(fmpq(-1))))
    return out

bump = fmpq_poly([1, 0, -1]) ** 2
T = []   # Legendre coefficients (in y = x/a) of v_k = psi_k/4 - psi_k''/a^2
for k in range(K):
    psi = bump * P[k]
    T.append(legendre_coeffs(psi * fmpq(1, 4) - psi.derivative().derivative() * (1 / (aq * aq))))

def q(x): return arb(x.p) / x.q
G = [A * 2 / (2 * j + 1) for j in range(N)]
sig = {(j, k): [(rho[(j, k)][m] if m < len(rho[(j, k)]) else fmpq(0)) + (rho[(k, j)][m] if m < len(rho[(k, j)]) else fmpq(0))
                for m in range(max(len(rho[(j, k)]), len(rho[(k, j)])))] for j in range(N) for k in range(N)}
deg = max(len(s) for s in sig.values())
I = acb(0, 1)
mu = [None] + [acb.integral(lambda z, _, m=m: z ** (m - 1) * (A * z / 2).exp() / (2 * (I * A * z).sinc()), 0, 2).real
               for m in range(1, deg)]
nu = acb.integral(lambda z, _: (z / 4).exp() * (I * z / 4).sinc() / (4 * (I * z).sinc()), 0, 2 * A).real
def mom(c):
    return [A * acb.integral(lambda z, _, k=k: sum((acb(q(P[k][i])) * z ** i for i in range(P[k].degree() + 1)), acb(0))
                             * (c * A * z).exp(), -1, 1).real for k in range(N)]
mp_, mm_ = mom(arb(1) / 2), mom(-arb(1) / 2)
def vm(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return arb(p).log() if m == 1 else None
primes = [(n, vm(n)) for n in range(2, int(mp.floor(mp.e ** (2 * an / ad))) + 1)]
primes = [(n, l) for n, l in primes if l is not None]
const = arb(4 * arb.pi()).log() + arb.const_euler() + A.tanh().log()
Q = [[None] * N for _ in range(N)]
for j in range(N):
    for k in range(j, N):
        s = sig[(j, k)]
        arch = sum((A * q(s[m]) * mu[m] for m in range(1, len(s))), arb(0)) + (2 * G[j] * nu if j == k else arb(0))
        WR = (const * G[j] if j == k else arb(0)) + arch
        pr = arb(0)
        for n, l in primes:
            x = arb(n).log() / A
            pr += l / arb(n).sqrt() * A * sum((q(s[m]) * x ** m for m in range(len(s))), arb(0))
        Q[j][k] = Q[k][j] = mp_[j] * mm_[k] + mm_[j] * mp_[k] - WR - pr

# numerical choice of p (mpmath generalized eigenproblem in the D0-psi space), then rounded to rationals
mp.mp.dps = 120
Qm = mp.matrix(N, N); Gm = mp.matrix(N, N)
for j in range(N):
    Gm[j, j] = mp.mpf(G[j].mid().str(100, radius=False))
    for k in range(N): Qm[j, k] = mp.mpf(Q[j][k].mid().str(100, radius=False))
Tm = mp.matrix([[mp.mpf(int(T[k][j].p)) / int(T[k][j].q) for j in range(N)] for k in range(K)])
QQ, GG = Tm * Qm * Tm.T, Tm * Gm * Tm.T
L = mp.cholesky(GG); Li = mp.inverse(L)
E, V = mp.eigsy(Li * QQ * Li.T)
i0 = min(range(K), key=lambda i: E[i])
d = Li.T * V[:, i0]
dq = [fmpq(int(mp.nint(d[k] * mp.mpf(10) ** 60)), 10 ** 60) for k in range(K)]
c = [sum((dq[k] * T[k][j] for k in range(K)), fmpq(0)) for j in range(N)]
cq = [q(x) for x in c]
num = sum((cq[j] * Q[j][k] * cq[k] for j in range(N) for k in range(N)), arb(0))
den = sum((cq[j] ** 2 * G[j] for j in range(N)), arb(0))
R = num / den
m1 = sum((cq[j] * mp_[j] for j in range(N)), arb(0)); m2 = sum((cq[j] * mm_[j] for j in range(N)), arb(0))
print(f'a={an}/{ad} K={K} primes={[n for n, _ in primes]}')
print('moments of v (must contain 0):', m1.str(5), m2.str(5))
print('numerical min (float):', mp.nstr(E[i0], 8))
print('CERTIFIED QW(v)/||v||^2 =', R.str(12))
from fractions import Fraction


def decimal_up(x, digits=6):
    """The least d.ddddd * 10^e (digits significant digits) that is >= the exact arb x > 0."""
    m, e = x.man_exp()
    v = Fraction(int(m)) * (Fraction(2) ** int(e))
    assert v > 0
    k = len(str(v.numerator // v.denominator)) - 1 if v >= 1 else -len(str(v.denominator // v.numerator))
    while Fraction(10) ** k > v:
        k -= 1
    while Fraction(10) ** (k + 1) <= v:
        k += 1
    s = Fraction(10) ** (k - digits + 1)
    q = -((-v) // s)                       # ceil(v / s)
    if q == 10 ** digits:
        q, k = 10 ** (digits - 1), k + 1
    out = q * Fraction(10) ** (k - digits + 1)
    assert out >= v
    d = str(q)
    return f'{d[0]}.{d[1:]}e{k:+03d}' if k < 0 else f'{d[0]}.{d[1:]}e+{k:02d}'


ub = decimal_up(R.upper())
print('CERTIFIED_UPPER_BOUND lambda0_a <=', ub, '(rounded up)')
