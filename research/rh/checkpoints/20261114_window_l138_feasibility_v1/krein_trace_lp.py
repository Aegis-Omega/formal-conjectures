"""Feasibility mirror (float, untrusted) of the Krein slot of window_of_certificate_* (H hats, d boundary terms;
both empty in every Lean window so far) and of the exact prime symbol, for the trace T of the complement bound.
LP over the slack s(t) >= 0 on a grid (t >= 0; the certificate is even in t) and the correction coefficients:
   Wt(t) (S(t) - m) + sum_k a_k 2 h cos(t c_k) sinc^2(t h / 2) + 2 sum_{j <= JD} x_j t^j cs_j(tL) + Wt(t) s(t) >= 0,
S = h+(t) - sum_q a_q cos(t log q), Wt = (t^2 + 1/4)^2, L = LT + 1/100, hats = triangles of half-width h at +-c_k
with c_k - h >= L, cs_j = cos for even j and sin for odd j. The objective is the trace T = sum 2 dt s(t) TD(t),
TD = the trace_cells_k.py cell bound of dist^2(e_t, atoms) for the atoms |n| <= K. Printed: the Lean-chain slack
max(0, m + W - h+) ("hat-free"), the exact-symbol slack with no corrections, the LP ("hats" column, whatever
corrections were allowed), a tail check past XMAX and the slack maximized over a 50x finer grid in each cell;
kappa = (2 pi)^2 LT (m - T / 2 pi).
usage: krein_trace_lp.py LT K m1,m2,.. XMAX DT [NH] [HW] [|a| bound] [JD] [|x| bound]"""
import sys, math
from fractions import Fraction as F
import numpy as np
from scipy.special import digamma
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, diags

LTq, K = F(sys.argv[1]), int(sys.argv[2]); ms = [float(x) for x in sys.argv[3].split(',')]
XMAX, DT = float(sys.argv[4]), float(sys.argv[5])
NH = int(sys.argv[6]) if len(sys.argv) > 6 else 200
HW = float(sys.argv[7]) if len(sys.argv) > 7 else 0.02
AB = float(sys.argv[8]) if len(sys.argv) > 8 else 1e7
JD = int(sys.argv[9]) if len(sys.argv) > 9 else -1   # boundary terms t^j cs_j(tL), j <= JD
DB = float(sys.argv[10]) if len(sys.argv) > 10 else 1e3
LT = float(LTq); Lk = LT + 0.01; h = 2 * np.pi / LT
x, y = np.exp(-LT / 2), np.exp(LT / 2)
def lam(n):
    for p in range(2, n + 1):
        if n % p == 0:
            q = n
            while q % p == 0: q //= p
            return math.log(p) if q == 1 else 0.0
PP = [(math.log(n), 2 * lam(n) / math.sqrt(n)) for n in range(2, int(math.exp(LT)) + 1) if lam(n)]
W = sum(a for _, a in PP)
hp = lambda t: np.real(digamma(0.25 + 0.5j * t)) - math.log(math.pi)
Sx = lambda t: hp(t) - sum(a * np.cos(t * lq) for lq, a in PP)
# TD exactly as trace_cells_k.py, cells [t, t + DT]
nG00, nG11 = 1 - x ** 2, y ** 2 - 1
Dlo = x ** 2 + y ** 2 - 2 - LT ** 2
tb0 = (1 - x) ** 2 / LT * (2 / (h * (h * K))); tb1 = (y - 1) ** 2 / LT * (2 / (h * (h * K)))
rho0, rho1 = np.sqrt(tb0), np.sqrt(tb1)
r00, r11, r01 = rho0 ** 2, rho1 ** 2, rho0 * rho1
Den = Dlo - (nG00 * r11 + nG11 * r00 + 2 * LT * r01 + r00 * r11 + r01 * r01)
Yb0, Yb1 = 2 * (x + 1), 2 * (y + 1); A1, A2 = 1 + LT, LT - 1
def nc(u1, u2, v1, v2): return dict(p0=u1*u1+v1*v1, p2=u2*u2+v2*v2, q0=u1*v1, q2=u2*v2, r=u2*v1-u1*v2)
nc0 = nc((A1*y - x)/2, -A2*y - x, (y*y + A2)/2, y*y - A1); nc1 = nc((-A2*x - y)/2, y - A1*x, (x*x - A1)/2, -A2 - x*x)
def pm(xl, xh, yl, yh): return np.maximum(np.maximum(xl*yl, xl*yh), np.maximum(xh*yl, xh*yh))
def Pup(k, a, b, cl, ch, sl, sh):
    c1, c2 = -2*(k['q0'] + k['q2']*a*a), -2*(k['q0'] + k['q2']*b*b); r1, r2 = 2*k['r']*a, 2*k['r']*b
    return k['p0'] + k['p2']*b*b + pm(np.minimum(c1, c2), np.maximum(c1, c2), cl, ch) + pm(np.minimum(r1, r2), np.maximum(r1, r2), sl, sh)
def TDf(a, b):
    w = (b - a) * LT; cl, ch = np.cos(a*LT) - w, np.cos(a*LT) + w; sl, sh = np.sin(a*LT) - w, np.sin(a*LT) + w
    tail = 1/(h*(h*K - b)) + 1/(h*(h*K + a)); Aup = (2 - 2*cl)/LT*tail; al = np.sqrt(Aup)
    n0 = np.sqrt(Pup(nc0, a, b, cl, ch, sl, sh))/(a*a + .25); n1 = np.sqrt(Pup(nc1, a, b, cl, ch, sl, sh))/(a*a + .25)
    d0 = nG11*al*rho0 + r11*Yb0 + r11*al*rho0 + LT*al*rho1 + r01*Yb1 + r01*al*rho1
    d1 = nG00*al*rho1 + r00*Yb1 + r00*al*rho1 + LT*al*rho0 + r01*Yb0 + r01*al*rho0
    G2 = ((n0 + d0)**2 + (n1 + d1)**2)/Den**2
    eps = np.sqrt(G2*(tb0 + tb1)/np.maximum(Aup, 1e-300)) + 2.0**-20
    return (1 + eps)*Aup + (1 + 1/eps)*G2*(tb0 + tb1)
xg = np.arange(0, XMAX, DT); wg = (xg**2 + .25)**2
cc = Lk + HW + HW * np.arange(NH)
cols = [2*np.cos(xg*c)*np.sinc(xg*HW/(2*np.pi))**2*HW for c in cc]
bnd = [(-AB, AB)]*NH
for j in range(JD + 1):
    cols += [2*xg**j*(np.cos(xg*Lk) if j % 2 == 0 else np.sin(xg*Lk))]; bnd += [(-DB/(1+Lk)**j, DB/(1+Lk)**j)]
hb = np.array(cols).T; NC = hb.shape[1]
print('LT=%s K=%d hK=%.1f W=%.4f grid %d, %d hats [%.3f, %.3f] |a|<=%g, boundary j<=%d' % (LTq, K, h*K, W, len(xg), NH, cc[0] if NH else 0, cc[-1] if NH else 0, AB, JD))
for m in ms:
    g = wg*(Sx(xg) - m)
    ns = int(np.max(np.nonzero(g < 0)[0])) + 1 if (g < 0).any() else 1
    ns = min(ns + int(20 / DT), len(xg), int(np.searchsorted(xg, h*K - 1)))
    print('  m=%.2f: S < m up to t=%.1f, slack allowed to %.1f (hK %.1f)' % (m, xg[int(np.max(np.nonzero(g < 0)[0]))], xg[ns - 1], h*K))
    td = TDf(xg[:ns], xg[:ns] + DT)
    s0 = np.maximum(0, m + W - hp(xg[:ns])); T0 = (2*DT*s0*td).sum()
    s1 = np.maximum(0, m - Sx(xg[:ns])); T1 = (2*DT*s1*td).sum()
    print('  exact-S slack, no hats: T=%.4f gap=%.4f kappa=%.2f' % (T1, m - T1/(2*np.pi), (2*np.pi)**2*LT*(m - T1/(2*np.pi))))
    A = hstack([csr_matrix(-hb), csr_matrix((-wg[:ns], (np.arange(ns), np.arange(ns))), shape=(len(xg), ns))]).tocsr()
    lp = linprog(np.concatenate([np.zeros(NC), 2*DT*td]), A_ub=A, b_ub=g, bounds=bnd + [(0, None)]*ns, method='highs')
    if lp.status != 0:
        print('m=%.2f LP status %d %s' % (m, lp.status, lp.message)); continue
    s = lp.x[NC:]; T = lp.fun; last = xg[np.max(np.nonzero(s > 1e-9)[0])] if (s > 1e-9).any() else 0
    print('m=%.2f  hat-free T=%.4f gap=%.4f kappa=%.2f |  hats T=%.4f gap=%.4f kappa=%.2f  slack to %.1f  max|a| %.2e' % (
        m, T0, m - T0/(2*np.pi), (2*np.pi)**2*LT*(m - T0/(2*np.pi)), T, m - T/(2*np.pi), (2*np.pi)**2*LT*(m - T/(2*np.pi)),
        last, np.abs(lp.x[:NC]).max()), flush=True)
    dco = lp.x[NH:NC]
    if len(dco):
        xt = np.array([XMAX * f for f in (1, 2, 4, 16, 256)])
        lhs = (xt**2 + .25)**2 * (hp(xt) - W - m)
        rhs = sum(2*abs(dco[j])*xt**j for j in range(JD + 1)) + 2*HW*np.abs(lp.x[:NH]).sum()
        print('    tail check t = XMAX*(1,2,4,16,256): worst-case lhs/rhs', ' '.join('%.3g' % v for v in lhs/rhs))
    # within-cell check: needed slack max over a 50x finer grid in each cell, then the cell trace
    SUB = 50; xf = (xg[:ns, None] + DT * np.arange(SUB + 1)[None, :] / SUB).ravel()
    Ff = (xf**2 + .25)**2 * (Sx(xf) - m)
    Ff += sum(lp.x[i] * 2*np.cos(xf*cc[i])*np.sinc(xf*HW/(2*np.pi))**2*HW for i in range(NH))
    for jj in range(JD + 1):
        Ff += lp.x[NH + jj] * 2*xf**jj*(np.cos(xf*Lk) if jj % 2 == 0 else np.sin(xf*Lk))
    need = np.maximum(0, -Ff / (xf**2 + .25)**2).reshape(ns, SUB + 1).max(axis=1)
    Tc = (2*DT*need*td).sum()
    print('    cell-max slack (x%d finer): T=%.4f gap=%.4f kappa=%.2f  (grid-point T %.4f)' % (SUB, Tc, m - Tc/(2*np.pi), (2*np.pi)**2*LT*(m - Tc/(2*np.pi)), T))
    np.save('sol_%s_%d_%.2f.npy' % (str(LTq).replace('/', '_'), K, m), lp.x[:NC])
