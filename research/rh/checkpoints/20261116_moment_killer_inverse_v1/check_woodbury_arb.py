# Arb: G11 = Z^H Z of feshbach_arb_v2 (L = 9/5, N = 400, piv = [0, 1]); G11.inv() vs Woodbury with the
# closed-form real pivots c0(m) = (m-1)/4/(1/4 + k m^2), c1(m) = -m (1/4 + k)/(1/4 + k m^2), k = (2 pi/L)^2.
import time, sys
from flint import arb, acb, arb_mat, acb_mat, ctx
ctx.prec = int(sys.argv[1]) if len(sys.argv) > 1 else 200
L = arb(9) / 5; N = 400; pi = arb.pi()
band = list(range(-N, N + 1)); piv = [0, 1]; rest = [m for m in band if m not in piv]; k = len(rest)
def mom(m, s): a = acb(s, 2 * pi * m / L); return ((a * L).exp() - 1) / a
t0 = time.time()
Cp = acb_mat([[mom(m, s) for m in piv] for s in (arb('0.5'), arb('-0.5'))]); Cpinv = Cp.inv()
Ucode = acb_mat(2, k)
for j, m in enumerate(rest):
    sol = Cpinv * acb_mat([[-mom(m, arb('0.5'))], [-mom(m, arb('-0.5'))]])
    Ucode[0, j] = sol[0, 0]; Ucode[1, j] = sol[1, 0]
kap = (2 * pi / L) ** 2; q = arb(1) / 4
Ucf = arb_mat(2, k)
for j, m in enumerate(rest):
    Ucf[0, j] = (m - 1) * q / (q + kap * m * m); Ucf[1, j] = -m * (q + kap) / (q + kap * m * m)
ok = all(acb(Ucf[i, j]).overlaps(Ucode[i, j]) for i in range(2) for j in range(k))
print('closed form overlaps the code pivots:', ok, ' (%.1fs)' % (time.time() - t0), flush=True)
# G11 = I + U^T U (real), direct inverse vs Woodbury
G = arb_mat(k, k)
for i in range(k):
    for j in range(k):
        G[i, j] = Ucf[0, i] * Ucf[0, j] + Ucf[1, i] * Ucf[1, j] + (1 if i == j else 0)
t1 = time.time(); Gi = G.inv(); td = time.time() - t1
t1 = time.time()
S2 = arb_mat([[(1 if a == b else 0) + sum((Ucf[a, j] * Ucf[b, j] for j in range(k)), arb(0)) for b in range(2)] for a in range(2)])
S2i = S2.inv(); W = Ucf.transpose() * S2i * Ucf
Gw = arb_mat(k, k)
for i in range(k):
    for j in range(k): Gw[i, j] = (1 if i == j else 0) - W[i, j]
tw = time.time() - t1
ov = all(Gi[i, j].overlaps(Gw[i, j]) for i in range(0, k, 7) for j in range(0, k, 7))
rd = max(float(Gi[i, j].rad()) for i in range(0, k, 7) for j in range(0, k, 7))
rw = max(float(Gw[i, j].rad()) for i in range(0, k, 7) for j in range(0, k, 7))
print('prec %d: direct inv %.1fs, Woodbury %.1fs; enclosures overlap: %s; max radius direct %.3e, Woodbury %.3e' % (ctx.prec, td, tw, ov, rd, rw))
