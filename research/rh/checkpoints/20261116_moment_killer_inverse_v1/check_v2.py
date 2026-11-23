# Independent check of HOLON V2 claims 1-2 (own script, reads nothing downloaded).
import sympy as sp
t, s, a, b = sp.symbols('t s a b', real=True)
phi = sp.Function('phi')
# (1) psi(t) = int_{-oo}^t (1 - e^{s-t}) phi(s) ds  ==>  psi'' + psi' = phi  (Leibniz)
lo = sp.Symbol('lo')
psi = sp.Integral((1 - sp.exp(s - t)) * phi(s), (s, lo, t))
d1 = sp.diff(psi, t); d2 = sp.diff(d1, t)
print('(1) psi\'\'+psi\'-phi =', sp.simplify((d2 + d1 - phi(t)).doit()))
# beyond the support: psi(t) = M0 - e^{-t} M1 (explicit tail when a moment is nonzero)
M0, M1 = sp.symbols('M0 M1')
print('    tail for t > b: M0 - exp(-t)*M1  -> compact iff M0 = M1 = 0')
# (1b) concrete: psi0 = (1-t^2)^5 on [-1,1], phi = psi0'' + psi0' ; recover psi0 by the formula
p0 = (1 - t**2)**5
f = sp.expand(sp.diff(p0, t, 2) + sp.diff(p0, t))
print('    moments of phi:', sp.integrate(f, (t, -1, 1)), sp.simplify(sp.integrate(f*sp.exp(t), (t, -1, 1))))
rec = sp.integrate(((1 - sp.exp(s - t)) * f.subs(t, s)), (s, -1, t))
print('    recovered - psi0 on [-1,1]:', sp.simplify(rec - p0))
print('    psi at t = 1 (support end):', sp.simplify(rec.subs(t, 1)))
# complex example: psi0 = (1-t^2)^5 * exp(i*3*t)
pc = (1 - t**2)**5 * sp.exp(3*sp.I*t)
fc = sp.diff(pc, t, 2) + sp.diff(pc, t)
recc = sp.integrate(sp.expand((1 - sp.exp(s - t)) * fc.subs(t, s)), (s, -1, t))
print('    complex recovered - psi0:', sp.simplify(sp.expand(recc - pc)))
# (2) conjugation and energy identity
h = sp.Function('h')
T = lambda g: sp.diff(g, t, 2) + sp.diff(g, t)
print('(2) e^{t/2} T(e^{-t/2} h) - (h\'\' - h/4) =', sp.simplify(sp.exp(t/2)*T(sp.exp(-t/2)*h(t)) - (sp.diff(h(t), t, 2) - h(t)/4)))
# ||h''-h/4||^2 = ||h''||^2 + 1/2||h'||^2 + 1/16||h||^2 for compact real h: check on h = (1-t^2)^5
hh = (1 - t**2)**5
L = sp.integrate((sp.diff(hh, t, 2) - hh/4)**2, (t, -1, 1))
R = sp.integrate(sp.diff(hh, t, 2)**2 + sp.Rational(1, 2)*sp.diff(hh, t)**2 + sp.Rational(1, 16)*hh**2, (t, -1, 1))
print('    energy identity residual:', sp.simplify(L - R))
