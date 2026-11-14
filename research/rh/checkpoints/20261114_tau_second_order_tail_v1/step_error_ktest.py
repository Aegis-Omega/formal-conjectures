import sympy as sp
X,Y,s,t=sp.symbols('X Y s t')
N=(7*X**5 + 7*X**4*Y - 31*X**4 - 10*X**3*Y**2 - 16*X**3*Y + 54*X**3 - 2*X**2*Y**3 + 26*X**2*Y**2 + 6*X**2*Y - 46*X**2 + 19*X*Y**4 + 40*X*Y**3 - 22*X*Y**2 + 8*X*Y + 19*X + 11*Y**5 + 29*Y**4 + 26*Y**3 + 6*Y**2 - 5*Y - 3)
R=X+Y; E=X+Y-1; P=(X+Y+1)**2-4*X
# sanity: R2/w = -2N/(3 R E^3 P^2)
c,w=sp.symbols('c w',positive=True)
Ec=c**2-1+w**2; Rc=c**2+w**2; Rm=(c-1)**2+w**2; Rp=(c+1)**2+w**2; v=2*w/Ec
R2=v-v**3/3-2*w/Rc-(c-1)*w/(3*Rm**2)+(c+1)*w/(3*Rp**2)
chk=sp.simplify(R2/w + 2*N.subs({X:c**2,Y:w**2})/(3*Rc*Ec**3*(Rm*Rp)**2))
print('identity check',chk)
for X0 in [4]:
  for K in [sp.Rational(14,3),5,6,8,10,12,16,20]:
    low=sp.expand((3*K*E**3*P**2 - 2*N*R**2).subs({X:X0+s,Y:1+t}))
    up=sp.expand((15*K*E**5*P**2 + 10*N*R**2*E**2 - 96*Y**2*R**3*P**2).subs({X:X0+s,Y:1+t}))
    nl=[cf for cf in sp.Poly(low,s,t).coeffs() if cf<0]
    nu=[cf for cf in sp.Poly(up,s,t).coeffs() if cf<0]
    print(X0,K,'low neg coeffs',len(nl),'up neg coeffs',len(nu))
