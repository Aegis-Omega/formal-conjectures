import sympy as sp, mpmath as mp
X,Y,s,t=sp.symbols('X Y s t')
N=(7*X**5 + 7*X**4*Y - 31*X**4 - 10*X**3*Y**2 - 16*X**3*Y + 54*X**3 - 2*X**2*Y**3 + 26*X**2*Y**2 + 6*X**2*Y - 46*X**2 + 19*X*Y**4 + 40*X*Y**3 - 22*X*Y**2 + 8*X*Y + 19*X + 11*Y**5 + 29*Y**4 + 26*Y**3 + 6*Y**2 - 5*Y - 3)
R=X+Y; E=X+Y-1; P=(X+Y+1)**2-4*X
lo=sp.expand((24*E**3*P**2 - 2*N*R**2).subs({X:s+4,Y:t+1}))
hi=sp.expand((120*E**5*P**2 + 10*N*R**2*E**2 - 96*Y**2*R**3*P**2).subs({X:s+4,Y:t+1}))
def lean(poly):
    terms=[]
    for (i,j),cf in sorted(sp.Poly(poly,s,t).terms()):
        assert cf>=0 and cf==int(cf)
        if cf==0: continue
        m=[str(int(cf))]
        if i: m.append('s' if i==1 else f's ^ {i}')
        if j: m.append('t' if j==1 else f't ^ {j}')
        terms.append(' * '.join(m))
    return ' + '.join(terms)
for name,p in [('lo',lo),('hi',hi)]:
    L=lean(p); print(name, len(sp.Poly(p,s,t).terms()), 'terms, maxcoef', max(abs(c) for c in sp.Poly(p,s,t).coeffs()))
    open(f'{name}.txt','w').write(L)
# numeric spot checks of the original step inequality with K=8
mp.mp.dps=40
def delta(cc,ww):
    cc=mp.mpf(cc);ww=mp.mpf(ww)
    E=cc**2-1+ww**2;R=cc**2+ww**2;Rm=(cc-1)**2+ww**2;Rp=(cc+1)**2+ww**2
    return mp.atan(2*ww/E)-(cc-1)*ww/(3*Rm**2)+(cc+1)*ww/(3*Rp**2)-2*ww/R
import random
random.seed(1);worst=0
for _ in range(20000):
    cc=2*10**random.uniform(0,5); ww=10**random.uniform(0,5)
    r=abs(delta(cc,ww))*(cc**2+ww**2)**3/(8*ww); worst=max(worst,r)
print('worst |delta|/(8w/R^3)',worst)
