import sympy as sp, mpmath as mp
c,w=sp.symbols('c w',positive=True)
E=c**2-1+w**2; R=c**2+w**2; Rm=(c-1)**2+w**2; Rp=(c+1)**2+w**2
v=2*w/E
R2=v-v**3/3-2*w/R-(c-1)*w/(3*Rm**2)+(c+1)*w/(3*Rp**2)
num,den=sp.fraction(sp.together(sp.simplify(R2/w)))
num=sp.expand(num); den=sp.factor(den)
print('den',den)
X,Y=sp.symbols('X Y')
pn=sp.Poly(num,c,w)
print('num degree',pn.total_degree(), 'terms',len(pn.terms()))
# check evenness
print('even in c?', sp.expand(num.subs(c,-c)-num)==0, 'even in w?', sp.expand(num.subs(w,-w)-num)==0)
numXY=sp.expand(num.subs({c:sp.sqrt(X),w:sp.sqrt(Y)}))
print('numXY', sp.Poly(numXY,X,Y).total_degree())
print(sp.factor(numXY))
# numeric scan of ratio |delta|*R^3/w
mp.mp.dps=50
def delta(cc,ww):
    cc=mp.mpf(cc);ww=mp.mpf(ww)
    E=cc**2-1+ww**2;R=cc**2+ww**2;Rm=(cc-1)**2+ww**2;Rp=(cc+1)**2+ww**2
    return mp.atan(2*ww/E)-(cc-1)*ww/(3*Rm**2)+(cc+1)*ww/(3*Rp**2)-2*ww/R
mx=0;arg=None
for cc in [2,2.5,3,4,5,7,10,15,20,30,50,100,300,1000,1e4,1e5]:
  for ww in [1,1.5,2,3,5,8,13,20,40,100,300,1000,1e4,1e5]:
    r=abs(delta(cc,ww))*(cc**2+ww**2)**3/ww
    if r>mx: mx=r;arg=(cc,ww)
print('max |delta| R^3/w',mx,arg)
