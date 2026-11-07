# Exact-rational cell bound of the trace certificate (CvSTraceCellL65V1) with the window L as a parameter.
from fractions import Fraction as F
import math, mpmath as mp, sys, json
mp.mp.dps=40
piLo=F(314159265358979323846,10**20); piHi=F(314159265358979323847,10**20)
LQ=F(sys.argv[1]) if len(sys.argv)>1 else F(6,5)
mp.mp.dps=60
_e=mp.exp(-mp.mpf(LQ.numerator)/LQ.denominator/2)
e35Lo=F(int(mp.floor(_e*2**128))-1,2**128); e35Hi=F(int(mp.ceil(_e*2**128))+1,2**128)
assert mp.mpf(e35Lo.numerator)/e35Lo.denominator<_e<mp.mpf(e35Hi.numerator)/e35Hi.denominator
TWO64=2**64
def rdn(x): return F(math.floor(x*TWO64),TWO64)
def rup(x): return F(-math.floor(-x*TWO64),TWO64)
def sinPartial(x,n):
    s=F(0); 
    for i in range(n): s+=(-1)**i*x**(2*i+1)/math.factorial(2*i+1)
    return s
def sinLoQ(x): return sinPartial(x,14) if x>=0 else -sinPartial(-x,15)
def sinHiQ(x): return sinPartial(x,15) if x>=0 else -sinPartial(-x,14)
def mid(ul): return math.floor(ul+F(1,2))
def thLo(ul): m=mid(ul); return rdn(min(piLo*(ul-m),piHi*(ul-m)))
def thHi(ul,uh): m=mid(ul); return max(piLo*(uh-m),piHi*(uh-m))
def baseLo(ul,uh): return sinLoQ(thLo(ul))-(thHi(ul,uh)-thLo(ul))
def baseHi(ul,uh): return sinHiQ(thLo(ul))+(thHi(ul,uh)-thLo(ul))
def sinPiLo(ul,uh): return baseLo(ul,uh) if mid(ul)%2==0 else -baseHi(ul,uh)
def sinPiHi(ul,uh): return baseHi(ul,uh) if mid(ul)%2==0 else -baseLo(ul,uh)
def mlo(x1,x2,y1,y2): return min(min(x1*y1,x1*y2),min(x2*y1,x2*y2))
def mhi(x1,x2,y1,y2): return max(max(x1*y1,x1*y2),max(x2*y1,x2*y2))
xL,xH=e35Lo,e35Hi; yL,yH=1/e35Hi,1/e35Lo
hL=2*piLo/LQ
nG00=1-xL**2; nG11=yH**2-1
Dlo=xL**2+yL**2-2-LQ*LQ
tb0=rup((1-xL)**2*(1/LQ)*(2/(hL*(hL*70))))
tb1=rup((yH-1)**2*(1/LQ)*(2/(hL*(hL*70))))
def sqrt_up(q,den=2**40):
    r=F(math.isqrt(int(q*den*den))+1,den)
    assert r*r>=q
    return r
rho0=sqrt_up(tb0); rho1=sqrt_up(tb1)
r00,r11,r01=rho0**2,rho1**2,rho0*rho1
ddQ=nG00*r11+nG11*r00+LQ*r01+LQ*r01+r00*r11+r01*r01
Den=Dlo-ddQ
Yb0=2*(xH+1); Yb1=2*(yH+1)
def NC(u1,u2,v1,v2):
    return dict(p0=rup(mhi(*u1,*u1)+mhi(*v1,*v1)), p2=rup(mhi(*u2,*u2)+mhi(*v2,*v2)),
        q0l=rdn(mlo(*u1,*v1)), q0h=rup(mhi(*u1,*v1)), q2l=rdn(mlo(*u2,*v2)), q2h=rup(mhi(*u2,*v2)),
        rl=rdn(mlo(*u2,*v1)-mhi(*u1,*v2)), rh=rup(mhi(*u2,*v1)-mlo(*u1,*v2)))
nc0=NC((((1+LQ)*yL-xH)/2,((1+LQ)*yH-xL)/2),(-(LQ-1)*yH-xH,-(LQ-1)*yL-xL),((yL**2+(LQ-1))/2,(yH**2+(LQ-1))/2),(yL**2-(1+LQ),yH**2-(1+LQ)))
nc1=NC(((-(LQ-1)*xH-yH)/2,(-(LQ-1)*xL-yL)/2),(yL-(1+LQ)*xH,yH-(1+LQ)*xL),((xL**2-(1+LQ))/2,(xH**2-(1+LQ))/2),(-(LQ-1)-xH**2,-(LQ-1)-xL**2))
def ul(a): return a*LQ/piHi
def uh(b): return b*LQ/piLo
def trig(a,b):
    return (rdn(sinPiLo(ul(a)+F(1,2),uh(b)+F(1,2))), rup(sinPiHi(ul(a)+F(1,2),uh(b)+F(1,2))),
            rdn(sinPiLo(ul(a),uh(b))), rup(sinPiHi(ul(a),uh(b))))
def tailQ(a,b): return 1/(hL*(hL*70-b))+1/(hL*(hL*70+a))
def Pup(k,a,b,cl,ch,sl,sh):
    Ql=k['q0l']+mlo(k['q2l'],k['q2h'],a*a,b*b); Qh=k['q0h']+mhi(k['q2l'],k['q2h'],a*a,b*b)
    RTl=mlo(k['rl'],k['rh'],a,b); RTh=mhi(k['rl'],k['rh'],a,b)
    return k['p0']+k['p2']*b*b+mhi(-2*Qh,-2*Ql,cl,ch)+mhi(2*RTl,2*RTh,sl,sh)
W=float(F(0))  # placeholder
def hplus(t): return float(mp.re(mp.digamma(mp.mpf(1)/4+0.5j*mp.mpf(t))))-float(mp.log(mp.pi))
w2w3=float(mp.sqrt(2)*mp.log(2)+2*mp.log(3)/mp.sqrt(3))
def mkcell(a,b,m):
    cl,ch,sl,sh=trig(a,b)
    assert abs(thLo(ul(a)))<=2 and abs(thLo(ul(a)+F(1,2)))<=2
    A=(2-2*cl)*(1/LQ)*tailQ(a,b)
    al=sqrt_up(A,2**32)
    n=[]
    for k in (nc0,nc1):
        P=Pup(k,a,b,cl,ch,sl,sh)
        P=max(P,F(0))
        n.append(sqrt_up(P/((a*a+F(1,4))**2),2**32))
    f0,f1=al*rho0,al*rho1
    d0=nG11*f0+r11*Yb0+r11*f0+LQ*f1+r01*Yb1+r01*f1
    d1=nG00*f1+r00*Yb1+r00*f1+LQ*f0+r01*Yb0+r01*f0
    G2=((n[0]+d0)**2+(n[1]+d1)**2)/Den**2
    B=G2*(tb0+tb1)
    if A>0:
        e=math.sqrt(float(B/A)); eps=F(max(1,round(e*2**20)),2**20)
    else: eps=F(2**20)
    TD=rup((1+eps)*A+(1+1/eps)*B)
    sv=m+w2w3-hplus(float(a))+1e-6
    s=F(max(0,math.ceil(sv*2**20)),2**20)
    return dict(a=a,b=b,s=s,eps=eps,al=al,n0=n[0],n1=n[1],TD=TD)
def grid(spec):
    pts=[]
    for (lo,hi,st) in spec:
        x=lo
        while x<hi: pts.append(x); x+=st
    pts.append(spec[-1][1]); return list(zip(pts[:-1],pts[1:]))
if __name__=='__main__':
    m=F(sys.argv[2]) if len(sys.argv)>2 else F(3,2)
    g=int(sys.argv[3]) if len(sys.argv)>3 else 1
    import math as _m
    lo,hi=1.0,5000.0
    for _ in range(60):
        md=(lo+hi)/2
        lo,hi=(lo,md) if hplus(md)>=float(m)+w2w3 else (md,hi)
    top=F(_m.ceil(hi))
    assert float(top)<float(hL)*70, 'tail beyond 70h'
    spec=[(F(0),F(4),F(1,50*g)),(F(4),F(20),F(1,10*g)),(F(20),F(100),F(1,2*g)),(F(100),top,F(1,g))]
    cells=[mkcell(a,b,float(m)) for (a,b) in grid(spec)]
    T=sum(2*(c['b']-c['a'])*c['s']*c['TD'] for c in cells)
    gap=float(m)-float(T)/(2*_m.pi)
    print('L',LQ,'m',m,'grid',g,'cells',len(cells),'t*',float(top),'T',float(T),'gap',gap,'max kappa',(2*_m.pi)**2*float(LQ)*gap,'tail hplus',hplus(float(top)),'need',float(m)+w2w3)
