"""Source-bound Q96 interval experiment for the fixed L=6/5 Gram budget.
Float least squares proposes a rational projection only. All enclosures and
certificate validation use exact integers. This script is NOT a Lean proof
of the analytic enclosure or of the final RH/window obligations.
"""
import ast,hashlib,json,re,subprocess,time
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal,localcontext
import numpy as np
root=Path('/workspace/formal-conjectures/research/rh/feshbach_lean_v1')
out=Path('/workspace/aegis-row-budget-recovery');out.mkdir(exist_ok=True)
P=96;S=1<<P;N=139;NP=150
floor=lambda x:x.numerator//x.denominator
ceil=lambda x:-floor(-x)
def ev(n):
 if isinstance(n,ast.Constant) and type(n.value)==int:return F(n.value)
 if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -ev(n.operand)
 if isinstance(n,ast.BinOp):
  a,b=ev(n.left),ev(n.right)
  if isinstance(n.op,ast.Div):return a/b
  if isinstance(n.op,ast.Add):return a+b
  if isinstance(n.op,ast.Sub):return a-b
  if isinstance(n.op,ast.Mult):return a*b
 raise ValueError(ast.dump(n))
def table(module,name):
 s=(root/(module+'.lean')).read_text();m=re.search(r'def '+name+r' : List ℚ := \[(.*?)\]',s,re.S);assert m
 return [ev(n) for n in ast.parse('['+m[1]+']',mode='eval').body.elts]
def iv(a,b=None):
 if b is None:b=a
 return floor(a*S),ceil(b*S)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 x=[a[i]*b[j] for i in range(2) for j in range(2)];return min(x)//S,-((-max(x))//S)
def divint(a,d):
 if d<0:return neg(divint(a,-d))
 return a[0]//d,-((-a[1])//d)
def arr(rows):return tuple(np.array([[a[k] for a in r] for r in rows],dtype=object) for k in range(2))
def midrad(A):
 m=(A[0]+A[1])//2;return m,np.maximum(m-A[0],A[1]-m)
def mm(A,B):
 a,ar=midrad(A);b,br=midrad(B);c=a@b;rad=abs(a)@br+ar@abs(b)+ar@br
 return (c-rad)//S,-((-(c+rad))//S)
def scale(A,c):
 return arr([[mul((A[0][i,j],A[1][i,j]),c) for j in range(A[0].shape[1])] for i in range(A[0].shape[0])])
def plus(A,B):return A[0]+B[0],A[1]+B[1]
def minus(A,B):return A[0]-B[1],A[1]-B[0]
def tr(A):return A[0].T,A[1].T
def congr(A,G):return mm(tr(A),mm(G,A))
def emit(s):print(s,flush=True)
t0=time.monotonic();src=(root/'CvSProjectedPackedCertificateL12V1.lean').read_text()
rrows=re.findall(r'private def certRRow(\d+) : List ℤ :=\s*(\[[^\]]*\])',src)
irows=re.findall(r'private def certIRow(\d+) : List Iv :=\s*(\[[^\]]*\])',src)
assert len(rrows)==len(irows)==N
R=[ast.literal_eval(v) for k,v in rrows];I=[[(int(a),int(b)) for a,b in re.findall(r'⟨(-?\d+),\s*(-?\d+)⟩',v)] for k,v in irows]
assert all(len(v)==N for v in R+I)
pl=F(314159265358979323846,10**20);ph=F(314159265358979323847,10**20)
pi=iv(pl,ph);lp=iv(F(6,5)/ph,F(6,5)/pl)
tl=table('CvSTauPrimeL12V1','tauFLo')+table('CvSTauR1PrimeL12V1','tauFLoExtra')
th=table('CvSTauPrimeL12V1','tauFHi')+table('CvSTauR1PrimeL12V1','tauFHiExtra');assert len(tl)==len(th)==NP
T={0:(0,0)};T.update({k:iv(tl[k-1],th[k-1]) for k in range(1,NP+1)});T.update({-k:neg(T[k]) for k in range(1,NP+1)})
D=[iv(a,b) for a,b in zip(table('CvSDiagL12V1','diagLo'),table('CvSDiagL12V1','diagHi'))]
def r(n,i):return R[n+69][i] if -69<=n<=69 else 0
X=arr([[mul(iv(-F(25,9)*ph**2*n*n-F(1,4),-F(25,9)*pl**2*n*n-F(1,4)),iv(F(2*r(n,i)-r(n-1,i)-r(n+1,i),1<<42))) for i in range(N)] for n in range(-70,71)])
E=arr([[mul((2*pi[0],2*pi[1]),D[abs(n)]) if n==m else mul(lp,divint(sub(T[n],T[m]),n-m)) for n in range(-70,71)] for m in range(-NP,NP+1)])
Y=mm(E,X);xm,_=midrad(X);ym,_=midrad(Y);xf=np.array(xm,dtype=float)/S;yf=np.array(ym[NP-70:NP+71],dtype=float)/S
# Arbitrary exact rational witness: no correctness of floating fit is assumed.
qproj=48;fit=np.linalg.lstsq(xf,yf,rcond=None)[0];LI=np.array([[int(round(v*(1<<qproj))) for v in row] for row in fit],dtype=object)
Lam=(LI*(1<<(P-qproj)),LI*(1<<(P-qproj)))
Z=Y[0].copy(),Y[1].copy();inside=mm(X,Lam);Z[0][NP-70:NP+71]-=inside[1];Z[1][NP-70:NP+71]-=inside[0]
BF=mm(tr(Z),Z);emit('finite residual matrix enclosed')
H=[F(0)]
for k in range(1,NP+72):H.append(H[-1]+F(1,k))
def gu(n,m):
 return (1/(NP-n+F(1,2))+1/(NP+n+F(1,2))) if n==m else (H[NP-m]-H[NP-n]+H[NP+n]-H[NP+m])/(n-m)
G=arr([[iv(gu(n,m)) for m in range(-70,71)] for n in range(-70,71)])
DX=arr([[mul(T[n],(X[0][n+70,i],X[1][n+70,i])) for i in range(N)] for n in range(-70,71)])
BT=scale(plus(scale(congr(DX,G),iv(F(2))),scale(congr(X,G),iv(F(338)))),mul(lp,lp));emit('exact rational harmonic Gram tail enclosed')
B=plus(BF,BT);QI=arr([[(lo<<(P-64),hi<<(P-64)) for lo,hi in row] for row in I]);C=minus(scale(QI,iv(F(40))),B)
# Symmetric hull only widens enclosures, covering both original orientations.
C=np.minimum(C[0],C[0].T),np.maximum(C[1],C[1].T)
assert np.array_equal(C[0],C[0].T) and np.array_equal(C[1],C[1].T)
# Deterministic rational Cholesky witness, then exact Gershgorin verification.
cm,cr=midrad(C);q=80;assert q%2==0
with localcontext() as ctx:
 ctx.prec=100
 A=[[Decimal(int(cm[i,j]))/Decimal(S) for j in range(N)] for i in range(N)]
 # Gershgorin-safe requested margin, exact verifier below decides adequacy.
 eig_hint=float(np.linalg.eigvalsh(np.array(cm,dtype=float)/S)[0])
 eps=max(1,int(eig_hint*(1<<q)*3/4))
 emit('untrusted eigenvalue hint '+str(eig_hint))
 Chol=[[Decimal(0)]*N for _ in range(N)]
 for i in range(N):
  for j in range(i+1):
   v=A[i][j]-(Decimal(eps)/Decimal(1<<q) if i==j else 0)-sum(Chol[i][k]*Chol[j][k] for k in range(j))
   Chol[i][j]=v.sqrt() if i==j else v/Chol[j][j]
 L=np.array([[int((Chol[i][j]*Decimal(1<<(q//2))).to_integral_value()) if j<=i else 0 for j in range(N)] for i in range(N)],dtype=object)
# Outward rescale Q96 enclosures to Q80.
cl=C[0]//(1<<(P-q));ch=-((-C[1])//(1<<(P-q)));g=L@L.T+np.eye(N,dtype=object)*eps
err=np.maximum(ch-g,g-cl);rows=err.sum(axis=1);eta=int(max(rows));bound=max(abs(int(x)) for x in L.flat);bits=(N*N*4*bound*bound).bit_length()+1
emit('exact eps/eta '+str((eps,eta)))
assert eps>eta,(eps,eta)
data={'dimension':N,'fractional_bits':q,'base':1<<bits,'B':bound,'eps':eps,'eta':eta,'L':L.tolist(),'I':[[[int(cl[i,j]),int(ch[i,j])] for j in range(N)] for i in range(N)],'projection_fractional_bits':qproj,'projection':LI.tolist()}
(out/'ROW_BUDGET_DATA.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
rec={'status':'EXACT_INTEGER_FINITE_CERTIFICATE_PASS; analytic enclosure not yet formalized in Lean','source_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [root/n for n in ['CvSProjectedPackedCertificateL12V1.lean','CvSTauPrimeL12V1.lean','CvSTauR1PrimeL12V1.lean','CvSDiagL12V1.lean','CvSGramTailV1.lean','CvSRowTailV1.lean']]},'dimension':N,'NP':NP,'kappa':40,'epsilon':1,'tau_far_bound':13,'row_budget':'40 R^T Q_actual R - (finite residual Gram + Gram tail) with chosen rational projection','arithmetic':'Q96 outward exact integer midpoint-radius matrix products; exact rational harmonic G; Q80 outward final enclosure','certificate':{k:data[k] for k in ['base','B','eps','eta']},'margin_numerator':eps-eta,'margin_denominator':1<<q,'maximum_interval_radius_q96':int(np.max(cr)),'floating_point_use':'Least-squares proposes the rational projection; an eigenvalue hint proposes the shift; Decimal Cholesky proposes the integer factor; all acceptance uses exact integers.','seconds':time.monotonic()-t0,'remaining_Lean_obligation':'Prove correspondence and outward enclosure for the actual residual/tail form, then apply packed soundness; original-function projection defined by basis surjectivity.'}
(out/'ROW_BUDGET_EXACT_RECEIPT.json').write_text(json.dumps(rec,indent=2)+'\n');emit(json.dumps(rec,indent=2))
