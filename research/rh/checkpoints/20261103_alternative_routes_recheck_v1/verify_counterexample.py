"""Exact falsifier of a generic Li-positivity bridge, not of RH.

Compare the Gaussian-rational zero sum with independent formal division
of the logarithmic derivative of the explicit polynomial's Mobius pullback.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

def require(ok,message):
    if not ok:raise ValueError(message)
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def inv(a):
    d=a[0]*a[0]+a[1]*a[1]
    require(d>0,'zero complex inverse')
    return(a[0]/d,-a[1]/d)
def convolution(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def encoded(q):return[str(q.numerator),str(q.denominator)]

parser=argparse.ArgumentParser()
parser.add_argument('output_dir',type=Path)
args=parser.parse_args()
args.output_dir.mkdir(exist_ok=False)
results=[]
for height,expected in ((1,6),(20,125)):
    h=Q(height)
    plus=[Q(x) for x in (1,4,6,4,1)]
    minus=[Q(x) for x in (1,-4,6,-4,1)]
    middle=[Q(x) for x in (1,0,-2,0,1)]
    P=[16*plus[i]+128*(h*h-Q(1,16))*middle[i]
       +256*(h*h+Q(1,16))**2*minus[i] for i in range(5)]
    require(P[0]>0,'pullback has zero constant')
    derivative=[(i+1)*P[i+1] for i in range(4)]
    A=convolution(derivative,[Q(1),Q(-1)])
    A=[A[i]+4*P[i] for i in range(5)]
    B=convolution(P,[Q(1),Q(-1)])
    coefficients=[]
    for n in range(expected):
        value=(A[n] if n<len(A) else Q(0))
        value-=sum((B[j]*coefficients[n-j] for j in range(1,min(n,len(B)-1)+1)),Q(0))
        coefficients.append(value/B[0])

    rho=(Q(1,4),h);rho_inv=inv(rho)
    w=(1-rho_inv[0],-rho_inv[1]);w_inverse=inv(w)
    u=v=(Q(1),Q(0));zero_values=[]
    for m in range(1,expected+1):
        u=mul(u,w);v=mul(v,w_inverse)
        zero_values.append(4-2*(u[0]+v[0]))
    require(coefficients==zero_values,'zero formula and direct pullback division disagree')
    require(all(x>0 for x in coefficients[:-1]),'claimed initial positive prefix fails')
    require(coefficients[-1]<0,'negative counterexample not established')
    if height==1:
        require(P==[425,-1092,1590,-1092,425],'explicit polynomial mismatch')
        require(coefficients[-1]==Q(-309804177801344,5892961181640625),'exact negative coefficient mismatch')
    results.append(dict(height=height,roots=['1/4+ib','1/4-ib','3/4+ib','3/4-ib'],
                        first_negative_Li_index=expected,provider_taylor_index=expected-1,
                        strict_positive_prefix=expected-1,
                        negative_coefficient=encoded(coefficients[-1]),
                        exact_pullback_polynomial=[encoded(x) for x in P],
                        all_compared_coefficients=[encoded(x) for x in coefficients],
                        two_exact_methods_agree=True))
report=dict(schema='AEGIS_GENERIC_LI_BRIDGE_FALSIFIER_V1',
            checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            exact_arithmetic='Python fractions.Fraction; no floating-point decisions',
            cases=results,falsified='generic analytic-properties producer of all Li signs',
            actual_zeta_redefined=False,provider_criterion_refuted=False,
            full_analytic_kernel_verification=False,rh_proven=False)
(args.output_dir/'EXACT_COUNTEREXAMPLE_RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
for d in results:
    print('b=',d['height'],'positive prefix=',d['strict_positive_prefix'],
          'negative Li index=',d['first_negative_Li_index'])
