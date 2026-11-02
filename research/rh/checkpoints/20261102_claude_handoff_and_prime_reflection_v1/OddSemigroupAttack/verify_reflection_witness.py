"""Direct Arb check of a positive mixed entry in the ACTUAL odd Weil block.

This does not test the sign of a diagonal quadratic value or claim RH.
The ordinary smooth counterexample is proved in the accompanying manuscript.
"""
from pathlib import Path
from math import factorial
import argparse
import hashlib
import json
import flint
from flint import arb, acb, ctx, fmpq, fmpq_poly

def require(ok, message):
    if not ok:
        raise ValueError(message)

parser=argparse.ArgumentParser()
parser.add_argument('denominator',type=int,choices=(1000,2000))
parser.add_argument('output',type=Path)
args=parser.parse_args()
require(not args.output.exists(),'refusing to overwrite receipt')
ctx.prec=800
delta=arb(1)/args.denominator
d=arb(2).log(); x0=d/3; y0=2*d/3
require(0<x0-delta and y0+delta<arb(1)/2,'support containment fails')
require(d/3-2*delta>arb(1)/5 and d+2*delta<1,'support separation fails')
require(arb(2)<arb(1).exp() and arb(1).exp()<3,'prime cutoff not isolated')

v=fmpq_poly([1,0,-1]); t=fmpq_poly([0,1]); right=fmpq_poly([1,-1])
primitive=(v*v).integral()
norm=primitive(fmpq(1))-primitive(fmpq(-1))
require(norm==fmpq(16,15),'exact bump norm identity fails')
rho=fmpq_poly([0]); derivative=v
for k in range(v.degree()+1):
    p=(v*derivative).integral()
    rho+=(p(right)-p(fmpq(-1)))*t**k/factorial(k)
    derivative=derivative.derivative()
require(rho(0)==norm and rho(2)==0,'exact correlation identities fail')

def evaluate(poly,z):
    result=acb(0)
    for k in range(poly.degree(),-1,-1):
        result=result*z+arb(poly[k].p)/poly[k].q
    return result

settings=dict(rel_tol=arb(2)**-700,abs_tol=arb(2)**-700,
              deg_limit=100,eval_limit=100000,depth_limit=40)
def kernel(z):
    return (z/2).exp()/z.sinh()
def arch_peak(center):
    return delta*acb.integral(
        lambda z,analytic: evaluate(rho,z)*15/16*
        (kernel(center+delta*z)+kernel(center-delta*z)),0,2,**settings)

arch=-arch_peak(d/3)+arch_peak(d)
moment=acb.integral(lambda z,analytic: 2*(1-z*z)*(delta*z/2).cosh(),0,1,**settings)
polar=-8*(arb(15)*delta/16)*(x0/2).sinh()*(y0/2).sinh()*moment**2
prime=arb(2).sqrt()*d
require(arch.is_finite() and polar.is_finite() and arch.imag.contains(0) and polar.imag.contains(0),
        'integrals not finitely enclosed')
mixed=arch.real+polar.real+prime
require(mixed>arb(1)/2,'positive mixed entry not certified')
require(abs(arch.real)<40*delta and abs(polar.real)<64*delta,'ordinary uniform estimates contradicted')
def exact_upper(q):
    b=q.upper().fmpq();return [str(b.p),str(b.q)]
def exact_lower(q):
    b=q.lower().fmpq();return [str(b.p),str(b.q)]
report=dict(schema='AEGIS_ODD_PRIME_REFLECTION_REPLAY_V1',
            checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            python_flint=flint.__version__,arb_precision=ctx.prec,
            delta=['1',str(args.denominator)],centers=['log(2)/3','2*log(2)/3'],
            half_width=['1','2'],bump='sqrt(15/16)*(1-u^2) on [-1,1], zero outside',
            exact_bump_norm=['16','15'],complete_prime_power_indices=[2],
            exact_prime_mixed_contribution='sqrt(2)*log(2)',
            archimedean_mixed=arch.real.str(70),polar_mixed=polar.real.str(70),
            full_mixed_value=mixed.str(70),exact_dyadic_lower=exact_lower(mixed),
            exact_dyadic_upper=exact_upper(mixed),full_mixed_strictly_above_half=True,
            form='complete Weil form including both poles',moment_zero=False,
            domain='odd H^1 bump test; smooth universal proof separate',
            falsified_candidate='positivity preservation of the odd half-line semigroup',
            not_claimed=['negative diagonal','failure of PSD','RH counterexample','Lean theorem'],
            rh_proven=False)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
