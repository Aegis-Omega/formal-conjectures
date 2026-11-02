"""Verify that the actual reflected-prime obstruction survives BOTH moments."""
from pathlib import Path
import argparse
import hashlib
import json
from math import factorial
import sys
import flint
from flint import arb, acb, ctx, fmpq, fmpq_poly

root=Path(__file__).parent
sys.path.insert(0,str(root.parent/'ClaudeHandoffReview'))
from check_exact_witness import evaluate, require

parser=argparse.ArgumentParser()
parser.add_argument('denominator',type=int,choices=(1000,2000))
parser.add_argument('output',type=Path)
args=parser.parse_args()
require(not args.output.exists(),'refusing to overwrite receipt')
ctx.prec=800
delta_q=fmpq(1,args.denominator);delta=arb(1)/args.denominator
psi=fmpq_poly([1,0,-1])**4
require(all(psi(x)==0 and psi.derivative()(x)==0 for x in (fmpq(-1),fmpq(1))),
        'clamped endpoint identity fails')
v=psi/4-psi.derivative().derivative()/(delta_q**2)
primitive=(v*v).integral(); norm=primitive(fmpq(1))-primitive(fmpq(-1))
require(norm>0,'nonpositive norm')
t=fmpq_poly([0,1]);right=fmpq_poly([1,-1]);rho=fmpq_poly([0]);derivative=v
for k in range(v.degree()+1):
    p=(v*derivative).integral()
    rho+=(p(right)-p(fmpq(-1)))*t**k/factorial(k)
    derivative=derivative.derivative()
require(rho(0)==norm and rho(2)==0,'exact correlation identity fails')
d=arb(2).log()
require(d*2/3+delta<arb(1)/2 and d/3-2*delta>arb(1)/5,'support/separation fails')
require(d+2*delta<arb(3).log(),'unexpected additional prime shift')
norm_ball=arb(norm.p)/norm.q
settings=dict(rel_tol=arb(2)**-700,abs_tol=arb(2)**-700,
              deg_limit=100,eval_limit=100000,depth_limit=40)
def kernel(z):return (z/2).exp()/z.sinh()
def peak(center):
    return delta*acb.integral(lambda z,analytic:
        evaluate(rho,z)/norm_ball*(kernel(center+delta*z)+kernel(center-delta*z)),0,2,**settings)
arch=-peak(d/3)+peak(d)
require(arch.is_finite() and arch.imag.contains(0),'nonfinite integral')
prime=arb(2).sqrt()*d
mixed=arch.real+prime
require(mixed>arb(9)/10,'moment-legal positive mixed entry not enclosed')
def integral_on_unit(poly):
    p=poly.integral();return p(fmpq(1))-p(fmpq(-1))
M=integral_on_unit(psi)
A=integral_on_unit(psi.derivative().derivative()**2)
B=integral_on_unit(psi.derivative()**2)
N=integral_on_unit(psi**2)
def ratball(q):return arb(q.p)/q.q
zpoly=fmpq_poly([0,1])
numerator=4*zpoly*(9+55*zpoly+31*zpoly**2+zpoly**3)
denominator=(1-zpoly)**5
first_num=numerator.derivative()*denominator-numerator*denominator.derivative()
second_num=(numerator.derivative().derivative()*denominator**2
            -numerator*denominator.derivative().derivative()*denominator
            -2*numerator.derivative()*denominator*denominator.derivative()
            +2*numerator*denominator.derivative()**2)
def transformed_kernel(t,second=False):
    z=(-2*t).exp();den=evaluate(denominator,z)
    R=evaluate(numerator,z)/den
    if not second:return (-t/2).exp()*R
    return (-t/2).exp()*(R/4+6*z*evaluate(first_num,z)/den**2
                         +4*z*z*evaluate(second_num,z)/den**3)
leading=2*ratball(M*M/A)*(transformed_kernel(d/3)-transformed_kernel(d))
delta0=arb(1)/1000
error_constant=(leading*(ratball(B/(2*A))+delta0**2*ratball(N/(16*A)))
                +8*ratball(M*M/A)*transformed_kernel(arb(1)/5,second=True))
require(leading>0 and error_constant>0,'asymptotic constants not positive')
residual=arch.real+leading*delta**5
require(abs(residual)<error_constant*delta**7,'explicit order-seven remainder fails')
bound=mixed.lower().fmpq()
exact_norm=delta_q*norm
report=dict(schema='AEGIS_MOMENT_LEGAL_REFLECTION_REPLAY_V1',
            checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            shared_helper_sha256=hashlib.sha256((root.parent/'ClaudeHandoffReview/check_exact_witness.py').read_bytes()).hexdigest(),
            python_flint=flint.__version__,arb_precision=ctx.prec,delta=['1',str(args.denominator)],
            potential='(1-u^2)^4 on [-1,1], zero outside',operator='1/4-d2/dx2',
            clamped_conditions_exact=True,moments_zero_by_exact_integration_by_parts=True,
            full_polar_term='exactly zero',prime_power_indices=[2],
            exact_prime_mixed_over_local_norm='sqrt(2)*log(2)',
            local_norm_squared=[str(exact_norm.p),str(exact_norm.q)],
            normalized_arch_mixed=arch.real.str(70),normalized_full_mixed=mixed.str(70),
            leading_order_five_coefficient=leading.str(60),
            explicit_order_seven_constant=error_constant.str(60),
            order_seven_error_bound_verified=True,
            exact_potential_mass=[str(M.p),str(M.q)],
            exact_potential_second_derivative_norm=[str(A.p),str(A.q)],
            exact_dyadic_lower=[str(bound.p),str(bound.q)],strict_lower=['9','10'],
            smooth_domain_bridge='ordinary clamped-potential approximation proof',
            not_claimed=['negative diagonal','failure of PSD','RH counterexample','Lean theorem'],
            rh_proven=False)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
