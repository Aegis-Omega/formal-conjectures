#!/usr/bin/env python3
"""Exact scalar test reusing the existing rational logarithm backend.

The analytic digamma sum/integral estimate is derived in DEFECT_TAIL.md,
not claimed as a Lean theorem or as established by finite testing.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, sys, datetime
ROOT=Path(__file__).resolve().parent
BACKEND=Path('/workspace/aegis-rh-next-local-20261028/signed_covariance_continuum_20261030')
sys.path.insert(0,str(BACKEND))
from rational_core import log, require
SOURCES=[
 Path('/workspace/formal-conjectures/research/rh/krein_ring_v1/RHKreinZetaBridgeV3.lean'),
 Path('/workspace/formal-conjectures/research/rh/feshbach_lean_v1/CvSDigammaSeriesV1.lean'),
 Path('/workspace/formal-conjectures/AEGISOverlay/RHKreinDigammaLowerBoundV1.lean'),
 Path('/workspace/formal-conjectures/research/rh/consolidated_v1/src/RHEulerGammaV13.lean'),
 BACKEND/'rational_core.py',
]
def main():
    l2=log(Q(2))
    require(l2.lo>Q(1,2),'coarse log2 bound')
    require(2*l2.lo>Q(11,8),'M=3 support cutoff validity for width11/8')
    s=Q(2);u=2**64;M=3
    F=Q(1,s)*((s*s*u*u+Q(1,4))/(u*u+Q(1,4)))**2
    F_lo=Q(289,50)
    require(F>=F_lo,'scaled multiplier lower bound')
    A_bound=Q(M*(M+1))
    # For t>=2, the ordinary series-integral estimate gives
    # log(t)-6-A <= S_M(t) <= log(t)+2+A.
    # log(2u)>=log(u), log(u)>=64*log(2)>32.
    coarse= (F_lo-1)*32-F_lo*(6+A_bound)-(2+A_bound)
    sharp=(F_lo-1)*(64*l2.lo)-F_lo*(6+A_bound)-(2+A_bound)
    require(coarse==Q(873,25) and sharp>coarse>0,'positive actual-symbol defect bound')
    cases=[]
    for scale in [Q(11,10),Q(3,2),Q(2),Q(3)]:
        lower=scale;upper=1/scale**3
        require(lower>upper,'normalization contradiction')
        cases.append({'s':str(scale),'zero_frequency_requires_c_squared_at_least':str(lower),
                      'tail_requires_c_squared_at_most':str(upper),'compatible':False})
    # Positive control: identity scale has the same necessary scalar bound.
    require(Q(1)==1/Q(1)**3,'identity control')
    rejected=[]
    for label,fn in [
      ('unscaled pointwise defect nonpositive at all frequencies',lambda:require(coarse<=0,'strictly positive certified ordinary lower bound')),
      ('c_squared=s repairs both zero frequency and tail',lambda:require(s*s**3<=1,'tail coefficient is s^4-1>0')),
      ('c_squared=s^-3 repairs both zero frequency and tail',lambda:require(1/s**3>=s,'zero-frequency negative symbol forces c^2>=s'))]:
        try: fn()
        except ValueError as e:rejected.append({'candidate':label,'rejected':True,'reason':str(e)})
        else:raise ValueError('false candidate accepted')
    result={'status':'EXACT_DEFECT_TAIL_SCALAR_CHECK_PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'source_bindings':[{'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in SOURCES],
      'ordinary_analytic_statement':'For every fixed finite M and s>1, no constant amplitude c can satisfy |c|^2 F_s(u) S_M(su)<=S_M(u) for every real u.',
      's':str(s),'M':M,'u':str(u),'u_description':'2^64',
      'actual_prime_power_terms_retained':'n+1<=M, exactly as ScertM M; all bounded by their total amplitude, none removed',
      'total_amplitude_upper_bound':str(A_bound),'exact_multiplier':str(F),
      'certified_ordinary_defect_lower_bound_coarse':str(coarse),
      'certified_ordinary_defect_lower_bound_with_existing_rational_log':str(sharp),
      'normalization_instances':cases,'identity_scale_control':'necessary lower and upper c^2 bounds both 1',
      'negative_controls':rejected,'new_independent_certificate_engine':False,
      'verification_scope':'Exact rational consequences of the written ordinary analytic estimate. No numerical digamma evaluation, no Lean integral/tail proof.',
      'new_Lean_replay':False,'RH_closed':False,
      'OPEN':'Weighted integral transport for actual packet Fourier densities; pointwise impossibility does not decide it.'}
    (ROOT/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print('EXACT_DEFECT_TAIL_SCALAR_CHECK_PASS')
    print('DELTA_2_3_at_2pow64 >=',coarse,'>0 (ordinary analytic reduction)')
    print('AMPLITUDE_NORMALIZATION_CONFLICT_INSTANCES',len(cases))
    print('FALSE_CANDIDATES_REJECTED',len(rejected))
    print('LEAN_ANALYTIC_PROOF False RH_CLOSED False')
if __name__=='__main__':main()
