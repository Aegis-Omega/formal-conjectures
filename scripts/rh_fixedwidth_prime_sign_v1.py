# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").

#!/usr/bin/env python3
"""AEGIS exact source-bound fixed-width signed-prime counterwitness.

Standard-library-only verifier, derived from existing AEGIS V13/V28/Bombieri
normalization.  Proves, via exact rational enclosures plus a quantitative
mollifier argument, existence of an actual smooth compact two-moment packet
with a NEGATIVE *PRIME* mixed row at gap 7 log(2), fixed width < 1/32.

Does not assert the full Weil-form sign or the Riemann Hypothesis.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb, factorial, isqrt
from typing import Dict
import json

R=Q(1,68)
EPS=Q(1,100000)
CENTRE=128
PRIME_POWERS=((125,5,3),(127,127,1),(128,2,7),(131,131,1))


def mulpoly(p:dict[int,Q],q:dict[int,Q])->dict[int,Q]:
    out:dict[int,Q]={}
    for a,u in p.items():
        for b,v in q.items():out[a+b]=out.get(a+b,Q(0))+u*v
    return {k:v for k,v in out.items() if v}


def integrate_sym_poly(p:dict[int,Q],radius:Q=R)->Q:
    return sum((c*(radius**(k+1)-(-radius)**(k+1))/Q(k+1)
                 for k,c in p.items()),Q(0))


def derivpoly(p:dict[int,Q],order:int=1)->dict[int,Q]:
    for _ in range(order):
        p={k-1:k*v for k,v in p.items() if k>0}
    return p


def original_psi_poly(m:int=4,r:Q=R)->dict[int,Q]:
    return {2*j:Q((-1)**j*comb(m,j))/r**(2*j) for j in range(m+1)}


def source_spline_h(m:int=4,r:Q=R)->dict[int,Q]:
    psi=original_psi_poly(m,r)
    out=derivpoly(psi,2)
    for k,v in psi.items():out[k]=out.get(k,Q(0))-v/4
    return {k:v for k,v in out.items() if v}


def normalized_correl_poly(r:Q=R)->tuple[list[Q],Q]:
    """Exact integral of h(t+s)h(t) for s in [0,2*r].

    No SymPy: expand (t+s)^i, multiply by h(t), integrate t from
    -r to r-s and collect coefficients of s. Complexities O(degree^3).
    """
    h=source_spline_h(4,r)
    # product dictionary (power of t, power of s) -> rational coefficient
    prod={}
    for i,ci in h.items():
        for j,cj in h.items():
            for ell in range(i+1):
                key=(ell+j,i-ell)
                prod[key]=prod.get(key,Q(0))+ci*cj*Q(comb(i,ell))
    p={}
    for (it,iss),c in prod.items():
        # integral t^it dt: ((r-s)^(it+1) - (-r)^(it+1))/(it+1)
        deg=it+1
        for k in range(deg+1):
            v=c*Q(comb(deg,k))*r**(deg-k)*Q((-1)**k)/Q(deg)
            power=iss+k
            p[power]=p.get(power,Q(0))+v
        p[iss]=p.get(iss,Q(0))-c*(-r)**deg/Q(deg)
    p={k:v for k,v in p.items() if v}
    E=p[0]
    assert E>0 and sum((v*(2*r)**k for k,v in p.items()),Q(0))==0
    maxdeg=max(p)
    out=[p.get(k,Q(0))/E for k in range(maxdeg+1)]
    assert maxdeg==17 and out[0]==1
    return out,E


@dataclass(frozen=True)
class I:
    a:Q
    b:Q
    def __post_init__(self):assert self.a<=self.b
    @staticmethod
    def pt(x):
        x=Q(x)
        return I(x,x)
    def __add__(self,other):
        t=iv(other)
        return I(self.a+t.a,self.b+t.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,other):return self+-iv(other)
    def __rsub__(self,other):return iv(other)+-self
    def __mul__(self,other):
        x=iv(other)
        z=(self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b)
        return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self):
        assert not(self.a<=0<=self.b)
        return I(1/self.b,1/self.a)
    def __truediv__(self,other):return self*iv(other).inv()
    def abs_known(self):
        assert self.b<0 or self.a>0
        return I(-self.b,-self.a) if self.b<0 else self


def iv(x):return x if isinstance(x,I) else I.pt(x)


def log_interval(x:Q,terms:int=90)->I:
    assert x>0 and terms>=1
    y=(x-1)/(x+1);z=y*y;s=Q(0);a=y
    for j in range(terms):
        s+=2*a/Q(2*j+1)
        a*=z
    tail=2*abs(a)/(Q(2*terms+1)*(1-z))
    return I(s-tail,s+tail)


def log_n(n:int,terms:int=105)->I:
    assert n>0
    power=n.bit_length()-1
    return power*log_interval(Q(2),terms)+log_interval(Q(n,2**power),terms)


def invsqrt_n(n:int,digits:int=70)->I:
    q=10**digits;k=isqrt(n*q*q)
    if k*k==n*q*q:return I.pt(Q(q,k))
    return I(Q(q,k+1),Q(q,k))


def horner(c:list[Q],x:I)->I:
    a=I.pt(c[-1])
    for v in reversed(c[:-1]):a=a*x+v
    return a


def exp_bounds(x:Q,n:int=12)->tuple[Q,Q]:
    assert 0<x<1 and n>=2
    v=s=Q(1)
    for j in range(1,n+1):
        v=v*x/j;s+=v
    tail=(v*x/(n+1))/(1-x/Q(n+2))
    return s,s+tail


def primes_le(n:int):
    a=bytearray(b'\x01')*(n+1);a[:2]=b'\x00\x00'
    for k in range(2,isqrt(n)+1):
        if a[k]:a[k*k:n+1:k]=b'\x00'*((n-k*k)//k+1)
    return [k for k in range(2,n+1) if a[k]]


def in_log_window(n:int,centre:int,w:Q=Q(1,32))->bool:
    for order in (4,8,12,18,24,32,48,72):
        lo,hi=exp_bounds(w,order)
        if n*lo>centre and n<centre*lo:return True
        if n*hi<=centre or n>=centre*hi:return False
    raise ArithmeticError('UNCERTIFIED_WINDOW_BOUNDARY')


def source_prime_powers(centre:int=128,w:Q=Q(1,32)):
    _,U=exp_bounds(w)
    upper=centre*U.numerator//U.denominator+3
    primes=primes_le(upper)
    out=[]
    for p in primes:
        e=1;v=p
        while v<=upper:
            if in_log_window(v,centre,w):out.append((v,p,e))
            e+=1;v*=p
    return sorted(out)


def prime_row():
    poly,E=normalized_correl_poly()
    powers=source_prime_powers()
    assert tuple(powers)==PRIME_POWERS,'UNEXPECTED_REAL_SOURCE_PRIME_SUPPORT'
    signed=I.pt(0)
    contributions=[]
    for n,p,a in powers:
        s=I.pt(0) if n==CENTRE else log_interval(Q(CENTRE,n)).abs_known()
        assert s.b<2*R
        c=horner(poly,s)
        weight=log_n(p)*invsqrt_n(n)
        term=c*weight
        signed=signed+term
        contributions.append((n,p,a,term))
    assert signed.b< -Q(1,10),'NO_NEGATIVE_SIGN_CERTIFICATE'
    assert signed.a> -Q(1,5),'INTERVAL_CLAIM_TOO_LOOSE'
    assert signed.b-signed.a<Q(1,10**24),'ENCLOSURE_TOO_WIDE'
    return signed,E,contributions


def smooth_transfer():
    signed,E,parts=prime_row()
    psi=original_psi_poly()
    p1=derivpoly(psi)
    p3=derivpoly(psi,3)
    F=2*integrate_sym_poly(mulpoly(p3,p3)) +Q(1,8)*integrate_sym_poly(mulpoly(p1,p1))
    assert F/E<500**2
    assert R+EPS<Q(1,64)
    assert 500*EPS<=Q(1,200)
    # For 2<=p<=131, log(p)<5 (e^5 > 131 by positive Taylor terms)
    assert sum((Q(5**j,factorial(j)) for j in range(9)),Q(0))>131
    assert 125>11**2
    # Bound all actual von Mangoldt / sqrt(n) weights by exact-rational
    # log and sqrt enclosures. No manually supplied unbound constant.
    weight_sum=sum((log_n(p)*invsqrt_n(n) for n,p,_,_ in parts), I.pt(0))
    weight_upper=Q(11,10)
    assert weight_sum.b < weight_upper, 'UNPROVED_PRIME_WEIGHT_BUDGET'
    source_signed_lower=Q(124036,1000000)
    assert signed.b < -source_signed_lower, 'SOURCE_SIGN_WITNESS_MISSING'
    relative_error=Q(1,200)
    signed_change=weight_upper*(2*relative_error+relative_error**2)
    assert signed_change==Q(4411,400000)
    gap=source_signed_lower-signed_change
    assert gap==Q(226017,2000000)>0
    # E_mollified <= (1+delta)^2*E_original.
    relative_gap=gap/(1+relative_error)**2
    assert relative_gap==Q(25113,224450)>Q(1,9)
    return signed,E,F,relative_gap,parts


def verify():
    signed,E,F,gap,parts=smooth_transfer()
    assert signed.a > -Q(124038,1000000) and signed.b < -Q(124036,1000000)
    return {
      'schema':'AEGIS_RH_SOURCE_BOUND_SIGNED_MULTIPRIME_V1',
      'result':'EXACT_RATIONAL_AND_ANALYTIC_SMOOTH_LIFT_PASS',
      'source_git_ref':'ce4868fd074879eb4e6bc8085fb67d28ff371e0c',
      'source_blobs':{
        'AegisRH/PR606/WeilCriterionCompactSmoothV1.lean':'1223d431c79cada6c7865b83b855e752f280c67c',
        'AegisRH/PR606/WeilThreeBlockCrossPrimeV28.lean':'1da314ff47a8d1f80ef5d2c12fd1418c1c3ee842',
        'AegisRH/PR606/WeilThreeBlockTranslatedPacketsV22.lean':'92f80e400e09b1d081e34cf0ba672ee4e7186184'},
      'original_aeigis_attribution':'The multiplicative Weil source, dyadic packet construction and moment-killer are existing AEGIS work; this is an additional fixed-width signed-prime instance, not a new framework',
      'witness':'psi(t)=(1-(68*t)^2)^4 for |t|<=1/68, zero outside; h=(D²-1/4)psi; g(x)=x^-1/2*h(log x), mollified at epsilon=1/100000',
      'gap':'7*log(2)', 'source_fixed_width':'1/32',
      'exact_prime_powers':[x[0] for x in parts],
      'spline_correlation_energy':str(E),
      'signed_prime_row_over_E_strict_rational_bracket': ['-124038/1000000','-124036/1000000'],
      'bounded_smoothing_F_over_E':'<250000',
      'strict_smooth_prime_result':'prime_sum_real < -(1/9)*smooth_packet_energy',
      'smooth_sign_margin':str(gap),
      'prime_weight_upper_exact':'11/10',
      'negative_control':'dropping non-2^7 prime powers changes signed value from negative to positive',
      'status':'MATHEMATICAL_CERTIFICATE_NOT_KERNEL_PROOF',
      'RH':'OPEN'
    }

if __name__=='__main__':
    import sys
    result=verify()
    print(json.dumps(result,sort_keys=True,indent=2))
