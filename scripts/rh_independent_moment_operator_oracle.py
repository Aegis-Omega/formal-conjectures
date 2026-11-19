# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License").
"""Independent AEGIS exact-rational moment-operator correlation identity.

Derive the correlation of h=(D_t^2-1/4) psi from the correlation of psi,
NOT from expanding h(t+s)*h(t).

With r=1/68, q=s/r, phi(z)=(1-z^2)^4, and
P(q)=int_{-1}^{1-q} phi(z+q)phi(z) dz for 0<=q<=2:

 C_h(r*q)=r*(r^-4 P''''(q)-1/2*r^-2 P''(q)+P(q)/16).

This follows from compact-support integration by parts and independently
checks every exact coefficient of the first source-bound verifier.
This is not a Lean kernel proof of the full analytic Weil sign or RH.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
import json

def derivative(p:dict[int,F],n:int=1)->dict[int,F]:
    p=dict(p)
    for _ in range(n):
        p={k-1:F(k)*v for k,v in p.items() if k>0}
    return p

def add(*entries:tuple[F,dict[int,F]])->dict[int,F]:
    o={}
    for mul,p in entries:
        for k,v in p.items():o[k]=o.get(k,F(0))+mul*v
    return {k:v for k,v in o.items() if v}

def value(p:dict[int,F],x:F)->F:
    return sum((v*x**k for k,v in p.items()),F(0))

def phi_correlation_q()->dict[int,F]:
    # An independent normalized-coordinate calculation on z in [-1,1].
    coeff={2*j:F((-1)**j*comb(4,j)) for j in range(5)}
    out={}
    for i,ci in coeff.items():
        for j,cj in coeff.items():
            for l in range(i+1):
                n=l+j+1
                v=ci*cj*comb(i,l)/n
                base=i-l
                for k in range(n+1):
                    idx=base+k
                    out[idx]=out.get(idx,F(0))+v*comb(n,k)*(-1)**k
                out[base]-=v*(-1)**n
    return {k:v for k,v in out.items() if v}

def h_correlation_s(r:F=F(1,68))->tuple[dict[int,F],F]:
    P=phi_correlation_q()
    Q=add((r**-4,derivative(P,4)),
          (-F(1,2)*r**-2,derivative(P,2)),
          (F(1,16),P))
    C={k:v*r**(1-k) for k,v in Q.items()}
    E=C[0]
    assert E>0
    assert value(C,2*r)==0
    assert max(C)==17
    return C,E

def verify():
    from rh_fixedwidth_prime_sign_v1 import normalized_correl_poly
    oracle,E=h_correlation_s()
    expected,other_E=normalized_correl_poly()
    assert E==other_E
    assert [oracle.get(k,F(0))/E for k in range(18)]==expected
    for u in (F(0),F(1,170),F(1,68),F(1,40),F(2,68)):
        assert 0<=u<=F(2,68)
        assert value(oracle,u)==E*sum((a*u**k for k,a in enumerate(expected)),F(0))
    P=phi_correlation_q()
    right=add((F(68)**4,derivative(P,4)),
              (-F(1,2)*F(68)**2,derivative(P,2)),(F(1,16),P))
    wrong=add((F(68)**4,derivative(P,4)),
              (F(1,2)*F(68)**2,derivative(P,2)),(F(1,16),P))
    assert wrong!=right
    return {'status':'EXACT_RATIONAL_INDEPENDENT_CORRELATION_PASS',
            'identity':'C_(D2-1/4)psi=(D_s4-1/2 D_s2+1/16) C_psi',
            'degree':17,'energy':str(E),'terms':18,
            'negative_control':'reversing cross-term sign rejected',
            'RH':'OPEN','Lean_kernel':'OPEN'}

if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
