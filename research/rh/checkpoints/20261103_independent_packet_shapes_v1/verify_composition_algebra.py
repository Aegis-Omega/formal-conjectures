"""Exact finite algebra checks for the written actual-function composition.

This does not certify the analytic source bounds or the Riemann Hypothesis.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sympy as s


def require(condition, message):
    if not condition:
        raise ValueError(message)


a,b,c,d = s.symbols('a b c d')
def q(alpha):
    return a+s.conjugate(alpha)*b+alpha*c+alpha*s.conjugate(alpha)*d

identity=s.expand(q(1)-q(-1)+s.I*q(s.I)-s.I*q(-s.I)-4*b)
energies=s.expand(sum(q(alpha) for alpha in [s.Integer(1),s.Integer(-1),s.I,-s.I])-4*(a+d))
require(identity==0,'non-Hermitian polarization has wrong phase')
require(energies==0,'four-energy sum fails')
A=F(5671,3200); R=F(1621,1850)
require(A-2*R==F(2339,118400)>0,'source exact margin fails')
require(F(57430,65536)-R==F(2911,30310400)>0,'existing row-consumer budget not met')
require(F(2339,118400)>F(641,32768),'comparison with rounded source consumer fails')
print(json.dumps({
    'scope':'non-Hermitian symbolic identity, four-energy sum and exact rational constants only',
    'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'polarization_residual':str(identity),'energy_residual':str(energies),
    'exact_margin':str(A-2*R),
    'row_consumer_headroom':str(F(57430,65536)-R),
    'analytic_source_lemmas_replayed':False,
    'lean_replay':'NOT_RUN','rh_proven':False,
},indent=2))
