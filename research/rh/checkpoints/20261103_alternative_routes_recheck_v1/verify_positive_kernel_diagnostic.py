"""Arb diagnostic of the explicit Mellin/Bessel example.

The analytic zero identity, entire growth and location proof are in the
manuscript. A ball containing zero is not promoted to an exact identity.
"""
from pathlib import Path
import json
import hashlib
import flint
from flint import arb,acb,ctx

ctx.prec=800
z0=acb(arb(1)/4,arb.pi()/4)
rho=z0+arb(1)/2
B=2*acb(1).bessel_k(z0)
C=(4*z0).cosh()+acb(1).cosh()
w=1-1/rho
if B.contains(0) or not abs(w)<1 or not C.contains(0):
    raise ValueError('explicit analytic example inconsistent with interval evaluation')
report=dict(schema='AEGIS_POSITIVE_MELLIN_DIAGNOSTIC_V1',
            checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            python_flint=flint.__version__,arb_precision=ctx.prec,
            exact_z0='1/4+i*pi/4',exact_rho='3/4+i*pi/4',
            B_value=B.str(60),B_interval_excludes_zero=True,
            cosh_zero_expression=C.str(30),
            exact_zero_identity='cosh(1+i*pi)+cosh(1)=0; ordinary analytic identity',
            identity_proved_by_interval_containment=False,
            mobius_modulus=abs(w).str(60),pole_strictly_inside_unit_disk=True,
            integral_identity='B_a(z)=2*K_z(a), a>0; classical integral representation',
            role='independent special-function diagnostic; ordinary proof establishes the universal claims',
            analytic_Lean_port=False,rh_proven=False)
out=Path(__file__).parent/'POSITIVE_KERNEL_DIAGNOSTIC.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
