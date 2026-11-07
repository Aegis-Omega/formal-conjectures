"""Nonrigorous, independent Fourier-coordinate sign/factor diagnostic.

The ordinary proof and Arb enclosures do not rely on SciPy's error estimate.
"""
from pathlib import Path
import hashlib
import json
import math
from scipy.integrate import quad
from scipy.special import digamma

root=Path(__file__).parent
results=[]
for denominator in (1000,2000):
    delta=1/denominator
    d=math.log(2); h=d/3
    def transform(t):
        z=delta*t
        if abs(z)<0.01:
            value=4/3-2*z*z/15+z**4/210-z**6/11340+z**8/997920
        else:
            value=4*(math.sin(z)-z*math.cos(z))/z**3
        return (15*delta/16)*value**2
    def amplitude(t):
        return (digamma(0.25+0.5j*t).real-math.log(math.pi))*transform(t)
    values=[]; estimates=[]; statuses=[]
    for frequency in (h,d):
        result=quad(amplitude,0,math.inf,weight='cos',wvar=frequency,
                    epsabs=1e-11,limlst=1000,limit=200,maxp1=100,full_output=1)
        values.append(result[0]); estimates.append(result[1]); statuses.append(len(result)==3)
    arch=2/math.pi*(values[0]-values[1])
    receipt=json.loads((root/f'REFLECTION_RECEIPT_{denominator}.json').read_text())
    midpoint=float(receipt['archimedean_mixed'].split()[0][1:])
    if not all(statuses) or abs(arch-midpoint)>1e-8:
        raise RuntimeError('independent Fourier diagnostic disagrees')
    results.append(dict(denominator=denominator,fourier_arch=arch,
                        arb_arch_midpoint=midpoint,difference=arch-midpoint,
                        scipy_reported_error=2/math.pi*sum(estimates),
                        diagnostic_only=True))
report=dict(schema='AEGIS_ODD_FOURIER_DIAGNOSTIC_V1',
            checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            results=results,rigorous_numerical_certificate=False,rh_proven=False)
destination=root/'FOURIER_DIAGNOSTIC.json'
if destination.exists():raise ValueError('refusing to overwrite diagnostic')
destination.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
