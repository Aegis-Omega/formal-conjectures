"""Parse the kernel-checked L = 4/3 boxes from the staged Lean modules."""
import re
from fractions import Fraction as F
from pathlib import Path

D = Path(__file__).resolve().parent.parent


def qlist(path, name):
    t = (D / path).read_text()
    m = re.search(r'def ' + name + r' : List ℚ := \[(.*?)\]', t, re.S)
    out = []
    for tok in m.group(1).replace('\n', ' ').split(','):
        tok = tok.strip()
        if '/' in tok:
            a, b = tok.split('/')
            out.append(F(int(a.strip().replace('(', '').replace(')', '')), int(b.strip())))
        else:
            out.append(F(int(tok.replace('(', '').replace(')', ''))))
    return out


def load():
    lo = qlist('CvSTauPrimeL43V1.lean', 'tauFLo') + qlist('CvSTauR1PrimeL43V1.lean', 'tauFLoExtra')
    hi = qlist('CvSTauPrimeL43V1.lean', 'tauFHi') + qlist('CvSTauR1PrimeL43V1.lean', 'tauFHiExtra')
    dlo = qlist('CvSDiagL43V1.lean', 'diagLo')
    dhi = qlist('CvSDiagL43V1.lean', 'diagHi')
    assert len(lo) == len(hi) == 200 and len(dlo) == len(dhi) == 71
    tau = {0: (F(0), F(0))}
    for k in range(1, 201):
        tau[k] = (lo[k - 1], hi[k - 1])
        tau[-k] = (-hi[k - 1], -lo[k - 1])
    diag = {n: (dlo[abs(n)], dhi[abs(n)]) for n in range(-70, 71)}
    return tau, diag


if __name__ == '__main__':
    tau, diag = load()
    print('max tau radius k<=70: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(1, 71)))
    print('max tau radius 71..200: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(71, 201)))
    print('max diag radius: %.3e' % max(float(diag[n][1] - diag[n][0]) / 2 for n in range(71)))
    print('max |tau| k<=70: %.3f, 71..200: %.3f' % (max(abs(float(tau[k][0])) for k in range(1, 71)),
                                                     max(abs(float(tau[k][0])) for k in range(71, 201))))
