"""Parse the kernel-checked L = 3/2 boxes: tau_k, k = 1..900 (CvSTauL32K{1..851}V1.tLo/tHi) and the
diagonal n = 0..150 (CvSDiagL32V1.diagLo/diagHi)."""
import re
from fractions import Fraction as F
from pathlib import Path

D = Path(__file__).resolve().parent.parent / 'l32'


def qlist(path, name):
    t = (D / path).read_text()
    m = re.search(r'def ' + name + r' : List ℚ := \[(.*?)\]', t, re.S)
    return [F(int(a), int(b)) for a, b in re.findall(r'(-?\d+) / (\d+)', m.group(1))]


def load():
    lo, hi = [], []
    for s in range(1, 901, 50):
        lo += qlist(f'CvSTauL32K{s}V1.lean', 'tLo'); hi += qlist(f'CvSTauL32K{s}V1.lean', 'tHi')
    dlo, dhi = qlist('CvSDiagL32V1.lean', 'diagLo'), qlist('CvSDiagL32V1.lean', 'diagHi')
    assert len(lo) == len(hi) == 900 and len(dlo) == len(dhi) == 151
    tau = {0: (F(0), F(0))}
    for k in range(1, 901):
        assert lo[k - 1] <= hi[k - 1]
        tau[k] = (lo[k - 1], hi[k - 1]); tau[-k] = (-hi[k - 1], -lo[k - 1])
    diag = {n: (dlo[abs(n)], dhi[abs(n)]) for n in range(-150, 151)}
    return tau, diag


if __name__ == '__main__':
    tau, diag = load()
    print('max tau radius k<=150: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(1, 151)))
    print('max tau radius 151..900: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(151, 901)))
    print('max diag radius: %.3e' % max(float(diag[n][1] - diag[n][0]) / 2 for n in range(151)))
    print('max |tau| 151..900: %.3f' % max(max(abs(float(tau[k][0])), abs(float(tau[k][1]))) for k in range(151, 901)))
