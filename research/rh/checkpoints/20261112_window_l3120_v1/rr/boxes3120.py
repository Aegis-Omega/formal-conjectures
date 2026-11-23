"""Parse the kernel-checked L = 31/20 boxes: tau_k, k = 1..2000 (CvSTauL3120K{1..1951}V1.tLo/tHi) and the
diagonal n = 0..156 (CvSDiagL3120V1.diagLo/diagHi). Derived from ../20261112_window_l32_rowcert_v1/boxes32.py."""
import re
from fractions import Fraction as F
from pathlib import Path

D = Path(__file__).resolve().parent.parent


def qlist(path, name):
    t = (D / path).read_text()
    m = re.search(r'def ' + name + r' : List ℚ := \[(.*?)\]', t, re.S)
    return [F(int(a), int(b)) for a, b in re.findall(r'(-?\d+) / (\d+)', m.group(1))]


def load():
    lo, hi = [], []
    for s in range(1, 2001, 50):
        lo += qlist(f'CvSTauL3120K{s}V1.lean', 'tLo'); hi += qlist(f'CvSTauL3120K{s}V1.lean', 'tHi')
    dlo, dhi = qlist('CvSDiagL3120V1.lean', 'diagLo'), qlist('CvSDiagL3120V1.lean', 'diagHi')
    assert len(lo) == len(hi) == 2000 and len(dlo) == len(dhi) == 157
    tau = {0: (F(0), F(0))}
    for k in range(1, 2001):
        assert lo[k - 1] <= hi[k - 1]
        tau[k] = (lo[k - 1], hi[k - 1]); tau[-k] = (-hi[k - 1], -lo[k - 1])
    diag = {n: (dlo[abs(n)], dhi[abs(n)]) for n in range(-156, 157)}
    return tau, diag


if __name__ == '__main__':
    tau, diag = load()
    print('max tau radius k<=156: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(1, 157)))
    print('max tau radius 157..2000: %.3e' % max(float(tau[k][1] - tau[k][0]) / 2 for k in range(157, 2001)))
    print('max diag radius: %.3e' % max(float(diag[n][1] - diag[n][0]) / 2 for n in range(157)))
    print('max |tau| 157..2000: %.3f' % max(max(abs(float(tau[k][0])), abs(float(tau[k][1]))) for k in range(157, 2001)))
