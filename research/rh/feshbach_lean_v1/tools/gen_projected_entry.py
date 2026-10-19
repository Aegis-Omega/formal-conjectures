"""Untrusted generator / exact mirror for CvSProjectedEntryL12V1 (L = 6/5, 139 x 139).

Reads certR, certI (CvSProjectedPackedCertificateL12V1), diagLo/diagHi (CvSDiagL12V1) and
tauFLo/tauFHi (CvSTauPrimeL12V1), recomputes every quantity of `bigCheck` in exact integers,
checks all 9730 upper-triangle entries against both Im certI i j and Im certI j i, and compares
the embedded data of CvSProjectedEntryL12V1.lean.  Usage: python3 tools/gen_projected_entry.py
"""
import math, re, sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def src(name): return (ROOT / (name + '.lean')).read_text()

def rows(text, prefix):
    out = {}
    for m in re.finditer(r'def ' + prefix + r'Row(\d+) : List \S+ :=\s*\[(.*?)\]\n', text, re.S):
        out[int(m[1])] = m[2]
    return [out[i] for i in range(len(out))]

def qlist(text, name):
    body = re.search(r'def ' + name + r' : List ℚ := \[(.*?)\]', text, re.S)[1]
    res = []
    for t in body.split(','):
        t = t.strip()
        m = re.fullmatch(r'(-?\d+)\s*/\s*(\d+)(?:\s*\^\s*(\d+))?', t)
        res.append(F(int(m[1]), int(m[2]) ** int(m[3] or 1)) if m else F(int(t)))
    return res

cert = src('CvSProjectedPackedCertificateL12V1')
R = [[int(x) for x in re.findall(r'-?\d+', r)] for r in rows(cert, 'certR')]
I = [[tuple(int(v) for v in p.split(',')) for p in re.findall(r'⟨([^⟩]*)⟩', r)] for r in rows(cert, 'certI')]
assert len(R) == 139 and all(len(r) == 139 for r in R) and len(I) == 139 and all(len(r) == 139 for r in I)
dl, dh = qlist(src('CvSDiagL12V1'), 'diagLo'), qlist(src('CvSDiagL12V1'), 'diagHi')
tl, th = qlist(src('CvSTauPrimeL12V1'), 'tauFLo'), qlist(src('CvSTauPrimeL12V1'), 'tauFHi')

N, P = 141, 64
pl, ph = F(314159265358979323846, 10**20), F(314159265358979323847, 10**20)
SI = round(F(31415926535897932384626433832795, 10**31) ** 2 * 2**70)
es = F(1, 2**63); sh = F(SI, 2**70)
assert pl * pl >= sh - es and ph * ph <= sh + es
LAM = math.lcm(*range(1, 141)); sig = 9 * 2**112

def rZ(m, i): return R[m][i] if 0 <= m < 139 else 0
def xI(k, i):
    n = k - 70
    return -(25 * n * n * SI + 9 * 2**68) * (2 * rZ(n + 69, i) - rZ(n + 68, i) - rZ(n + 70, i))
X = [[xI(k, i) for k in range(N)] for i in range(139)]
def kp(k, l): return 0 if k == l else LAM // (k - l)
H = [[sum(kp(k, l) * X[i][l] for l in range(N)) for k in range(N)] for i in range(139)]

def i48(q):
    x = q * 2**48; assert x.denominator == 1; return int(x.numerator)
dmI = [i48(dl[m] + dh[m]) for m in range(71)]; drI = [i48(dh[m] - dl[m]) for m in range(71)]
tmI = [i48(tl[m] + th[m]) for m in range(70)]; trI = [i48(th[m] - tl[m]) for m in range(70)]
d2 = [dmI[abs(k - 70)] for k in range(N)]; dr = [drI[abs(k - 70)] for k in range(N)]
tK = [-tmI[69 - k] if k < 70 else 0 if k == 70 else tmI[k - 71] for k in range(N)]
tr = [0 if k == 70 else trI[abs(k - 70) - 1] for k in range(N)]

C1, C2 = 5 * SI * LAM, 3 * 2**70
v = [[C1 * d2[k] * X[i][k] for k in range(N)] + [C2 * tK[k] * X[i][k] for k in range(N)] +
     [C2 * H[i][k] for k in range(N)] for i in range(139)]
w = [X[i] + H[i] + [tK[k] * X[i][k] for k in range(N)] for i in range(139)]
B1, B2 = 2**205, 2**448
assert all(abs(kp(k, l)) <= B1 for k in range(N) for l in range(N))
assert all(abs(x) <= B2 for r in v + w for x in r)

def isqrt_up(num, den):
    a = math.isqrt(num // den)
    while a * a * den < num: a += 1
    return a
Q49 = 2**49 * sig * sig
AD = [isqrt_up(2**128 * sum(dr[k] * X[i][k]**2 for k in range(N)), Q49) for i in range(139)]
AT = [isqrt_up(2**128 * sum(tr[k] * X[i][k]**2 for k in range(N)), Q49) for i in range(139)]
BT = [isqrt_up(2**128 * sum(tr[k] * H[i][k]**2 for k in range(N)), Q49 * LAM * LAM) for i in range(139)]
XMI = max(abs(x) for r in X for x in r); HMI = max(abs(x) for r in H for x in r)
assert XMI <= B1
DMI = max(abs(dmI[m]) + drI[m] for m in range(71)); TMI = max(abs(x) for x in tmI); RTI = max(trI)
CPI = math.ceil(F(3, 5) / (pl * pl) * 2**64)
XM, HM = F(XMI, sig), F(HMI, sig * LAM); dX = es / 9 * XM; dH = 141 * dX; dC = 3 * es / 405
DM, TM, RT, CP = F(DMI, 2**49), F(TMI, 2**49), F(RTI, 2**49), F(CPI, 2**64)
Rpi = (141 * (DM * ((XM + dX) * dX + dX * XM)) + CP * (141 * (RT * (2 * (dX * (HM + dH) + XM * dH))))
       + 141 * (TM * (dC * (2 * ((XM + dX) * (HM + dH))) + CP * (2 * ((XM + dX) * dH + dX * HM)))))
SR, T64 = 2**192, 2**64
RPI = math.ceil(Rpi * SR)
DE = Q49 * LAM * 5 * SI

bad = 0
for i in range(139):
    for j in range(i, 139):
        ne = sum(a * b for a, b in zip(v[i], w[j]))
        rad = AD[i] * AD[j] * T64 + CPI * (AT[i] * BT[j] + AT[j] * BT[i]) + RPI
        for lo, hi in (I[i][j], I[j][i]):
            if not (lo * SR * DE + rad * T64 * DE <= ne * T64 * SR and
                    ne * T64 * SR + rad * T64 * DE <= hi * SR * DE):
                bad += 1
print('entries checked: 9730 (both orientations), failures:', bad, ' Rpi ~', float(Rpi))

data = dict(SI=SI, LAM=LAM, dmI=dmI, drI=drI, tmI=tmI, trI=trI, AD=AD, AT=AT, BT=BT, XMI=XMI,
            HMI=HMI, DMI=DMI, TMI=TMI, RTI=RTI, CPI=CPI, RPI=RPI)
lean = src('CvSProjectedEntryL12V1')
for k, val in data.items():
    m = re.search(r'^def ' + k + r' : .*?:= (.*)$', lean, re.M)
    got = [int(x) for x in re.findall(r'-?\d+', m[1])]
    want = val if isinstance(val, list) else [val]
    assert got == want, k
print('embedded data of CvSProjectedEntryL12V1.lean matches')
sys.exit(1 if bad else 0)
