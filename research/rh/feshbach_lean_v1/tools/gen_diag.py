"""Untrusted generator for CvSDiagL12V1: exact-rational mirror of the Lean definitions.
Emits the E tables, log(pi) bounds and the outward-rounded boxes for cvsEntry M (6/5) n n, n = 0..70."""
import sys
from fractions import Fraction as F
from math import floor, ceil, factorial
S64, S48 = 2**64, 2**48
D = 18446744073709551616
def rdn(x): return F(floor(x * S64), S64)
def rup(x): return F(ceil(x * S64), S64)
piLo = F(314159265358979323846, 10**20); piHi = F(314159265358979323847, 10**20)
l2Lo, l2Hi = F(12786308645202655659, D), F(12786308645202655660, D)
l3Lo, l3Hi = F(20265819725292939637, D), F(20265819725292939639, D)
s2Lo, s2Hi = F(13043817825332782212, D), F(13043817825332782213, D)
s3Lo, s3Hi = F(10650232656628343401, D), F(10650232656628343402, D)
e35Lo = F(339697949173256452625728347, 618970019642690137449562112)
e35Hi = F(679395898346512905251456695, 1237940039285380274899124224)
def Ehi(j): return e35Hi ** (4 * min(j, 12) + 1)
def Elo(j): return e35Lo ** (4 * j + 1) if j < 12 else F(0)
def cw(k): return 2 * k + F(1, 2)
def logSum(y, n): return sum(y ** (i + 1) / (i + 1) for i in range(n))
def lg2(f, x):
    e = 0
    while f > 0 and x >= 2: x /= 2; e += 1; f -= 1
    return e
def yOf(x): return 1 - F(2) ** lg2(64, x) / x
def logLoQ(x): yl = rdn(yOf(x)); return lg2(64, x) * l2Lo + logSum(yl, 64) - yl ** 65 / (1 - yl)
def logHiQ(x): yh = rup(yOf(x)); return lg2(64, x) * l2Hi + logSum(yh, 64) + yh ** 65 / (1 - yh)
def logOk(x): return x > 0 and rdn(yOf(x)) >= 0 and rup(yOf(x)) < 1
def idivLo(nl, nh, dl, dh): return nl / dh if nl >= 0 else nl / dl
def idivHi(nl, nh, dl, dh): return nh / dl if nh >= 0 else nh / dh
aK = F(159, 2)
def SLo(q): return sum(rdn(2 * cw(k) / (cw(k) ** 2 + q)) for k in range(40))
def SHi(q): return sum(rup(2 * cw(k) / (cw(k) ** 2 + q)) for k in range(40))
assert logOk(piLo) and logOk(piHi)
lpiLo, lpiHi = rdn(logLoQ(piLo)) - F(1, S64), rup(logHiQ(piHi)) + F(1, S64)
def hpLo(ql, qh):
    return (-SHi(ql) + logLoQ(aK ** 2 + ql) / 2 - l2Hi
            + idivLo(aK ** 2 - qh, aK ** 2 - ql, (aK ** 2 + ql) ** 2, (aK ** 2 + qh) ** 2) / 6
            - 1 / (4 * aK ** 4) - lpiHi)
def hpHi(ql, qh):
    return (-SLo(qh) + logHiQ(aK ** 2 + qh) / 2 - l2Lo
            + idivHi(aK ** 2 - qh, aK ** 2 - ql, (aK ** 2 + ql) ** 2, (aK ** 2 + qh) ** 2) / 6
            + 1 / (4 * aK ** 4) - lpiLo)
EloL = [rdn(Elo(k)) for k in range(40)]
EhiL = [rup(Ehi(k)) for k in range(40)]
ehK = rup(Ehi(40))
assert all(EloL[k] <= Elo(k) and Ehi(k) <= EhiL[k] <= 1 for k in range(40)) and Ehi(40) <= ehK
def fLo(k, ql, qh): return idivLo(cw(k) ** 2 - qh, cw(k) ** 2 - ql, (cw(k) ** 2 + ql) ** 2, (cw(k) ** 2 + qh) ** 2)
def fHi(k, ql, qh): return idivHi(cw(k) ** 2 - qh, cw(k) ** 2 - ql, (cw(k) ** 2 + ql) ** 2, (cw(k) ** 2 + qh) ** 2)
def DhLo(ql, qh): return sum(rdn(min((1 - EhiL[k]) * fLo(k, ql, qh), (1 - EloL[k]) * fLo(k, ql, qh))) for k in range(40))
def DhHi(ql, qh): return sum(rup(max((1 - EhiL[k]) * fHi(k, ql, qh), (1 - EloL[k]) * fHi(k, ql, qh))) for k in range(40))
def t3(ql, qh): return (aK ** 3 - 3 * aK * qh, aK ** 3 - 3 * aK * ql, (aK ** 2 + ql) ** 3, (aK ** 2 + qh) ** 3)
def gDLo(ql, qh): return aK / (aK ** 2 + qh) / 2 - idivHi(*t3(ql, qh)) / 6
def gDHi(ql, qh): return aK / (aK ** 2 + ql) / 2 - idivLo(*t3(ql, qh)) / 6
hDHi = 1 / (4 * aK ** 5) + ehK / (2 * aK)
def DLo(ql, qh): return DhLo(ql, qh) + gDLo(ql, qh) - hDHi
def DHi(ql, qh): return DhHi(ql, qh) + gDHi(ql, qh) + hDHi
# sine machinery (mirror of CvSTauPrimeL12V1)
def sinPartial(x, n): return sum((-1) ** i * x ** (2 * i + 1) / factorial(2 * i + 1) for i in range(n))
def sinLoQ(x): return sinPartial(x, 14) if x >= 0 else -sinPartial(-x, 15)
def sinHiQ(x): return sinPartial(x, 15) if x >= 0 else -sinPartial(-x, 14)
def mid(ul): return floor(ul + F(1, 2))
def thLo(ul): d = ul - mid(ul); return rdn(min(piLo * d, piHi * d))
def thHi(ul, uh): d = uh - mid(ul); return max(piLo * d, piHi * d)
def baseLo(ul, uh): return sinLoQ(thLo(ul)) - (thHi(ul, uh) - thLo(ul))
def baseHi(ul, uh): return sinHiQ(thLo(ul)) + (thHi(ul, uh) - thLo(ul))
def sinPiLo(ul, uh): return baseLo(ul, uh) if mid(ul) % 2 == 0 else -baseHi(ul, uh)
def sinPiHi(ul, uh): return baseHi(ul, uh) if mid(ul) % 2 == 0 else -baseLo(ul, uh)
w2Lo, w2Hi = l2Lo * (2 * s2Lo), l2Hi * (2 * s2Hi)
w3Lo, w3Hi = l3Lo * (2 * s3Lo), l3Hi * (2 * s3Hi)
cf2Lo, cf2Hi = F(6, 5) * w2Lo * (1 - 5 * l2Hi / 6), F(6, 5) * w2Hi * (1 - 5 * l2Lo / 6)
cf3Lo, cf3Hi = F(6, 5) * w3Lo * (1 - 5 * l3Hi / 6), F(6, 5) * w3Hi * (1 - 5 * l3Lo / 6)
def co(n, lLo, lHi): return 5 * n * lLo / 3 + F(1, 2), 5 * n * lHi / 3 + F(1, 2)
def PdLo(n):
    c2 = sinPiLo(*co(n, l2Lo, l2Hi)); c3 = sinPiLo(*co(n, l3Lo, l3Hi))
    return min(cf2Lo * c2, cf2Hi * c2) + min(cf3Lo * c3, cf3Hi * c3)
def PdHi(n):
    c2 = sinPiHi(*co(n, l2Lo, l2Hi)); c3 = sinPiHi(*co(n, l3Lo, l3Hi))
    return max(cf2Lo * c2, cf2Hi * c2) + max(cf3Lo * c3, cf3Hi * c3)
def ql(n): return (5 * piLo * n / 3) ** 2
def qh(n): return (5 * piHi * n / 3) ** 2
def entryLo(n): return F(6, 5) * hpLo(ql(n), qh(n)) + 2 * DLo(ql(n), qh(n)) - PdHi(n)
def entryHi(n): return F(6, 5) * hpHi(ql(n), qh(n)) + 2 * DHi(ql(n), qh(n)) - PdLo(n)
lo, hi, worst = [], [], 0.0
for n in range(71):
    assert logOk(aK ** 2 + ql(n)) and logOk(aK ** 2 + qh(n))
    assert abs(thLo(co(n, l2Lo, l2Hi)[0])) <= 2 and abs(thLo(co(n, l3Lo, l3Hi)[0])) <= 2
    a, b = entryLo(n), entryHi(n)
    assert a <= b
    worst = max(worst, float(b - a))
    lo.append(F(floor(a * S48), S48)); hi.append(F(ceil(b * S48), S48))
print(f"-- worst entry width {worst:.3e}", file=sys.stderr)
try:
    import mpmath as mp
    mp.mp.dps = 40
    for n in (0, 1, 2, 35, 70):
        r = 5 * mp.pi * n / 3; L = mp.mpf(6) / 5
        h = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * r / 2)) - mp.log(mp.pi)
        ex = mp.nsum(lambda k: mp.e ** (-(2 * k + mp.mpf(1) / 2) * L) * ((2 * k + mp.mpf(1) / 2) ** 2 - r ** 2) / ((2 * k + mp.mpf(1) / 2) ** 2 + r ** 2) ** 2, [0, mp.inf])
        Dv = mp.re(mp.polygamma(1, mp.mpf(1) / 4 + 1j * r / 2)) / 4 - ex
        P = L * (mp.sqrt(2) * mp.log(2) * (1 - mp.log(2) / L) * mp.cos(2 * mp.pi * n / L * mp.log(2)) +
                 2 * mp.log(3) / mp.sqrt(3) * (1 - mp.log(3) / L) * mp.cos(2 * mp.pi * n / L * mp.log(3)))
        v = L * h + 2 * Dv - P
        vf = F(str(mp.nstr(v, 35)))
        assert lo[n] <= vf <= hi[n], n
        print(f"-- n={n}: cvsEntry n n = {mp.nstr(v, 15)}", file=sys.stderr)
except ImportError:
    print("-- mpmath not available", file=sys.stderr)
def lst(name, xs, scale):
    out = [f"def {name} : List ℚ := ["]
    out += [f"  {x.numerator * (scale // x.denominator)} / {scale}," for x in xs]
    out[-1] = out[-1].rstrip(',')
    out.append("]")
    return "\n".join(out)
print(f"def lpiLo : ℚ := {lpiLo.numerator * (S64 // lpiLo.denominator)} / {S64}")
print(f"def lpiHi : ℚ := {lpiHi.numerator * (S64 // lpiHi.denominator)} / {S64}")
print(f"def ehK : ℚ := {ehK.numerator * (S64 // ehK.denominator)} / {S64}")
print(lst('EloL', EloL, S64)); print(lst('EhiL', EhiL, S64))
print(lst('diagLo', lo, S48)); print(lst('diagHi', hi, S48))
