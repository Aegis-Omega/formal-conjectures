"""Untrusted generator for CvSTauPrimeL43V1 (port of gen_tau_prime.py to L = 4/3): mirrors
primeLo/primeHi exactly (Fractions) and emits outward-rounded boxes (scale 2^48) for
tau_k = int h+ S_k + prime part, k = 1..70. Usage: python3 gen_tau_prime43.py CvSTauL43DataV1.lean"""
import re, sys
from fractions import Fraction as F
from math import floor, ceil, factorial
S64 = 2**64
S48 = 2**48
D = 18446744073709551616
l2Lo, l2Hi = F(12786308645202655659, D), F(12786308645202655660, D)
l3Lo, l3Hi = F(20265819725292939637, D), F(20265819725292939639, D)
s2Lo, s2Hi = F(13043817825332782212, D), F(13043817825332782213, D)
s3Lo, s3Hi = F(10650232656628343401, D), F(10650232656628343402, D)
piLo = F(314159265358979323846, 100000000000000000000)
piHi = F(314159265358979323847, 100000000000000000000)
def rdn(x): return F(floor(x * S64), S64)
def sinPartial(x, n): return sum((-1)**i * x**(2*i+1) / factorial(2*i+1) for i in range(n))
def sinLoQ(x): return sinPartial(x, 14) if x >= 0 else -sinPartial(-x, 15)
def sinHiQ(x): return sinPartial(x, 15) if x >= 0 else -sinPartial(-x, 14)
def mid(ul): return floor(ul + F(1, 2))
def thLo(ul): d = ul - mid(ul); return rdn(min(piLo*d, piHi*d))
def thHi(ul, uh): d = uh - mid(ul); return max(piLo*d, piHi*d)
def baseLo(ul, uh): return sinLoQ(thLo(ul)) - (thHi(ul, uh) - thLo(ul))
def baseHi(ul, uh): return sinHiQ(thLo(ul)) + (thHi(ul, uh) - thLo(ul))
def sinPiLo(ul, uh): return baseLo(ul, uh) if mid(ul) % 2 == 0 else -baseHi(ul, uh)
def sinPiHi(ul, uh): return baseHi(ul, uh) if mid(ul) % 2 == 0 else -baseLo(ul, uh)
w2Lo, w2Hi = l2Lo * (2 * s2Lo), l2Hi * (2 * s2Hi)
w3Lo, w3Hi = l3Lo * (2 * s3Lo), l3Hi * (2 * s3Hi)
def s2l(k): return sinPiLo(3*k*l2Lo/2, 3*k*l2Hi/2)
def s2h(k): return sinPiHi(3*k*l2Lo/2, 3*k*l2Hi/2)
def s3l(k): return sinPiLo(3*k*l3Lo/2, 3*k*l3Hi/2)
def s3h(k): return sinPiHi(3*k*l3Lo/2, 3*k*l3Hi/2)
def sumLo(k): return min(w2Lo*s2l(k), w2Hi*s2l(k)) + min(w3Lo*s3l(k), w3Hi*s3l(k))
def sumHi(k): return max(w2Lo*s2h(k), w2Hi*s2h(k)) + max(w3Lo*s3h(k), w3Hi*s3h(k))
def primeLo(k): return min(piLo*sumLo(k), piHi*sumLo(k))
def primeHi(k): return max(piLo*sumHi(k), piHi*sumHi(k))

def full_boxes(tLo, tHi, k0):
    """Outward-rounded tau boxes for k = k0, k0 + 1, ... from source boxes tLo, tHi."""
    lo, hi, worst = [], [], 0.0
    for i, (sl, sh) in enumerate(zip(tLo, tHi)):
        k = k0 + i
        assert abs(thLo(3*k*l2Lo/2)) <= 2 and abs(thLo(3*k*l3Lo/2)) <= 2
        pl, ph = primeLo(k), primeHi(k)
        assert pl <= ph
        worst = max(worst, float(ph - pl))
        lo.append(F(floor((sl + pl) * S48), S48)); hi.append(F(ceil((sh + ph) * S48), S48))
    print(f"-- worst prime-part width {worst:.3e}; max tau width {max(float(b-a) for a,b in zip(lo,hi)):.3e}", file=sys.stderr)
    return lo, hi
def lst(name, xs):
    out = [f"def {name} : List ℚ := ["]
    out += [f"  {x.numerator * (S48 // x.denominator)} / {S48}," for x in xs]
    out[-1] = out[-1].rstrip(',')
    out.append("]")
    return "\n".join(out)


if __name__ == '__main__':
    src = open(sys.argv[1]).read()
    def grab(name):
        body = re.search(r"def " + name + r" : List ℚ := \[(.*?)\]", src, re.S).group(1)
        return [F(int(a), int(b)) for a, b in re.findall(r"(\d+) / (\d+)", body)]
    tLo, tHi = grab('tauLo'), grab('tauHi')
    assert len(tLo) == len(tHi) == 70
    lo, hi = full_boxes(tLo, tHi, 1)
    try:
        import mpmath as mp
        mp.mp.dps = 40
        for k in (1, 7, 70):
            v = mp.pi*(mp.sqrt(2)*mp.log(2)*mp.sin(mp.pi*3*k*mp.log(2)/2) + 2*mp.log(3)/mp.sqrt(3)*mp.sin(mp.pi*3*k*mp.log(3)/2))
            assert primeLo(k) <= F(str(v)) + F(1,10**30) and F(str(v)) - F(1,10**30) <= primeHi(k), k
            print(f"-- k={k}: prime part {mp.nstr(v, 20)} in [{float(primeLo(k))}, {float(primeHi(k))}]", file=sys.stderr)
    except ImportError:
        print("-- mpmath not available", file=sys.stderr)
    print(lst('tauFLo', lo)); print(); print(lst('tauFHi', hi))
