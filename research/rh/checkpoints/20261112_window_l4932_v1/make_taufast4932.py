"""Write CvSTauFastL4932V1.lean from ../20261111_window_l32_tau_v1/CvSTauFastL32V1.lean (L = 3/2 -> 49/32):
omega_k = 64 pi k / 49 (a = 64 floor(pi)_20 k, D = 49 10^20), the 1 - e^{-c_j L} tables recomputed from
CvSExpL4932V1 (j0 = 12), the prime-part arguments 2 k log p / L = 64 k log p / 49. Every substitution is counted.
usage: python3 make_taufast4932.py PATH/CvSTauFastL32V1.lean OUT.lean
"""
import re
import sys
from fractions import Fraction as F
from math import floor, ceil

t = open(sys.argv[1]).read()


def rep(a, b, n):
    global t
    c = t.count(a)
    assert c == n, (a, c, n)
    t = t.replace(a, b)


lo = F(143923895647018040563762077, 309485009821345068724781056)   # CvSExpL4932V1.e4964Lo
hi = F(4497621738969313767617565, 9671406556917033397649408)        # CvSExpL4932V1.e4964Hi
j0 = 12
A = [floor(2 ** 64 * (1 - hi ** (4 * min(i, j0) + 1))) for i in range(13)]
B = [ceil(2 ** 64 * (1 - (lo ** (4 * i + 1) if i < j0 else 0))) for i in range(13)]


def fmt(name, v):
    s = f'def {name} : List ℕ := ['
    lines, cur = [], s
    for i, x in enumerate(v):
        piece = f'{x}' + (', ' if i < len(v) - 1 else ']')
        if len(cur) + len(piece.rstrip()) > 100:
            lines.append(cur.rstrip())
            cur = '  '
        cur += piece
    lines.append(cur)
    return '\n'.join(lines)


a0 = t.index('def NEloT'); a1 = t.index('\n\n', a0)
t = t[:a0] + fmt('NEloT', A) + t[a1:]
b0 = t.index('def NEhiT'); b1 = t.index('\n\n', b0)
t = t[:b0] + fmt('NEhiT', B) + t[b1:]

d0 = t.index('/-!\n# `τ_k` at `L = 3/2`'); d1 = t.index('-/', d0) + 2
t = t[:d0] + '''/-!
# `τ_k` at `L = 49/32` for every prime cutoff `M ≥ 4`: the check with integer head sums

`CvSTauFastL32V1` at `L = 49/32`: the head `Σ_{j<J} 2ω(1 − e^{−c_j L})/(c_j² + ω²)` of
`CvSTauL4932V1.tauCheck` summed in natural numbers. With `ω ∈ [a/D, b/D]` (`a = 64⌊π⌋₂₀k`,
`D = 49·10²⁰`), each term is `⌊8 a N_j D / ((4j+1)² D² + 4 b²)⌋ / 2⁶⁴` with
`N_j/2⁶⁴ ≤ 1 − e^{−c_j L}` (`hLo`), and `(⌊8 b N'_j D / ((4j+1)² D² + 4 a²)⌋ + 1) / 2⁶⁴` with
`1 − e^{−c_j L} ≤ N'_j/2⁶⁴` (`hHi`). `h_bounds` is the induction, `srcCheck_sound` the
`CvSTauL4932V1.tauCheck_sound` argument with this head.

The prime part: at `L = 49/32` the prime powers `2, 3, 4` contribute (`primeSum_eq`, from
`CvSNodeL4932V1`), with `ppw 3 = log 2` (`CvSTraceM4SlackV1.ppw_three`). `tauF_sound` turns a
passing check into `lo ≤ τ_k ≤ hi` for every `M ≥ 4`. Not RH.
-/''' + t[d1:]

rep('CvSTauFastL32V1', 'CvSTauFastL4932V1', 9)
rep('CvSTauL32V1', 'CvSTauL4932V1', t.count('CvSTauL32V1'))
rep('CvSNodeL32V1', 'CvSNodeL4932V1', t.count('CvSNodeL32V1'))
rep('(3 / 2)', '(49 / 32)', t.count('(3 / 2)'))
rep('L = 3/2', 'L = 49/32', t.count('L = 3/2'))
rep('(L := 3 / 2)', '(L := 49 / 32)', 1)
rep('4 * Real.pi * k / 3', '64 * Real.pi * k / 49', 1)
for x in ('Real.log 2', 'Real.log 3', 'l2Lo', 'l2Hi', 'l3Lo', 'l3Hi'):
    rep(f'8 * k * {x} / 3', f'128 * k * {x} / 49', t.count(f'8 * k * {x} / 3'))
    rep(f'4 * k * {x} / 3', f'64 * k * {x} / 49', t.count(f'4 * k * {x} / 3'))
rep('def Dk : ℕ := 300000000000000000000', 'def Dk : ℕ := 4900000000000000000000', 1)
rep('def aN (k : ℕ) : ℕ := 4 * pLoN * k', 'def aN (k : ℕ) : ℕ := 64 * pLoN * k', 1)
rep('def bN (k : ℕ) : ℕ := 4 * pHiN * k', 'def bN (k : ℕ) : ℕ := 64 * pHiN * k', 1)
left = [l for l in t.split('\n') if re.search(r'3 / 2|3/2|/ 3\b', l) and 'omHi k' not in l and 'ω / 3' not in l]
print('lines with / 3 left (check by hand):')
print('\n'.join(left))
open(sys.argv[2], 'w').write(t)
