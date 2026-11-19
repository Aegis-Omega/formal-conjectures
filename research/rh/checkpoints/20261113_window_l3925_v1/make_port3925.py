"""Derive the window 2r <= 39/25 scripts from the window 49/32 checkpoint (../20261112_window_l4932_v1/)
by counted substitution, as make_port3120.py of ../20261112_window_l3120_v1/ does for 31/20, with every
LT-dependent form computed from LT = p/q = 39/25: 2/LT, 4/LT, 1/LT, LT/2, LT^2, LT +- 1, 4 LT m, 2 LT,
LT/(2 pi^2), phi (16 q^2, p^2), e^{-LT/2} (Real.exp_bound, 24 terms), log 5 > LT (e^p < 5^q), LT/2001,
Dk = p 10^20, the check-matrix scale PS = 488 + 4 (bitlen(p^2) + 2) - 2 shift (shift from rescale_pkl.py),
the low tau target 3e-10 -> 3e-12 for k <= 156, the names 4932 -> 3925, and port_diag substituting K and
N before 2/LT (DIAG_FIX of make_port3120.py). Data constants of rr/port_rules3925.json: set_rules3925.py.
usage: python3 make_port3925.py L4932_DIR OUT_DIR"""
import re
import sys
from fractions import Fraction as F
from math import factorial, floor, ceil
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])
p, q = 39, 25
SHIFT = 11                                    # rescale_pkl.py on rr43_data.pkl (exponents -7 .. 11)
PS = 488 + 4 * ((p * p).bit_length() + 2) - 2 * SHIFT
TAG, ENAME = f'{p}{q}', f'e{p}{2 * q}'
FRONT, FRONT_DEC = 'thirty_nine_fiftieths', '0.78'
PREV = ('The previous frontier was `31/40` (`RHWindowL3120ExhaustionV1.rh_iff_windows_above_thirty_one_fortieths`).'
        '\\nNo hypothesis remains besides the windows `L > 39/50`')


def fr(x):
    return f'{x.numerator} / {x.denominator}'


def frs(x):
    return f'{x.numerator}/{x.denominator}'


LT, H = F(p, q), F(p, 2 * q)
x, n = -H, 24
S = sum(x ** m / factorial(m) for m in range(n)); err = abs(x) ** n * F(n + 1, factorial(n) * n)
eLo, eHi = floor((S - err) * 2 ** 88), ceil((S + err) * 2 ** 83)
assert F(2.7182818286) ** p < 5 ** q
assert 1 - F(4, 5) + 2 * F(6931471805, 10 ** 10) > LT                 # node_big: log 5 >= 1/5 + 2 log 2
c2, c4, c1 = F(2 * q, p), F(4 * q, p), F(q, p)                          # 2/LT, 4/LT, 1/LT
assert c2.denominator == c4.denominator == c1.denominator == p

LIT = [
    ('The previous frontier was `3/4` (`RHWindowL32ExhaustionV1.rh_iff_windows_above_three_quarters`).\\nNo hypothesis remains besides the windows `L > 49/64`',
     '@PREV@'),
    ('143923895647018040563762077', str(eLo)), ('4497621738969313767617565', str(eHi)), ('e4964', ENAME),
    ('Real.exp (49 / 32) ^ 32 = Real.exp 1 ^ 49', f'Real.exp ({p} / {q}) ^ {q} = Real.exp 1 ^ {p}'),
    ('Real.exp 1 ^ 49 < 5 ^ 32', f'Real.exp 1 ^ {p} < 5 ^ {q}'),
    ('(49 : ℕ) ≠ 0', f'({p} : ℕ) ≠ 0'),
    ('(2.7182818286 : ℝ) ^ 49 < 5 ^ 32', f'(2.7182818286 : ℝ) ^ {p} < 5 ^ {q}'),
    ('(not_lt.mp hc) 32', f'(not_lt.mp hc) {q}'),
    ('exp(49/32)^32 = e^49 < 5^32', f'exp({p}/{q})^{q} = e^{p} < 5^{q}'),
    ('phi with 49^2', f'phi with {p}^2'),
    ('49 / 64032', f'{p} / {q * 2001}'),
    ('2401 / 1024', fr(LT * LT)), ('81 / 32', fr(LT + 1)), ('17 / 32', fr(LT - 1)),
    ('1617 / 160', fr(4 * LT * F(33, 20))), ('49 / 16 * T', fr(2 * LT) + ' * T'), ('32 / 49', fr(1 / LT)),
    ('4096 / 2401', fr(c2 * c2)), ('4096/2401', frs(c2 * c2)),
    ('49 / (64 * Real.pi ^ 2)', f'{p} / ({2 * q} * Real.pi ^ 2)'), ('49/(64π²)', f'{p}/({2 * q}π²)'),
    ('64 * Real.pi ^ 2', f'{2 * q} * Real.pi ^ 2'),
    ('64πn/49', f'{2 * q}πn/{p}'), ('64πk/49', f'{2 * q}πk/{p}'), ('64 n log p / 49', f'{2 * q} n log p / {p}'),
    ('64 k log p / 49', f'{2 * q} k log p / {p}'), ('omega_k = 64 pi k / 49', f'omega_k = {2 * q} pi k / {p}'),
    ('a = 64 floor(pi)_20 k, D = 49 10^20', f'a = {2 * q} floor(pi)_20 k, D = {p} 10^20'),
    ('`a = 64⌊π⌋₂₀k`', f'`a = {2 * q}⌊π⌋₂₀k`'), ('`D = 49·10²⁰`', f'`D = {p}·10²⁰`'),
    ('mp.mpf(49) / 32', f'mp.mpf({p}) / {q}'), ('49 * 10 ** 20', f'{p} * 10 ** 20'),
    ('def Dk : ℕ := 4900000000000000000000', f'def Dk : ℕ := {p * 10 ** 20}'),
    ('LDL at 2^80 with P at 2^-520, so the interval shift is 440', f'LDL at 2^80 with P at 2^-{PS}, so the interval shift is {PS - 80}'),
    ('PS, Q = 520, 80', f'PS, Q = {PS}, 80'),
    ('64 * pLoN * k', f'{2 * q} * pLoN * k'), ('64 * pHiN * k', f'{2 * q} * pHiN * k'),
    ('F(49, 32)', f'F({p}, {q})'), ('(49, 32, 2000, 156)', f'({p}, {q}, 2000, 156)'),
    ('forty_nine_sixty_fourths', FRONT),
    ('49/32', frs(LT)), ('49 / 32', fr(LT)), ('49/64', frs(H)), ('49 / 64', fr(H)),
    ("return 3e-10 if k <= 156 else 3e-9'", "return 3e-12 if k <= 156 else 3e-9'"),
    ('`1.0·10⁻¹⁰` for `k ≤ 156`', '`1.0·10⁻¹²` for `k ≤ 156`'),
    ("(the row-check budget of\\n`../20261112_window_beyond_l32_feasibility_v1/`'",
     f"(the row-check budget of\\n`../20261112_window_l{TAG}_v1/FEASIBILITY_{TAG}.log`'"),
    ("('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)')])",
     "('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)'),\n"
     "    ('radius `5·10⁻¹¹` and `5·10⁻¹⁰`', 'radius `5·10⁻¹³` and `5·10⁻¹⁰`')])"),
]
RX = [(r'(?<![\d.])64 \* ([^/\n]{1,40}?) / 49(?![\d])', rf'{c2.numerator} * \1 / {p}'),
      (r'(?<![\d.])128 \* ([^/\n]{1,40}?) / 49(?![\d])', rf'{c4.numerator} * \1 / {p}'),
      (r'(?<![\d.])32 \* ([^/\n]{1,40}?) / 49(?![\d])', rf'{c1.numerator} * \1 / {p}'),
      (r'(?<!\d)16384(?!\d)', str(16 * q * q)), (r'(?<!\d)2401(?!\d)', str(p * p)),
      (r'(?<!\d)4932(?!\d)', TAG)]
DIAG_FIX = f"""

p = out / 'port_diag_l{TAG}.py'
L = p.read_text().split('\\n')
i = [k for k, l in enumerate(L) if l.startswith("    s, _ = re.subn(r'8 ")]
assert len(i) == 1 and L[i[0] + 1].startswith("    s, _ = re.subn(r'16 "), i
i = i[0]
assert [l[:30] for l in L[i + 2:i + 5]] == ["    s = re.sub(r'(?<![\\\\d.])40(", "    s = re.sub(r'(?<![\\\\d.])71(",
                                            "    s = re.sub(r'(?<![\\\\d.])70("], L[i + 2:i + 5]
L[i:i + 5] = L[i + 2:i + 5] + L[i:i + 2]
p.write_text('\\n'.join(L))
print('port_diag_l{TAG}.py: K and N substituted before 2/LT')
"""
SKIP = {'README.md', 'generated.sha256', 'cert4932_totals.json'}
LEFT = re.compile(r'(?<![\d.])(49|64|128|2401|4096|4932|4964)(?![\d])')

used = {a: 0 for a, _ in LIT}
for path in sorted(src.rglob('*')):
    if not path.is_file() or path.name in SKIP or path.suffix not in ('.py', '.sh', '.json', '.lean', '.txt'):
        continue
    t = path.read_text()
    for a, b in LIT:
        used[a] += t.count(a)
        t = t.replace(a, b)
    for a, b in RX:
        t = re.sub(a, b, t)
    t = t.replace('@PREV@', PREV)
    if path.name == 'make_diag_ports4932.py':
        t += DIAG_FIX
    dst = out / path.relative_to(src)
    dst = dst.with_name(re.sub(r'(?<!\d)4932(?!\d)', TAG, dst.name))
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(t)
    for i, l in enumerate(t.split('\n')):
        if LEFT.search(l.replace('2 ** 64', '').replace('2 ^ 64', '').replace('S64', '')):
            print(f'LEFT {dst.relative_to(out)}:{i + 1}: {l.strip()[:150]}')
print('PS', PS, 'e', eLo, eHi, 'unused:', [a for a, k in used.items() if k == 0])
