"""Derive the window 2r <= 31/20 scripts from the window 49/32 checkpoint (../20261112_window_l4932_v1/)
by counted substitution: LT 49/32 -> 31/20 (2/LT = 64/49 -> 40/31, 4/LT = 128/49 -> 80/31, LT/2 = 49/64 ->
31/40, LT^2, LT +- 1), e^{-49/64} -> e^{-31/40}, log 5 > LT (e^31 < 5^20), the far cutoff LT/2001, the low
tau boxes tightened (target 3e-10 -> 3e-11 for k <= 156) and the names 4932 -> 3120. Three rules go beyond
the literal LT forms (each found by the kernel): port_diag substitutes K and N before 2/LT (DIAG_FIX), the
numeral Dk = 49 10^20 of make_taufast, and the check-matrix scale PS = 516 (Pscale at DEN = 31^2).
Data-dependent constants of rr/port_rules3120.json are set afterwards by set_rules3120.py.
usage: python3 make_port3120.py L4932_DIR OUT_DIR"""
import re
import sys
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])

LIT = [
    # the exhaustion module names the 49/32 frontier as the previous one (restored after the rules below)
    ('The previous frontier was `3/4` (`RHWindowL32ExhaustionV1.rh_iff_windows_above_three_quarters`).\\nNo hypothesis remains besides the windows `L > 49/64`',
     '@PREV@'),
    # e^{-LT/2}: Real.exp_bound, 24 terms, as for e^{-49/64}
    ('143923895647018040563762077', '142580914187195743784704817'),
    ('4497621738969313767617565', '4455653568349866993272026'),
    ('e4964', 'e3140'),
    # log 5 > LT
    ('Real.exp (49 / 32) ^ 32 = Real.exp 1 ^ 49', 'Real.exp (31 / 20) ^ 20 = Real.exp 1 ^ 31'),
    ('Real.exp 1 ^ 49 < 5 ^ 32', 'Real.exp 1 ^ 31 < 5 ^ 20'),
    ('(49 : ℕ) ≠ 0', '(31 : ℕ) ≠ 0'),
    ('(2.7182818286 : ℝ) ^ 49 < 5 ^ 32', '(2.7182818286 : ℝ) ^ 31 < 5 ^ 20'),
    ('(not_lt.mp hc) 32', '(not_lt.mp hc) 20'),
    ('exp(49/32)^32 = e^49 < 5^32', 'exp(31/20)^20 = e^31 < 5^20'),
    ('phi with 49^2', 'phi with 31^2'),
    # far tau: LT / 2001
    ('49 / 64032', '31 / 40020'),
    # trace: LT^2, LT + 1, LT - 1, 4 LT m, 2 LT, 1/LT
    ('2401 / 1024', '961 / 400'), ('81 / 32', '51 / 20'), ('17 / 32', '11 / 20'),
    ('1617 / 160', '1023 / 100'), ('49 / 16 * T', '31 / 10 * T'), ('32 / 49', '20 / 31'),
    # rows: (2/LT)^2, LT/(2 pi^2), phi
    ('4096 / 2401', '1600 / 961'), ('4096/2401', '1600/961'),
    ('49 / (64 * Real.pi ^ 2)', '31 / (40 * Real.pi ^ 2)'), ('49/(64π²)', '31/(40π²)'),
    ('64 * Real.pi ^ 2', '40 * Real.pi ^ 2'),
    # 2/LT in prose and code
    ('64πn/49', '40πn/31'), ('64πk/49', '40πk/31'), ('64 n log p / 49', '40 n log p / 31'),
    ('64 k log p / 49', '40 k log p / 31'), ('omega_k = 64 pi k / 49', 'omega_k = 40 pi k / 31'),
    ('a = 64 floor(pi)_20 k, D = 49 10^20', 'a = 40 floor(pi)_20 k, D = 31 10^20'),
    ('`a = 64⌊π⌋₂₀k`', '`a = 40⌊π⌋₂₀k`'), ('`D = 49·10²⁰`', '`D = 31·10²⁰`'),
    ('mp.mpf(49) / 32', 'mp.mpf(31) / 20'), ('49 * 10 ** 20', '31 * 10 ** 20'),
    ('def Dk : ℕ := 4900000000000000000000', 'def Dk : ℕ := 3100000000000000000000'),
    # Pscale = 488 + 4 (bitlen(DEN) + 2) - 2 shift: 544 - 24 = 520 at 49/32 (DEN = 2401), 536 - 20 = 516 at 31/20
    ('LDL at 2^80 with P at 2^-520, so the interval shift is 440', 'LDL at 2^80 with P at 2^-516, so the interval shift is 436'),
    ('PS, Q = 520, 80', 'PS, Q = 516, 80'),
    ('64 * pLoN * k', '40 * pLoN * k'), ('64 * pHiN * k', '40 * pHiN * k'),
    ('F(49, 32)', 'F(31, 20)'), ('(49, 32, 2000, 156)', '(31, 20, 2000, 156)'),
    # frontier
    ('forty_nine_sixty_fourths', 'thirty_one_fortieths'),
    # LT
    ('49/32', '31/20'), ('49 / 32', '31 / 20'), ('49/64', '31/40'), ('49 / 64', '31 / 40'),
    # low tau boxes
    ("return 3e-10 if k <= 156 else 3e-9'", "return 3e-11 if k <= 156 else 3e-9'"),
    ('`1.0·10⁻¹⁰` for `k ≤ 156`', '`1.0·10⁻¹¹` for `k ≤ 156`'),
    ("(the row-check budget of\\n`../20261112_window_beyond_l32_feasibility_v1/`'",
     "(the row-check budget of\\n`../20261112_window_l3120_v1/FEASIBILITY_3120.log`'"),
    ("('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)')])",
     "('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)'),\n"
     "    ('radius `5·10⁻¹¹` and `5·10⁻¹⁰`', 'radius `5·10⁻¹²` and `5·10⁻¹⁰`')])"),
]
RX = [(r'(?<![\d.])64 \* ([^/\n]{1,40}?) / 49(?![\d])', r'40 * \1 / 31'),
      (r'(?<![\d.])128 \* ([^/\n]{1,40}?) / 49(?![\d])', r'80 * \1 / 31'),
      (r'(?<![\d.])32 \* ([^/\n]{1,40}?) / 49(?![\d])', r'20 * \1 / 31'),
      (r'(?<!\d)16384(?!\d)', '6400'), (r'(?<!\d)2401(?!\d)', '961'),
      (r'(?<!\d)4932(?!\d)', '3120')]
# 2/LT = 40/31 contains the token 40 (K = 40 of the 11/8 diagonal), which port_diag substitutes by K after
# the 2/LT rules; at 49/32 (64/49) the order did not matter. Substitute K and N first.
DIAG_FIX = r"""

p = out / 'port_diag_l3120.py'
L = p.read_text().split('\n')
i = [k for k, l in enumerate(L) if l.startswith("    s, _ = re.subn(r'8 ")]
assert len(i) == 1 and L[i[0] + 1].startswith("    s, _ = re.subn(r'16 "), i
i = i[0]
assert [l[:30] for l in L[i + 2:i + 5]] == ["    s = re.sub(r'(?<![\\d.])40(", "    s = re.sub(r'(?<![\\d.])71(",
                                            "    s = re.sub(r'(?<![\\d.])70("], L[i + 2:i + 5]
L[i:i + 5] = L[i + 2:i + 5] + L[i:i + 2]
p.write_text('\n'.join(L))
print('port_diag_l3120.py: K and N substituted before 2/LT')
"""
SKIP = {'README.md', 'generated.sha256', 'cert4932_totals.json'}
LEFT = re.compile(r'(?<![\d.])(49|64|128|2401|4096|4932|4964)(?![\d])')

used = {a: 0 for a, _ in LIT}
for p in sorted(src.rglob('*')):
    if not p.is_file() or p.name in SKIP or p.suffix not in ('.py', '.sh', '.json', '.lean', '.txt'):
        continue
    t = p.read_text()
    for a, b in LIT:
        used[a] += t.count(a)
        t = t.replace(a, b)
    for a, b in RX:
        t = re.sub(a, b, t)
    t = t.replace('@PREV@', 'The previous frontier was `49/64` (`RHWindowL4932ExhaustionV1.rh_iff_windows_above_forty_nine_sixty_fourths`).\\nNo hypothesis remains besides the windows `L > 31/40`')
    if p.name == 'make_diag_ports4932.py':
        t += DIAG_FIX
    q = out / p.relative_to(src)
    q = q.with_name(re.sub(r'(?<!\d)4932(?!\d)', '3120', q.name))
    q.parent.mkdir(parents=True, exist_ok=True)
    q.write_text(t)
    for i, l in enumerate(t.split('\n')):
        if LEFT.search(l.replace('2 ** 64', '').replace('2 ^ 64', '').replace('S64', '')):
            print(f'LEFT {q.relative_to(out)}:{i + 1}: {l.strip()[:150]}')
print('unused:', [a for a, n in used.items() if n == 0])
