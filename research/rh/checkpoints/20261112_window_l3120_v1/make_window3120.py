"""Write CvSWindowL3120V1.lean and RHWindowL3120ExhaustionV1.lean from the L = 3/2 modules of
../20261112_window_l32_v1/ (window 2r <= 31/20, M = 4, 311 atoms, R = 157, NP = 2000, kappa = 66, frontier
31/40). Every substitution is counted; log_five_gt gets a new proof (exp(31/20)^20 = e^31 < 5^20).
usage: python3 make_window3120.py L32_WINDOW_DIR OUTDIR"""
import sys
from pathlib import Path
src, out = Path(sys.argv[1]), Path(sys.argv[2])


def apply(t, R):
    for a, b, n in R:
        assert t.count(a) == n, (a, t.count(a), n)
        t = t.replace(a, b)
    return t


t = (src / 'CvSWindowL32V1.lean').read_text()
a = t.index('theorem log_five_gt'); b = t.index('/-- **The window')
t = t[:a] + '''theorem log_five_gt : (31 / 20 : ℝ) < Real.log ((4 + 1 : ℕ) : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have e : Real.exp (31 / 20) ^ 20 = Real.exp 1 ^ 31 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 ^ 31 < 5 ^ 20 := by
    have := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : (31 : ℕ) ≠ 0)
    linarith [show (2.7182818286 : ℝ) ^ 31 < 5 ^ 20 by norm_num]
  push_cast
  by_contra hc
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (not_lt.mp hc) 20
  linarith

''' + t[b:]
t = apply(t, [
    ('import CvSRelRowHBL32V1', 'import CvSRelRowHBL3120V1', 1), ('import CvSTraceCertL32V1', 'import CvSTraceCertL3120V1', 1),
    ('import CvSTauFarL32V1', 'import CvSTauFarL3120V1', 1),
    ('# The window `2r ≤ 3/2`', '# The window `2r ≤ 31/20`', 1),
    ('`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`',
     '`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 31/20`, `m = 33/20`', 1),
    ('`CvSTraceCertL32V1` (`trace_premises_L32`, `66 ≤ (2π)² LT (m − T/(2π))`), the 299 atoms centred\nat `−149, …, 149`, the rows up to `NP = 900` with `|τ_m| ≤ 15` beyond (`tau_abs_le_far`), and the\nrelative row budget `Brow ≤ 60 Q` of `CvSRelRowHBL32V1`. The conclusion holds for every\nmoment-zero test function of half-width `r` with `2r ≤ 3/2`.',
     '`CvSTraceCertL3120V1` (`trace_premises_L3120`, `66 ≤ (2π)² LT (m − T/(2π))`), the 311 atoms centred\nat `−155, …, 155`, the rows up to `NP = 2000` with `|τ_m| ≤ 15` beyond (`tau_abs_le_far`), and the\nrelative row budget `Brow ≤ 66 Q` of `CvSRelRowHBL3120V1`. The conclusion holds for every\nmoment-zero test function of half-width `r` with `2r ≤ 31/20`. As `CvSWindowL32V1` at `3/2`.', 1),
    ('namespace AEGIS.CvSWindowL32V1', 'namespace AEGIS.CvSWindowL3120V1', 1),
    ('end AEGIS.CvSWindowL32V1', 'end AEGIS.CvSWindowL3120V1', 1),
    ('#print axioms AEGIS.CvSWindowL32V1.', '#print axioms AEGIS.CvSWindowL3120V1.', 2),
    ('open AEGIS.CvSTraceCertL32V1 AEGIS.CvSTraceIntegralL32V1 AEGIS.CvSTraceDistK150V1',
     'open AEGIS.CvSTraceCertL3120V1 AEGIS.CvSTraceIntegralL3120V1 AEGIS.CvSTraceDistK156V1', 1),
    ('open AEGIS.CvSTraceCellL32V1 ', 'open AEGIS.CvSTraceCellL3120V1 ', 1),
    ('open AEGIS.CvSRelRowFormL32V1 AEGIS.CvSRelRowInL32V1 AEGIS.CvSRelRowHBL32V1',
     'open AEGIS.CvSRelRowFormL3120V1 AEGIS.CvSRelRowInL3120V1 AEGIS.CvSRelRowHBL3120V1', 1),
    ('/-- The 301-function trace family at `LT = 3/2` is a `TraceFamily`. -/', '/-- The 313-function trace family at `LT = 31/20` is a `TraceFamily`. -/', 1),
    ('Fin 299', 'Fin 311', 2), ('(3 / 2)', '(31 / 20)', 10), ('(3 / 2 : ℝ)', '(31 / 20 : ℝ)', 3),
    ('/-- **The window `2r ≤ 3/2`.** -/', '/-- **The window `2r ≤ 31/20`.** -/', 1),
    ('window_L32', 'window_L3120', 2), ('(h2r : 2 * r ≤ 3 / 2)', '(h2r : 2 * r ≤ 31 / 20)', 1),
    ('trace_premises_L32', 'trace_premises_L3120', 1), ('(cfC h32)', '(cfC h3120)', 1),
    ('hR hT hgap 151 900', 'hR hT hgap 157 2000', 1), ('|ctr i| ≤ 149', '|ctr i| ≤ 155', 1),
    ('AEGIS.CvSTauFarL32V1.tau_abs_le_far', 'AEGIS.CvSTauFarL3120V1.tau_abs_le_far', 1),
    ('(ε := 1) (by norm_num)', '(ε := 7 / 5) (by norm_num)', 1)])
assert 'L32' not in t.replace('CvSWindowL32V1` at', ''), [l for l in t.split('\n') if 'L32' in l]
import re
assert not re.search(r'(?<!\d)3 / 2(?!\d)', t), [l for l in t.split('\n') if re.search(r'(?<!\d)3 / 2(?!\d)', l)]
(out / 'CvSWindowL3120V1.lean').write_text(t)

t = (src / 'RHWindowL32ExhaustionV1.lean').read_text()
t = apply(t, [
    ('import CvSWindowL32V1', 'import CvSWindowL3120V1', 1),
    ('# The window `2r ≤ 3/2` in the window-exhaustion chain', '# The window `2r ≤ 31/20` in the window-exhaustion chain', 1),
    ('`CvSWindowL32V1.window_L32` closes every window with `L ≤ 3/4`, with no hypotheses:',
     '`CvSWindowL3120V1.window_L3120` closes every window with `L ≤ 31/40`, with no hypotheses:', 1),
    ('three_quarters', 'thirty_one_fortieths', 11),
    ('every log window with `L ≤ 3/4` has the arithmetic sign;', 'every log window with `L ≤ 31/40` has the arithmetic sign;', 1),
    ('the sign on the windows `L > 3/4`;', 'the sign on the windows `L > 31/40`;', 1),
    ('RH is equivalent to the sign on the windows\n  `L > 3/4`.', 'RH is equivalent to the sign on the windows\n  `L > 31/40`.', 1),
    ('The previous frontier was `11/16` (`RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths`).\nNo hypothesis remains besides the windows `L > 3/4`, which are not proved. Not RH.',
     'The previous frontier was `49/64` (`RHWindowL4932ExhaustionV1.rh_iff_windows_above_forty_nine_sixty_fourths`).\nNo hypothesis remains besides the windows `L > 31/40`, which are not proved. Not RH.', 1),
    ('namespace AEGIS.RHWindowL32ExhaustionV1', 'namespace AEGIS.RHWindowL3120ExhaustionV1', 1),
    ('end AEGIS.RHWindowL32ExhaustionV1', 'end AEGIS.RHWindowL3120ExhaustionV1', 1),
    ('#print axioms AEGIS.RHWindowL32ExhaustionV1.', '#print axioms AEGIS.RHWindowL3120ExhaustionV1.', 3),
    ('open AEGIS.CvSWindowL32V1', 'open AEGIS.CvSWindowL3120V1', 1),
    ('/-- Every log window `[−L, L]` with `L ≤ 3/4` has the arithmetic sign. -/', '/-- Every log window `[−L, L]` with `L ≤ 31/40` has the arithmetic sign. -/', 1),
    ('(hL : L ≤ 3 / 4)', '(hL : L ≤ 31 / 40)', 1), ('(window_L32 g hm L 0 hw (by linarith))', '(window_L3120 g hm L 0 hw (by linarith))', 1),
    ('/-- The final sign residual is equivalent to the sign on the windows `L > 3/4`. -/', '/-- The final sign residual is equivalent to the sign on the windows `L > 31/40`. -/', 1),
    ('3 / 4 < L', '31 / 40 < L', 2), ('rcases le_or_gt L (3 / 4)', 'rcases le_or_gt L (31 / 40)', 1),
    ('/-- RH is equivalent to the sign on the windows `L > 3/4`. -/', '/-- RH is equivalent to the sign on the windows `L > 31/40`. -/', 1)])
assert '3 / 4' not in t and '3/4' not in t.replace('`3/4` (`RHWindowL32', ''), [l for l in t.split('\n') if '3/4' in l or '3 / 4' in l]
(out / 'RHWindowL3120ExhaustionV1.lean').write_text(t)
print('written CvSWindowL3120V1.lean, RHWindowL3120ExhaustionV1.lean')
