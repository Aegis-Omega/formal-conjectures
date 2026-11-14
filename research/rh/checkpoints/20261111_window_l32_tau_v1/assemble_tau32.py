"""Write CvSTauL32AllV1.lean: tau boxes at L = 3/2 for k = 1..900 from the 18 data modules
CvSTauL32K{1,51,...,851}V1 (50 entries each). usage: python3 assemble_tau32.py OUTDIR"""
import sys
from pathlib import Path
OUT = Path(sys.argv[1])
starts = list(range(1, 901, 50))
LIC = open(Path(__file__).parent / 'CvSNodeL32V1.lean').read().split('-/', 1)[0] + '-/\n'
def mod(s): return f'AEGIS.CvSTauL32K{s}V1'
t = LIC + ''.join(f'import CvSTauL32K{s}V1\n' for s in starts) + '''
/-!
# `τ_k` at `L = 3/2` for `k = 1, …, 900` and every prime cutoff `M ≥ 4`

The eighteen data modules `CvSTauL32K{1, 51, …, 851}V1` in one statement. Box widths at most
`1.0·10⁻¹⁰` for `k ≤ 150` and `1.0·10⁻⁹` for `150 < k ≤ 900` (the row-check budget of
`ROW_BOXES_20261111.md`: radius `5·10⁻¹¹` and `5·10⁻¹⁰`). Not RH.
-/

namespace AEGIS.CvSTauL32AllV1

open AEGIS.CvSRowTailV1

'''
def chain(field):
    out = f'def {field}All (k : ℕ) : ℚ :=\n'
    for s in starts[:-1]:
        out += f'  if k < {s + 50} then {mod(s)}.{field}.getD (k - {s}) 0 else\n'
    out += f'  {mod(starts[-1])}.{field}.getD (k - {starts[-1]}) 0\n\n'
    return out
t += chain('tLo') + chain('tHi')
t += '''/-- **`τ_k` at `L = 3/2` for `1 ≤ k ≤ 900`, every prime cutoff `M ≥ 4`.** -/
theorem tau_mem_all {M : ℕ} (hM : 4 ≤ M) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 900) :
    ((tLoAll k : ℚ) : ℝ) ≤ tau M (3 / 2) (k : ℤ) ∧ tau M (3 / 2) (k : ℤ) ≤ ((tHiAll k : ℚ) : ℝ) := by
'''
for i, s in enumerate(starts):
    negs = ' '.join(f'if_neg c{j},' for j in range(i))
    last = i == len(starts) - 1
    body = (f'    have h := {mod(s)}.tau_mem hM (i := k - {s}) (by omega)\n'
            f'    rw [show {mod(s)}.k0 + (k - {s}) = k by simp only [{mod(s)}.k0]; omega] at h\n'
            f'    simp only [tLoAll, tHiAll, {negs}{"" if last else f" if_pos c{i}"}]\n'
            f'    exact h\n')
    if not last:
        t += f'  by_cases c{i} : k < {s + 50}\n  · ' + body[4:].replace('\n    ', '\n    ', 0)
    else:
        t += body[2:].replace('\n    ', '\n  ')
t += '''
end AEGIS.CvSTauL32AllV1

#print axioms AEGIS.CvSTauL32AllV1.tau_mem_all
'''
t = t.replace('simp only [tLoAll, tHiAll, ]', 'simp only [tLoAll, tHiAll]').replace(', ]', ']').replace('[tLoAll, tHiAll,  if_pos', '[tLoAll, tHiAll, if_pos')
(OUT / 'CvSTauL32AllV1.lean').write_text(t)
print('written CvSTauL32AllV1.lean', t.count('\n'), 'lines')
