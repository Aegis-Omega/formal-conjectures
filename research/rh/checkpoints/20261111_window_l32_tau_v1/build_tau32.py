"""Write the data module CvSTauL32K{K1}V1.lean: tau boxes at L = 3/2 for k = K1..K2 (from the untrusted
mirror gen_tau32f.py), kernel-checked in batches of 5 by CvSTauFastL32V1.tauF.
usage: python3 build_tau32.py K1 K2 OUTDIR"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import gen_tau32f as g

K1, K2, OUT = int(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
n = K2 - K1 + 1
name = f'CvSTauL32K{K1}V1'
rows = [g.box(k, g.tgt_of(k)) for k in range(K1, K2 + 1)]
worst = max(float(hi - lo) for _, lo, hi in rows)
LIC = open(Path(__file__).parent / 'CvSNodeL32V1.lean').read().split('-/', 1)[0] + '-/\n'
P = g.S48
def q(x): return f'{x.numerator * (P // x.denominator)} / {P}'
starts = list(range(0, n, 5))
t = LIC + f'''import CvSTauFastL32V1

/-!
# `τ_k` at `L = 3/2`, `k = {K1}, …, {K2}`

Boxes from the untrusted mirror `gen_tau32f.py` (worst width `{worst:.3e}`), checked in batches of
five by `CvSTauFastL32V1.tauF` with `decide +kernel`; `tau_mem` encloses `τ_k` for every prime
cutoff `M ≥ 4`. Not RH.
-/

namespace AEGIS.{name}

open AEGIS.CvSTauFastL32V1 AEGIS.CvSRowTailV1

def k0 : ℕ := {K1}

def tJ : List ℕ := [{', '.join(str(J) for J, _, _ in rows)}]

def tLo : List ℚ := [
  {(',' + chr(10) + '  ').join(q(lo) for _, lo, _ in rows)}]

def tHi : List ℚ := [
  {(',' + chr(10) + '  ').join(q(hi) for _, _, hi in rows)}]

def bat (s len : ℕ) : Bool :=
  (List.range' s len).all fun i => tauF (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0)

'''
for s in starts:
    t += f'set_option maxRecDepth 100000 in\ntheorem bat_{s} : bat {s} {min(5, n - s)} = true := by decide +kernel\n\n'
t += f'''theorem ok {{i : ℕ}} (hi : i < {n}) :
    tauF (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0) = true := by
  have H : ∀ s len, bat s len = true → s ≤ i → i < s + len →
      tauF (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0) = true := by
    intro s len h h1 h2
    simp only [bat, List.all_eq_true] at h
    exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)
'''
for s in starts[:-1]:
    t += f'  by_cases h{s} : i < {s + 5}\n  · exact H {s} 5 bat_{s} (by omega) (by omega)\n'
s = starts[-1]
t += f'''  exact H {s} {min(5, n - s)} bat_{s} (by omega) (by omega)

/-- **`τ_k` at `L = 3/2` for `k = {K1}, …, {K2}` and every prime cutoff `M ≥ 4`.** -/
theorem tau_mem {{M : ℕ}} (hM : 4 ≤ M) {{i : ℕ}} (hi : i < {n}) :
    ((tLo.getD i 0 : ℚ) : ℝ) ≤ tau M (3 / 2) ((k0 + i : ℕ) : ℤ) ∧
      tau M (3 / 2) ((k0 + i : ℕ) : ℤ) ≤ ((tHi.getD i 0 : ℚ) : ℝ) :=
  tauF_sound hM (ok hi)

end AEGIS.{name}

#print axioms AEGIS.{name}.tau_mem
'''
(OUT / f'{name}.lean').write_text(t)
print(name, 'k', K1, K2, 'worst width %.3e' % worst, 'max J', max(J for J, _, _ in rows))
