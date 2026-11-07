"""Untrusted generator of CvSTauR1SourceL43V1 and CvSTauR1PrimeL43V1: tau boxes at L = 4/3 for
k = 71..KMAX (the rows outside the low block), in kernel batches of 5.

Usage: python3 gen_tau_r1_43.py KMAX OUTDIR. Uses gen_tau43.py (source integrals) and
gen_tau_prime43.py (prime part); the kernel re-checks every box.
"""
import math
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import gen_tau43 as gs  # noqa: E402
import gen_tau_prime43 as gp  # noqa: E402

KMAX, OUT = int(sys.argv[1]), Path(sys.argv[2])
K0 = 71
assert (KMAX - K0 + 1) % 5 == 0
NB = (KMAX - K0 + 1) // 5
starts = [5 * i for i in range(NB)]

LICENSE = '''/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
'''

J, sLo, sHi = [], [], []
for k in range(K0, KMAX + 1):
    j = gs.pickJ(k)
    wl, wh, d, lo, hi = gs.box(k, j, 20)
    assert 1 <= wl and gs.j0 <= j and 2 < gs.cw(j) and wh ** 2 / 3 + 3 <= gs.cw(j) ** 2 and wh / d < 1
    assert lo >= 0 and hi >= 0
    J.append(j)
    sLo.append(F(math.floor(gs.piLo * lo * gs.P), gs.P))
    sHi.append(F(math.ceil(gs.piHi * hi * gs.P), gs.P))
print('-- max source width %.3e' % max(float(b - a) for a, b in zip(sLo, sHi)), file=sys.stderr)
fLo, fHi = gp.full_boxes(sLo, sHi, K0)

mem = '[' + ', '.join(map(str, starts)) + ']'
alts = ' | '.join(['rfl'] * NB)


def batches(name, fn):
    return '\n'.join(f'''set_option maxRecDepth 100000 in
theorem {name}_{s} : {fn} {s} = true := by decide +kernel
''' for s in starts)


def all_thm(name, fn):
    return f'''theorem {name}_all {{s : ℕ}} (hs : s ∈ {mem}) : {fn} s = true := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with {alts}
  exacts [{', '.join(f'{name}_{s}' for s in starts)}]
'''


def lookup(check, batch_all, fn):
    return f'''  have hs : 5 * ((k - 71) / 5) ∈ {mem} := by
    have : (k - 71) / 5 < {NB} := by omega
    interval_cases (k - 71) / 5 <;> simp
  have h := {batch_all} hs
  simp only [{fn}, List.all_eq_true, List.mem_range] at h
  have h' := h ((k - 71) % 5) (Nat.mod_lt _ (by norm_num))
  have hi : 5 * ((k - 71) / 5) + (k - 71) % 5 = k - 71 := by omega
  have hk : k - 71 + 71 = k := by omega
  simpa only [hi, hk] using h'
'''


src = LICENSE + f'''
import CvSTauL43V1

/-!
# Source integrals `∫ h₊ S_k` at `L = 4/3`, `71 ≤ k ≤ {KMAX}`

Boxes proposed by `tools/gen_tau_r1_43.py` (untrusted) and checked in batches of five by
`CvSTauL43V1.tauCheck` with `decide +kernel`; `CvSTauL43V1.tauCheck_sound` turns them into
enclosures. These are the digamma parts of `τ_k` for the rows `70 < |k| ≤ {KMAX}` of the `L = 4/3`
window. Not RH.
-/

open Finset

namespace AEGIS.CvSTauR1SourceL43V1

open AEGIS.CvSTauL43V1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchLorentzV1

/-- Cutoffs `J_k`, `k = 71, …, {KMAX}`. -/
def tauJExtra : List ℕ := [{', '.join(map(str, J))}]

{gp.lst('tauSrcLoExtra', sLo)}

{gp.lst('tauSrcHiExtra', sHi)}

/-- The checks for `k = s + 71, …, s + 75`. -/
def tauSourceBatchR1 (s : ℕ) : Bool :=
  (List.range 5).all fun i =>
    tauCheck (s + i + 71) (tauJExtra.getD (s + i) 0) 20
      (tauSrcLoExtra.getD (s + i) 0) (tauSrcHiExtra.getD (s + i) 0)

{batches('tauSourceBatchR1', 'tauSourceBatchR1')}
{all_thm('tauSourceBatchR1', 'tauSourceBatchR1')}
theorem tauSourceCheckR1_all {{k : ℕ}} (hk1 : 71 ≤ k) (hk2 : k ≤ {KMAX}) :
    tauCheck k (tauJExtra.getD (k - 71) 0) 20
      (tauSrcLoExtra.getD (k - 71) 0) (tauSrcHiExtra.getD (k - 71) 0) = true := by
{lookup('tauCheck', 'tauSourceBatchR1_all', 'tauSourceBatchR1')}
/-- **`∫ h₊ S_k` at `L = 4/3` for `k = 71, …, {KMAX}`.** -/
theorem source_integral_mem_R1 {{k : ℕ}} (hk1 : 71 ≤ k) (hk2 : k ≤ {KMAX}) :
    ((tauSrcLoExtra.getD (k - 71) 0 : ℚ) : ℝ) ≤ ∫ r, hplus r * sourceS (4 / 3) r (k : ℤ) ∧
      ∫ r, hplus r * sourceS (4 / 3) r (k : ℤ) ≤ ((tauSrcHiExtra.getD (k - 71) 0 : ℚ) : ℝ) :=
  tauCheck_sound (tauSourceCheckR1_all hk1 hk2)

end AEGIS.CvSTauR1SourceL43V1

#print axioms AEGIS.CvSTauR1SourceL43V1.source_integral_mem_R1
'''

prime = LICENSE + f'''
import CvSTauR1SourceL43V1
import CvSTauPrimeL43V1

/-!
# `τ_k` at `L = 4/3`, `71 ≤ k ≤ {KMAX}`

The source boxes of `CvSTauR1SourceL43V1` plus the prime part `CvSTauPrimeL43V1.prime_bounds`,
through `CvSTauPrimeL43V1.tau_eq`, for every prime cutoff `M ≥ 3` (data from
`tools/gen_tau_r1_43.py`, untrusted; batches of five). Not RH.
-/

open Finset

namespace AEGIS.CvSTauR1PrimeL43V1

open AEGIS.CvSTauR1SourceL43V1 AEGIS.CvSTauPrimeL43V1 AEGIS.CvSRowTailV1
open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchLorentzV1
open AEGIS.CvSTauPrimeL12V1 (thLo l2Lo l3Lo)

{gp.lst('tauFLoExtra', fLo)}

{gp.lst('tauFHiExtra', fHi)}

/-- The full check: source box plus the prime part, inside `[lo, hi]`. -/
def tauFullCheckR1 (k : ℕ) (lo hi : ℚ) : Bool :=
  decide (|thLo (3 * k * l2Lo / 2)| ≤ 2) && decide (|thLo (3 * k * l3Lo / 2)| ≤ 2) &&
    decide (lo ≤ tauSrcLoExtra.getD (k - 71) 0 + primeLo k) &&
    decide (tauSrcHiExtra.getD (k - 71) 0 + primeHi k ≤ hi)

theorem tauFullCheckR1_sound {{M : ℕ}} (hM : 3 ≤ M) {{k : ℕ}} (hk1 : 71 ≤ k) (hk2 : k ≤ {KMAX})
    {{lo hi : ℚ}} (h : tauFullCheckR1 k lo hi = true) :
    (lo : ℝ) ≤ tau M (4 / 3) k ∧ tau M (4 / 3) k ≤ hi := by
  simp only [tauFullCheckR1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, h3⟩, hl⟩, hh⟩ := h
  have hs := source_integral_mem_R1 hk1 hk2
  have hp := prime_bounds k h2 h3
  have hl' : (lo : ℝ) ≤ ((tauSrcLoExtra.getD (k - 71) 0 : ℚ) : ℝ) + (primeLo k : ℝ) := by
    exact_mod_cast hl
  have hh' : ((tauSrcHiExtra.getD (k - 71) 0 : ℚ) : ℝ) + (primeHi k : ℝ) ≤ hi := by
    exact_mod_cast hh
  rw [tau_eq hM]
  push_cast at hs hp ⊢
  constructor <;> linarith [hs.1, hs.2, hp.1, hp.2]

/-- The checks for `k = s + 71, …, s + 75`. -/
def tauPrimeBatchR1 (s : ℕ) : Bool :=
  (List.range 5).all fun i =>
    tauFullCheckR1 (s + i + 71) (tauFLoExtra.getD (s + i) 0) (tauFHiExtra.getD (s + i) 0)

{batches('tauPrimeBatchR1', 'tauPrimeBatchR1')}
{all_thm('tauPrimeBatchR1', 'tauPrimeBatchR1')}
theorem tauFullCheckR1_all {{k : ℕ}} (hk1 : 71 ≤ k) (hk2 : k ≤ {KMAX}) :
    tauFullCheckR1 k (tauFLoExtra.getD (k - 71) 0) (tauFHiExtra.getD (k - 71) 0) = true := by
{lookup('tauFullCheckR1', 'tauPrimeBatchR1_all', 'tauPrimeBatchR1')}
/-- **`τ_k` at `L = 4/3` for `k = 71, …, {KMAX}` and every prime cutoff `M ≥ 3`.** -/
theorem tau_mem_R1 {{M : ℕ}} (hM : 3 ≤ M) {{k : ℕ}} (hk1 : 71 ≤ k) (hk2 : k ≤ {KMAX}) :
    ((tauFLoExtra.getD (k - 71) 0 : ℚ) : ℝ) ≤ tau M (4 / 3) k ∧
      tau M (4 / 3) k ≤ ((tauFHiExtra.getD (k - 71) 0 : ℚ) : ℝ) :=
  tauFullCheckR1_sound hM hk1 hk2 (tauFullCheckR1_all hk1 hk2)

end AEGIS.CvSTauR1PrimeL43V1

#print axioms AEGIS.CvSTauR1PrimeL43V1.tauFullCheckR1_sound
#print axioms AEGIS.CvSTauR1PrimeL43V1.tau_mem_R1
'''

(OUT / 'CvSTauR1SourceL43V1.lean').write_text(src)
(OUT / 'CvSTauR1PrimeL43V1.lean').write_text(prime)
print('ok', NB, 'batches')
