/-
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
import WeilH64CrossV7
import WeilThreeBlockPrimeEvaluationV30

/-!
# OPTIMUS V7: the prime sector of a separated pair

For `p` left of `q` (`phi < qlo`), with `lo = qlo − phi`, `hi = qhi − plo`, on the actual repository
prime sum `WeilPrimeSumV1 (mixed p q)`:

* every sample `mixed p q m` (`m ≥ 1`) vanishes, and `mixed p q (1/m)` vanishes unless `log m ∈ [lo, hi]`;
* `prime_sum_zero`: if `log 2 ∉ [lo, hi]` and `hi < log 3`, the prime sum is `0`;
* `prime_sum_norm_le`: if `hi < log 3`, `‖prime sum‖ ≤ (log 2/√2) (E_p + E_q)/2` (V7 §2: the only
  possible term is `m = 2`, with `|ρ| ≤ 1`);
* `B_sep_norm_le`: `‖B p q‖ ≤ ‖prime sum‖ + ‖Arch‖` (the centre value vanishes).

Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators

noncomputable section

namespace AEGIS.WeilH64PrimeV7

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilH64CrossV7

variable {p q : WeilCompactSmoothGV1} {plo phi qlo qhi : ℝ}

theorem mixed_exp_zero (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) {u : ℝ}
    (hu : u < plo - qhi ∨ phi - qlo < u) : mixed p q (Real.exp u) = 0 := by
  have hc := logCross_zero_outside p q plo phi qlo qhi u hp hq hu
  rw [logCross_eq_mixed_v28] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by simp)

theorem mixed_nat_zero (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    {m : ℕ} (hm : 0 < m) : mixed p q (m : ℝ) = 0 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := mixed_exp_zero hp hq (u := Real.log m) (Or.inr (by linarith [Real.log_nonneg hm1]))
  rwa [Real.exp_log (by linarith)] at h

theorem mixed_inv_nat_zero (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    {m : ℕ} (hm : 0 < m) (hout : Real.log m < qlo - phi ∨ qhi - plo < Real.log m) :
    mixed p q ((m : ℝ)⁻¹) = 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mixed_exp_zero hp hq (u := -Real.log m) (by
    rcases hout with h | h
    · right; linarith
    · left; linarith)
  rwa [Real.exp_neg, Real.exp_log hm0] at h

/-- Every prime term with `m = n + 1 ≥ 3` vanishes when `hi < log 3`. -/
theorem term_zero_ge_three (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (h3 : qhi - plo < Real.log 3) {n : ℕ} (hn : 2 ≤ n) : WeilPrimeTermV1 (mixed p q) n = 0 := by
  have hm : (3 : ℝ) ≤ (n + 1 : ℕ) := by push_cast; exact_mod_cast (by omega : 3 ≤ n + 1)
  have hlog : Real.log 3 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) hm
  have hz := mixed_nat_zero hp hq hsep (m := n + 1) (by omega)
  have hi := mixed_inv_nat_zero hp hq (m := n + 1) (by omega) (Or.inr (by linarith))
  simp only [WeilPrimeTermV1, hz, hi, mul_zero, add_zero]

theorem term_zero_one : WeilPrimeTermV1 (mixed p q) 0 = 0 := by
  simp [WeilPrimeTermV1]

/-- With `hi < log 3` only `m = 2` survives. -/
theorem prime_sum_single (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (h3 : qhi - plo < Real.log 3) :
    WeilPrimeSumV1 (mixed p q) = WeilPrimeTermV1 (mixed p q) 1 := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single 1
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · exact term_zero_one
    · exact absurd rfl hn
  · exact term_zero_ge_three hp hq hsep h3 h

/-- **No prime**: `log 2 ∉ [lo, hi]` and `hi < log 3`. -/
theorem prime_sum_zero (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (h3 : qhi - plo < Real.log 3) (h2 : Real.log 2 < qlo - phi ∨ qhi - plo < Real.log 2) :
    WeilPrimeSumV1 (mixed p q) = 0 := by
  rw [prime_sum_single hp hq hsep h3]
  have hz : mixed p q (2 : ℝ) = 0 := by exact_mod_cast mixed_nat_zero hp hq hsep (m := 2) (by norm_num)
  have hi : mixed p q (2 : ℝ)⁻¹ = 0 := by
    exact_mod_cast mixed_inv_nat_zero hp hq (m := 2) (by norm_num) (by exact_mod_cast h2)
  change (ArithmeticFunction.vonMangoldt 2 : ℂ) *
    (mixed p q ((2 : ℕ) : ℝ) + (1 / ((2 : ℕ) : ℂ)) * mixed p q (((2 : ℕ) : ℝ))⁻¹) = 0
  push_cast
  rw [hz, hi]
  ring

/-- `‖mixed p q (1/2)‖ = √2 ‖C_pq(−log 2)‖`. -/
theorem mixed_half_norm (p q : WeilCompactSmoothGV1) :
    ‖mixed p q ((2 : ℝ)⁻¹)‖ = Real.sqrt 2 * ‖logCrossV28 p q (-Real.log 2)‖ := by
  have h := logCross_eq_mixed_v28 p q (-Real.log 2)
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at h
  have he : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring, Real.exp_neg,
      AEGIS.WeilThreeBlockPrimeEvaluationV30.exp_log_two_half]
  rw [h, norm_mul, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

/-- **The matched prime entry**: `‖prime sum‖ ≤ (log 2/√2) (E_p + E_q)/2`. -/
theorem prime_sum_norm_le (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (h3 : qhi - plo < Real.log 3) :
    ‖WeilPrimeSumV1 (mixed p q)‖ ≤ Real.log 2 / Real.sqrt 2 * ((energy p.1 + energy q.1) / 2) := by
  rw [prime_sum_single hp hq hsep h3]
  have hz := mixed_nat_zero hp hq hsep (m := 2) (by norm_num)
  have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  have hterm : WeilPrimeTermV1 (mixed p q) 1 =
      (Real.log 2 : ℂ) * ((1 / 2 : ℂ) * mixed p q ((2 : ℝ)⁻¹)) := by
    change (ArithmeticFunction.vonMangoldt 2 : ℂ) *
      (mixed p q ((2 : ℕ) : ℝ) + (1 / ((2 : ℕ) : ℂ)) * mixed p q (((2 : ℕ) : ℝ))⁻¹) = _
    rw [hz, hv]
    push_cast
    ring
  rw [hterm, norm_mul, norm_mul, mixed_half_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hc := logCross_norm_le p q (-Real.log 2)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h12]
  set X := ‖logCrossV28 p q (-Real.log 2)‖
  have key : Real.log 2 * (1 / 2 * (Real.sqrt 2 * X)) = Real.log 2 / Real.sqrt 2 * X := by
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hs.ne']
    have e : Real.log 2 * (1 / 2 * (Real.sqrt 2 * X)) * Real.sqrt 2 =
        Real.log 2 * X * ((Real.sqrt 2 * Real.sqrt 2) / 2) := by ring
    rw [e, hs2]
    ring
  rw [key]
  exact mul_le_mul_of_nonneg_left hc (div_nonneg hl.le hs.le)

/-- **A separated entry splits into prime and Archimedean parts.** -/
theorem B_sep_norm_le (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ + ‖WeilArchimedeanIntegralV1 (mixed p q)‖ := by
  unfold B WeilExplicitRightSideV1
  rw [mixed_one_zero p q hp hq hsep, mul_zero, add_zero]
  exact norm_add_le _ _

end AEGIS.WeilH64PrimeV7

#print axioms AEGIS.WeilH64PrimeV7.prime_sum_zero
#print axioms AEGIS.WeilH64PrimeV7.prime_sum_norm_le
#print axioms AEGIS.WeilH64PrimeV7.B_sep_norm_le
