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
import CvSArchLorentzV1
import Mathlib.Analysis.PSeries

/-!
# The archimedean source integral, summed over the digamma series (CvS step 5.2b)

For `S(r) = sourceS L r n` and `ω = 2πn/L`:

* `(r² − ω²) S(r) = ω (1 − cos(rL))`, so `|S(r)| ≤ K/(1 + r²)` and `S` is integrable;
* `∫ S = 0` (all constants drop out of the archimedean functional);
* with `c_k = 2k + 1/2` and `a_k(r) = 1/(k+1) − 2c_k/(c_k² + r²)` (the real parts of the digamma
  series terms at `1/4 + ir/2`), for every constant `C`
  `∫ (∑' k, a_k(r) − C) S(r) dr = ∑' k, 2πω(1 − e^{−c_k L})/(c_k² + ω²)`.
-/

open MeasureTheory Set Real

noncomputable section

namespace AEGIS.CvSArchSourceV1

open AEGIS.CvSArchLorentzV1

theorem source_hasDerivAt (ω r y : ℝ) :
    HasDerivAt (fun y => ω * Real.cos (ω * y) * Real.cos (r * y) +
      r * Real.sin (ω * y) * Real.sin (r * y))
      ((r ^ 2 - ω ^ 2) * (Real.sin (ω * y) * Real.cos (r * y))) y := by
  have hs : ∀ a : ℝ, HasDerivAt (fun y => Real.sin (a * y)) (Real.cos (a * y) * a) y :=
    fun a => by simpa using ((hasDerivAt_id y).const_mul a).sin
  have hc : ∀ a : ℝ, HasDerivAt (fun y => Real.cos (a * y)) (-Real.sin (a * y) * a) y :=
    fun a => by simpa using ((hasDerivAt_id y).const_mul a).cos
  refine ((((hc ω).const_mul ω).mul (hc r)).add (((hs ω).const_mul r).mul (hs r))).congr_deriv ?_
  ring

/-- **Source identity.** `(r² − ω²) S(r, n, L) = ω (1 − cos(rL))`, `ω = 2πn/L`. -/
theorem source_identity {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) :
    (r ^ 2 - (2 * π * n / L) ^ 2) * sourceS L r n =
      2 * π * n / L * (1 - Real.cos (r * L)) := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  have hS : sourceS L r n = -∫ y in (0 : ℝ)..L, Real.sin (ω * y) * Real.cos (r * y) := by
    simp only [sourceS]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext y
    rw [sin_node L y n, hω]; ring
  rw [hω, hS, mul_neg, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => source_hasDerivAt ω r y)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  have hωL : ω * L = n * (2 * π) := by rw [← hω]; field_simp
  rw [hωL, sin_int_mul_two_pi', Real.cos_int_mul_two_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem sourceS_abs_le {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) : |sourceS L r n| ≤ L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
    (f := fun y => Real.sin (2 * π * n * (1 - y / L)) * Real.cos (r * y)) (C := 1)
    (fun y _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
  simpa [sourceS, abs_of_pos hL] using h

theorem sq_mul_sourceS_abs_le {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) :
    |r ^ 2 * sourceS L r n| ≤ (2 * π * n / L) ^ 2 * L + 2 * |2 * π * n / L| := by
  have hid := source_identity hL n r
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  rw [hω] at hid ⊢
  have h1 : r ^ 2 * sourceS L r n = ω ^ 2 * sourceS L r n + ω * (1 - Real.cos (r * L)) := by
    linear_combination hid
  rw [h1]
  have hS := sourceS_abs_le hL n r
  have hcos : |1 - Real.cos (r * L)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (r * L), Real.cos_le_one (r * L)]
  calc |ω ^ 2 * sourceS L r n + ω * (1 - Real.cos (r * L))|
      ≤ |ω ^ 2 * sourceS L r n| + |ω * (1 - Real.cos (r * L))| := abs_add_le _ _
    _ = ω ^ 2 * |sourceS L r n| + |ω| * |1 - Real.cos (r * L)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ω)]
    _ ≤ ω ^ 2 * L + |ω| * 2 := by gcongr
    _ = ω ^ 2 * L + 2 * |ω| := by ring

theorem sourceS_continuous (L : ℝ) (n : ℤ) : Continuous fun r => sourceS L r n := by
  unfold sourceS
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by
      show Continuous fun p : ℝ × ℝ => Real.sin (2 * π * n * (1 - p.2 / L)) * Real.cos (p.1 * p.2)
      fun_prop) 0 L

/-- The constant of the decay bound `|S(r)| ≤ K/(1 + r²)`. -/
def sourceK (L : ℝ) (n : ℤ) : ℝ := L + (2 * π * n / L) ^ 2 * L + 2 * |2 * π * n / L|

theorem sourceS_bound {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) :
    |sourceS L r n| ≤ sourceK L n * (1 + r ^ 2)⁻¹ := by
  have h1 := sourceS_abs_le hL n r
  have h2 := sq_mul_sourceS_abs_le hL n r
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)] at h2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), sourceK]
  calc |sourceS L r n| * (1 + r ^ 2) = |sourceS L r n| + r ^ 2 * |sourceS L r n| := by ring
    _ ≤ _ := by linarith

theorem sourceS_integrable {L : ℝ} (hL : 0 < L) (n : ℤ) : Integrable fun r => sourceS L r n := by
  refine (integrable_inv_one_add_sq.const_mul (sourceK L n)).mono'
    (sourceS_continuous L n).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs]
  exact sourceS_bound hL n r

/-- Total mass of the Lorentzian: `∫ 2c/(c² + r²) dr = 2π`. -/
theorem lorentz_total {c : ℝ} (hc : 0 < c) : ∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) = 2 * π := by
  simpa using lorentz_cos_integral hc 0

theorem inv_lorentz_integrable {c : ℝ} (hc : 0 < c) :
    Integrable fun r : ℝ => (c ^ 2 + r ^ 2)⁻¹ := by
  refine ((lorentz_integrable hc one_ne_zero).const_mul (1 / (2 * c))).congr
    (Filter.Eventually.of_forall fun r => ?_)
  have : c ^ 2 + r ^ 2 ≠ 0 := by positivity
  simp only [one_mul]
  field_simp

theorem inv_lorentz_integral {c : ℝ} (hc : 0 < c) : ∫ r : ℝ, (c ^ 2 + r ^ 2)⁻¹ = π / c := by
  have h : (fun r : ℝ => (c ^ 2 + r ^ 2)⁻¹) = fun r => 1 / (2 * c) * (2 * c / (c ^ 2 + r ^ 2)) := by
    funext r
    have : c ^ 2 + r ^ 2 ≠ 0 := by positivity
    field_simp
  rw [h, integral_const_mul, lorentz_total hc]
  field_simp

/-- If `|x| ≤ A/c` for every `c > 0`, then `x = 0`. -/
theorem eq_zero_of_abs_le_div {x A : ℝ} (h : ∀ c : ℝ, 0 < c → |x| ≤ A / c) : x = 0 := by
  by_contra hx
  have hx' : 0 < |x| := abs_pos.mpr hx
  have hc : 0 < (|A| + 1) / |x| := by positivity
  have h' := h _ hc
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)] at h'
  nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self A)) hx'.le]

/-- **The archimedean source has zero mean**: `∫ S(r, n, L) dr = 0`. -/
theorem sourceS_integral_eq_zero {L : ℝ} (hL : 0 < L) (n : ℤ) : ∫ r : ℝ, sourceS L r n = 0 := by
  have hSint := sourceS_integrable hL n
  have hB := fun r => sq_mul_sourceS_abs_le hL n r
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  simp only [hω] at hB
  refine eq_zero_of_abs_le_div (A := π * |ω| + (ω ^ 2 * L + 2 * |ω|) * π) fun c hc => ?_
  have hden : ∀ r : ℝ, 0 < c ^ 2 + r ^ 2 := fun r => by positivity
  have hTint : Integrable fun r : ℝ => r ^ 2 * sourceS L r n * (c ^ 2 + r ^ 2)⁻¹ := by
    refine ((inv_lorentz_integrable hc).const_mul (ω ^ 2 * L + 2 * |ω|)).mono' ?_
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (((continuous_pow 2).mul (sourceS_continuous L n)).mul
        ((continuous_const.add (continuous_pow 2)).inv₀ fun r => (hden r).ne')).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (hden r)]
      exact mul_le_mul_of_nonneg_right (hB r) (inv_nonneg.mpr (hden r).le)
  have hJ : |∫ r : ℝ, r ^ 2 * sourceS L r n * (c ^ 2 + r ^ 2)⁻¹| ≤
      (ω ^ 2 * L + 2 * |ω|) * π / c := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((inv_lorentz_integrable hc).const_mul
      (ω ^ 2 * L + 2 * |ω|)) (Filter.Eventually.of_forall fun r => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (hden r)]
      exact mul_le_mul_of_nonneg_right (hB r) (inv_nonneg.mpr (hden r).le)
    · rw [integral_const_mul, inv_lorentz_integral hc]; ring
  have hsplit : (fun r : ℝ => 2 * c / (c ^ 2 + r ^ 2) * sourceS L r n) =
      fun r => 2 / c * (sourceS L r n - r ^ 2 * sourceS L r n * (c ^ 2 + r ^ 2)⁻¹) := by
    funext r
    have := (hden r).ne'
    field_simp
    ring
  have hV := lorentz_source_value hc hL n
  rw [hsplit, integral_const_mul, integral_sub hSint hTint, hω] at hV
  set I := ∫ r : ℝ, sourceS L r n
  set J := ∫ r : ℝ, r ^ 2 * sourceS L r n * (c ^ 2 + r ^ 2)⁻¹
  have hIJ : I = J + -(π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)) := by
    have h2 : I - J = c / 2 * (2 / c * (I - J)) := by field_simp
    rw [hV] at h2
    have : c ^ 2 + ω ^ 2 ≠ 0 := (by positivity : (0 : ℝ) < c ^ 2 + ω ^ 2).ne'
    linear_combination h2 + (by field_simp :
      c / 2 * (-(2 * π) * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)) =
        -(π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)))
  have he0 : 0 ≤ 1 - Real.exp (-c * L) := by
    have : Real.exp (-c * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have he1 : 1 - Real.exp (-c * L) ≤ 1 := by linarith [Real.exp_pos (-c * L)]
  have hVb : |π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)| ≤ π * |ω| / c := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos pi_pos, abs_of_pos hc, abs_of_nonneg he0,
      abs_of_pos (by positivity : (0 : ℝ) < c ^ 2 + ω ^ 2)]
    calc π * c * |ω| * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)
        ≤ π * c * |ω| * 1 / (c ^ 2 + ω ^ 2) := by gcongr
      _ ≤ π * c * |ω| * 1 / c ^ 2 := by gcongr; nlinarith [sq_nonneg ω]
      _ = π * |ω| / c := by field_simp
  rw [hIJ]
  calc |J + -(π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2))|
      ≤ |J| + |π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2)| := by
        rw [← abs_neg (π * c * ω * (1 - Real.exp (-c * L)) / (c ^ 2 + ω ^ 2))]
        exact abs_add_le _ _
    _ ≤ (ω ^ 2 * L + 2 * |ω|) * π / c + π * |ω| / c := add_le_add hJ hVb
    _ = (π * |ω| + (ω ^ 2 * L + 2 * |ω|) * π) / c := by ring

/-! ### The digamma series terms -/

/-- `c_k = 2k + 1/2`, the Lorentzian widths of `h₊`. -/
def archWidth (k : ℕ) : ℝ := 2 * k + 1 / 2

/-- `a_k(r) = 1/(k+1) − 2c_k/(c_k² + r²)`, the real part of the `k`-th digamma series term
at `1/4 + ir/2`. -/
def archTerm (k : ℕ) (r : ℝ) : ℝ := 1 / ((k : ℝ) + 1) - 2 * archWidth k / (archWidth k ^ 2 + r ^ 2)

theorem archWidth_pos (k : ℕ) : 0 < archWidth k := by unfold archWidth; positivity

theorem archWidth_sq_ge (k : ℕ) : ((k : ℝ) + 1) ^ 2 ≤ 4 * archWidth k ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold archWidth; nlinarith

theorem archShift_abs_le (k : ℕ) :
    |1 / ((k : ℝ) + 1) - 2 / archWidth k| ≤ 3 / ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (k : ℝ) + 1 / 2 ≠ 0 := by positivity
  have h3 : 4 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h : 1 / ((k : ℝ) + 1) - 2 / archWidth k = -(3 / ((4 * k + 1) * ((k : ℝ) + 1))) := by
    unfold archWidth; field_simp; ring
  rw [h, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hk hk]

/-- `a_k(r) = (1/(k+1) − 2/c_k) + (2/c_k) r²/(c_k² + r²)`. -/
theorem archTerm_split (k : ℕ) (r : ℝ) :
    archTerm k r = (1 / ((k : ℝ) + 1) - 2 / archWidth k) +
      2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹) := by
  have hc := archWidth_pos k
  have : archWidth k ^ 2 + r ^ 2 ≠ 0 := by positivity
  unfold archTerm
  field_simp
  ring

theorem archTerm_continuous (k : ℕ) : Continuous (archTerm k) := by
  have hc := archWidth_pos k
  unfold archTerm
  exact continuous_const.sub (continuous_const.div (by fun_prop) fun r => by positivity)

theorem archTerm_abs_le (k : ℕ) (r : ℝ) :
    |archTerm k r| ≤ (3 + 16 * r ^ 2) / ((k : ℝ) + 1) ^ 2 := by
  have hc := archWidth_pos k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcge : ((k : ℝ) + 1) / 2 ≤ archWidth k := by unfold archWidth; linarith
  have hhalf : 1 / 2 ≤ archWidth k := by unfold archWidth; linarith
  rw [archTerm_split]
  have hfrac : r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹ ≤ r ^ 2 / archWidth k ^ 2 := by
    rw [← div_eq_mul_inv]
    gcongr
    nlinarith [sq_nonneg r]
  have hpos : 0 ≤ 2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹) := by positivity
  have hcube : ((k : ℝ) + 1) ^ 2 ≤ 8 * archWidth k ^ 3 := by nlinarith [archWidth_sq_ge k]
  calc |1 / ((k : ℝ) + 1) - 2 / archWidth k + 2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹)|
      ≤ |1 / ((k : ℝ) + 1) - 2 / archWidth k| +
          |2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹)| := abs_add_le _ _
    _ ≤ 3 / ((k : ℝ) + 1) ^ 2 + 2 / archWidth k * (r ^ 2 / archWidth k ^ 2) := by
        rw [abs_of_nonneg hpos]
        gcongr
        · exact archShift_abs_le k
    _ = 3 / ((k : ℝ) + 1) ^ 2 + 2 * r ^ 2 / archWidth k ^ 3 := by field_simp
    _ ≤ 3 / ((k : ℝ) + 1) ^ 2 + 16 * r ^ 2 / ((k : ℝ) + 1) ^ 2 := by
        refine add_le_add le_rfl ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hcube (sq_nonneg r)]
    _ = (3 + 16 * r ^ 2) / ((k : ℝ) + 1) ^ 2 := by ring

theorem summable_inv_succ_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using h

theorem archTerm_summable (r : ℝ) : Summable fun k => archTerm k r := by
  refine Summable.of_norm_bounded ((summable_inv_succ_sq).mul_left (3 + 16 * r ^ 2)) fun k => ?_
  rw [Real.norm_eq_abs]
  refine (archTerm_abs_le k r).trans_eq ?_
  ring

theorem archTerm_source_integrable {L : ℝ} (hL : 0 < L) (n : ℤ) (k : ℕ) :
    Integrable fun r => archTerm k r * sourceS L r n := by
  have hc := archWidth_pos k
  refine (sourceS_integrable hL n).bdd_mul (c := 1 / ((k : ℝ) + 1) + 2 / archWidth k)
    (archTerm_continuous k).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs]
  unfold archTerm
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  refine add_le_add le_rfl ?_
  rw [div_le_div_iff₀ (by positivity) hc]
  nlinarith [sq_nonneg r]

/-- **One term**: `∫ a_k(r) S(r) dr = 2πω(1 − e^{−c_k L})/(c_k² + ω²)`. -/
theorem archTerm_source_integral {L : ℝ} (hL : 0 < L) (n : ℤ) (k : ℕ) :
    ∫ r, archTerm k r * sourceS L r n =
      2 * π * (2 * π * n / L) * (1 - Real.exp (-archWidth k * L)) /
        (archWidth k ^ 2 + (2 * π * n / L) ^ 2) := by
  have hc := archWidth_pos k
  have hlor : Integrable fun r => 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) * sourceS L r n := by
    have := (archTerm_source_integrable hL n k).sub ((sourceS_integrable hL n).const_mul
      (1 / ((k : ℝ) + 1)))
    refine (this.neg).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [archTerm, Pi.neg_apply, Pi.sub_apply]
    ring
  simp only [archTerm, sub_mul]
  rw [integral_sub ((sourceS_integrable hL n).const_mul _) hlor, integral_const_mul,
    sourceS_integral_eq_zero hL n, lorentz_source_value hc hL n]
  ring

/-- The integrable majorant of `|a_k S|`. -/
theorem archTerm_source_norm_integral_le {L : ℝ} (hL : 0 < L) (n : ℤ) (k : ℕ) :
    ∫ r, ‖archTerm k r * sourceS L r n‖ ≤
      (3 * (∫ r, |sourceS L r n|) + 8 * π * ((2 * π * n / L) ^ 2 * L + 2 * |2 * π * n / L|)) /
        ((k : ℝ) + 1) ^ 2 := by
  have hc := archWidth_pos k
  set B := (2 * π * n / L) ^ 2 * L + 2 * |2 * π * n / L| with hBdef
  have hB0 : 0 ≤ B := by positivity
  set d := 1 / ((k : ℝ) + 1) - 2 / archWidth k
  have hSabs : Integrable fun r => |sourceS L r n| := (sourceS_integrable hL n).abs
  have hG : Integrable fun r => |d| * |sourceS L r n| +
      2 / archWidth k * B * (archWidth k ^ 2 + r ^ 2)⁻¹ :=
    (hSabs.const_mul _).add ((inv_lorentz_integrable hc).const_mul _)
  have hpt : ∀ r, ‖archTerm k r * sourceS L r n‖ ≤
      |d| * |sourceS L r n| + 2 / archWidth k * B * (archWidth k ^ 2 + r ^ 2)⁻¹ := by
    intro r
    have hden : 0 < archWidth k ^ 2 + r ^ 2 := by positivity
    rw [Real.norm_eq_abs, archTerm_split, add_mul]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
    rw [show 2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹) * sourceS L r n =
        2 / archWidth k * (r ^ 2 * sourceS L r n) * (archWidth k ^ 2 + r ^ 2)⁻¹ by ring,
      abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 / archWidth k),
      abs_of_pos (inv_pos.mpr hden)]
    gcongr
    exact sq_mul_sourceS_abs_le hL n r
  refine (integral_mono ((archTerm_source_integrable hL n k).norm) hG hpt).trans ?_
  rw [integral_add (hSabs.const_mul _) ((inv_lorentz_integrable hc).const_mul _),
    integral_const_mul, integral_const_mul, inv_lorentz_integral hc]
  have hM : 0 ≤ ∫ r, |sourceS L r n| := integral_nonneg fun r => abs_nonneg _
  have hd := archShift_abs_le k
  have hsq := archWidth_sq_ge k
  have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have h2 : 2 / archWidth k * B * (π / archWidth k) ≤ 8 * π * B / ((k : ℝ) + 1) ^ 2 := by
    rw [show 2 / archWidth k * B * (π / archWidth k) = 2 * π * B / archWidth k ^ 2 by ring,
      div_le_div_iff₀ (by positivity) hk1]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * π * B)]
  calc |d| * (∫ r, |sourceS L r n|) + 2 / archWidth k * B * (π / archWidth k)
      ≤ 3 / ((k : ℝ) + 1) ^ 2 * (∫ r, |sourceS L r n|) + 8 * π * B / ((k : ℝ) + 1) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hd hM) h2
    _ = _ := by ring

theorem archTerm_source_summable {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Summable fun k => ∫ r, ‖archTerm k r * sourceS L r n‖ := by
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun r => norm_nonneg _)
    (fun k => archTerm_source_norm_integral_le hL n k) ?_
  refine (summable_inv_succ_sq.mul_left
    (3 * (∫ r, |sourceS L r n|) + 8 * π * ((2 * π * n / L) ^ 2 * L + 2 * |2 * π * n / L|))).congr
    fun k => ?_
  ring

/-- **Archimedean source value.** For every constant `C`,
`∫ (∑' k, a_k(r) − C) S(r) dr = ∑' k, 2πω(1 − e^{−c_k L})/(c_k² + ω²)`, `ω = 2πn/L`. -/
theorem arch_series_source {L : ℝ} (hL : 0 < L) (n : ℤ) (C : ℝ) :
    ∫ r, ((∑' k, archTerm k r) - C) * sourceS L r n =
      ∑' k, 2 * π * (2 * π * n / L) * (1 - Real.exp (-archWidth k * L)) /
        (archWidth k ^ 2 + (2 * π * n / L) ^ 2) := by
  have hSint := sourceS_integrable hL n
  set b : ℕ → ℝ := fun k => if k = 0 then C else 0 with hb
  set F : ℕ → ℝ → ℝ := fun k r => (archTerm k r - b k) * sourceS L r n with hF
  have hFint : ∀ k, Integrable (F k) := fun k =>
    ((archTerm_source_integrable hL n k).sub (hSint.const_mul (b k))).congr
      (Filter.Eventually.of_forall fun r => by simp only [hF, Pi.sub_apply]; ring)
  have hFval : ∀ k, ∫ r, F k r = ∫ r, archTerm k r * sourceS L r n := fun k => by
    have : F k = fun r => archTerm k r * sourceS L r n - b k * sourceS L r n := by
      funext r; simp only [hF]; ring
    rw [this, integral_sub (archTerm_source_integrable hL n k) (hSint.const_mul (b k)),
      integral_const_mul, sourceS_integral_eq_zero hL n, mul_zero, sub_zero]
  have hbsum : Summable fun k => |b k| * ∫ r, |sourceS L r n| := by
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    have : k ≠ 0 := by simpa using hk
    simp [hb, this]
  have hFsum : Summable fun k => ∫ r, ‖F k r‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun r => norm_nonneg _)
      (fun k => ?_) ((archTerm_source_summable hL n).add hbsum)
    have hpt : ∀ r, ‖F k r‖ ≤ ‖archTerm k r * sourceS L r n‖ + |b k| * |sourceS L r n| := by
      intro r
      simp only [hF, Real.norm_eq_abs, sub_mul]
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_mul (b k)]
    have hG : Integrable fun r => ‖archTerm k r * sourceS L r n‖ + |b k| * |sourceS L r n| :=
      (archTerm_source_integrable hL n k).norm.add (hSint.abs.const_mul _)
    refine (integral_mono (hFint k).norm hG hpt).trans_eq ?_
    rw [integral_add (archTerm_source_integrable hL n k).norm (hSint.abs.const_mul _),
      integral_const_mul]
  have hpt : ∀ r, ∑' k, F k r = ((∑' k, archTerm k r) - C) * sourceS L r n := by
    intro r
    simp only [hF]
    rw [tsum_mul_right, ((archTerm_summable r).tsum_sub (hasSum_ite_eq 0 C).summable),
      tsum_ite_eq]
  rw [← funext hpt, ← integral_tsum_of_summable_integral_norm hFint hFsum]
  exact tsum_congr fun k => by rw [hFval k, archTerm_source_integral hL n k]

end AEGIS.CvSArchSourceV1

#print axioms AEGIS.CvSArchSourceV1.source_identity
#print axioms AEGIS.CvSArchSourceV1.sourceS_abs_le
#print axioms AEGIS.CvSArchSourceV1.sq_mul_sourceS_abs_le
#print axioms AEGIS.CvSArchSourceV1.sourceS_continuous
#print axioms AEGIS.CvSArchSourceV1.sourceS_bound
#print axioms AEGIS.CvSArchSourceV1.sourceS_integrable
#print axioms AEGIS.CvSArchSourceV1.lorentz_total
#print axioms AEGIS.CvSArchSourceV1.inv_lorentz_integral
#print axioms AEGIS.CvSArchSourceV1.eq_zero_of_abs_le_div
#print axioms AEGIS.CvSArchSourceV1.sourceS_integral_eq_zero
#print axioms AEGIS.CvSArchSourceV1.archTerm_split
#print axioms AEGIS.CvSArchSourceV1.archTerm_abs_le
#print axioms AEGIS.CvSArchSourceV1.archTerm_summable
#print axioms AEGIS.CvSArchSourceV1.archTerm_source_integrable
#print axioms AEGIS.CvSArchSourceV1.archTerm_source_integral
#print axioms AEGIS.CvSArchSourceV1.archTerm_source_norm_integral_le
#print axioms AEGIS.CvSArchSourceV1.archTerm_source_summable
#print axioms AEGIS.CvSArchSourceV1.arch_series_source
