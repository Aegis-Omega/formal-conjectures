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
import Mathlib

/-!
# The arctan tail of `Σ 2ω/(c_j² + ω²)` (CvS step 7b)

`Complex.hasSum_arctan` gives the real arctan series and its alternating partial-sum bounds
(`arctan_le_partial`, `partial_le_arctan`). With `c_j = c₀ + 2j`, the steps
`arctan(ω/(c−1)) − arctan(ω/(c+1)) = arctan(2ω/(c²−1+ω²))` (`arctan_step`) telescope, and each
step is within `2ω/c⁴` of `2ω/(c²+ω²)` (`term_le_step`, `step_le_term`), so

  `arctan(ω/(c₀−1)) − (ω/3)(c₀−1)⁻³ ≤ Σ' j, 2ω/(c_j²+ω²) ≤ arctan(ω/(c₀−1))`   (`tail_bracket`)

when `ω ≥ 1`, `c₀ > 2` and `c₀² ≥ ω²/3 + 3`. Not RH.
-/

open Finset Filter Topology

namespace AEGIS.CvSArctanTailV1

/-- `x^(2n+1)/(2n+1)`, the `n`-th arctan coefficient. -/
noncomputable def atTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * n + 1)

theorem arctan_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * atTerm x n) (Real.arctan x) := by
  have h := Complex.hasSum_arctan (z := (x : ℂ)) (by simpa [Complex.norm_real] using hx)
  rw [← Complex.ofReal_arctan] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext n
  simp only [atTerm]
  push_cast
  ring

theorem atTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Antitone (atTerm x) := by
  refine antitone_nat_of_succ_le fun n => ?_
  simp only [atTerm]
  have h1 : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have h2 : (0 : ℝ) < 2 * n + 1 := by positivity
  push_cast
  rw [div_le_div_iff₀ (by positivity) h2]
  have h3 : 0 ≤ x ^ (2 * (n + 1) + 1) := by positivity
  nlinarith

theorem arctan_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Real.arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * atTerm x i :=
  (atTerm_antitone hx0 hx1.le).tendsto_le_alternating_series
    (arctan_hasSum (abs_lt.mpr ⟨by linarith, hx1⟩)).tendsto_sum_nat k

theorem partial_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * atTerm x i ≤ Real.arctan x :=
  (atTerm_antitone hx0 hx1.le).alternating_series_le_tendsto
    (arctan_hasSum (abs_lt.mpr ⟨by linarith, hx1⟩)).tendsto_sum_nat k

theorem arctan_le_self' {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) : Real.arctan v ≤ v := by
  simpa [atTerm] using arctan_le_partial h0 h1 0

theorem sub_cube_le_arctan {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) : v - v ^ 3 / 3 ≤ Real.arctan v := by
  have := partial_le_arctan h0 h1 1
  simp only [atTerm, show 2 * 1 = 2 by rfl, sum_range_succ, sum_range_zero] at this
  norm_num at this
  linarith

/-- `arctan a − arctan b = arctan ((a − b)/(1 + ab))` for `a, b ≥ 0`. -/
theorem arctan_sub_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.arctan a - Real.arctan b = Real.arctan ((a - b) / (1 + a * b)) := by
  have h : a * -b < 1 := by nlinarith [mul_nonneg ha hb]
  rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add h]
  congr 1
  ring_nf

/-- The telescoping step: `arctan(ω/(c−1)) − arctan(ω/(c+1)) = arctan(2ω/(c²−1+ω²))`. -/
theorem arctan_step {ω c : ℝ} (hω : 0 ≤ ω) (hc : 1 < c) :
    Real.arctan (ω / (c - 1)) - Real.arctan (ω / (c + 1)) =
      Real.arctan (2 * ω / (c ^ 2 - 1 + ω ^ 2)) := by
  have h1 : 0 < c - 1 := by linarith
  have h2 : 0 < c + 1 := by linarith
  rw [arctan_sub_eq (div_nonneg hω h1.le) (div_nonneg hω h2.le)]
  congr 1
  have h3 : 0 < c ^ 2 - 1 + ω ^ 2 := by nlinarith
  field_simp
  ring

/-- A telescoping series of an antitone sequence tending to `0`. -/
theorem hasSum_telescope {f : ℕ → ℝ} (hf : Antitone f) (h0 : Tendsto f atTop (𝓝 0)) :
    HasSum (fun n => f n - f (n + 1)) (f 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr (hf (Nat.le_succ n)))]
  simp_rw [Finset.sum_range_sub']
  simpa using (tendsto_const_nhds (x := f 0)).sub h0

/-- The upper comparison `2ω/(c²+ω²) ≤ arctan(2ω/(c²−1+ω²))` once `c² ≥ ω²/3 + 3`. -/
theorem term_le_step {ω c : ℝ} (hω : 0 ≤ ω) (hc : ω ^ 2 / 3 + 3 ≤ c ^ 2) :
    2 * ω / (c ^ 2 + ω ^ 2) ≤ Real.arctan (2 * ω / (c ^ 2 - 1 + ω ^ 2)) := by
  set E := c ^ 2 - 1 + ω ^ 2 with hE
  set D := c ^ 2 + ω ^ 2 with hD
  have hE0 : 0 < E := by nlinarith
  have hD0 : 0 < D := by nlinarith
  have hv0 : 0 ≤ 2 * ω / E := div_nonneg (by linarith) hE0.le
  have hv1 : 2 * ω / E < 1 := by
    rw [div_lt_one hE0]; nlinarith [sq_nonneg (ω - 1)]
  refine le_trans ?_ (sub_cube_le_arctan hv0 hv1)
  have hdiff : 2 * ω / E - 2 * ω / D = 2 * ω / (E * D) := by
    rw [div_sub_div _ _ hE0.ne' hD0.ne']
    congr 1
    rw [hD, hE]; ring
  have key : (2 * ω / E) ^ 3 / 3 ≤ 2 * ω / (E * D) := by
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hX : ω ^ 2 / 3 + 2 ≤ c ^ 2 - 1 := by linarith
    have hpoly : 4 * ω ^ 2 * D ≤ 3 * E ^ 2 := by
      rw [hD, hE]; nlinarith [sq_nonneg ω, mul_nonneg (sq_nonneg ω) (sq_nonneg ω)]
    have hω3 : 0 ≤ 2 * ω := by linarith
    calc (2 * ω) ^ 3 * (E * D) = (2 * ω) * E * (4 * ω ^ 2 * D) := by ring
      _ ≤ (2 * ω) * E * (3 * E ^ 2) := by
          apply mul_le_mul_of_nonneg_left hpoly; positivity
      _ = 2 * ω * (E ^ 3 * 3) := by ring
  linarith

/-- The lower comparison `arctan(2ω/(c²−1+ω²)) ≤ 2ω/(c²+ω²) + 2ω/c⁴` for `ω ≥ 1`, `c² > 2`. -/
theorem step_le_term {ω c : ℝ} (hω : 1 ≤ ω) (hc : 2 < c ^ 2) :
    Real.arctan (2 * ω / (c ^ 2 - 1 + ω ^ 2)) ≤ 2 * ω / (c ^ 2 + ω ^ 2) + 2 * ω / c ^ 4 := by
  set E := c ^ 2 - 1 + ω ^ 2 with hE
  set D := c ^ 2 + ω ^ 2 with hD
  have hE0 : 0 < E := by nlinarith
  have hc0 : 0 < c ^ 2 := by linarith
  have hv0 : 0 ≤ 2 * ω / E := div_nonneg (by linarith) hE0.le
  have hv1 : 2 * ω / E < 1 := by
    rw [div_lt_one hE0]; nlinarith [sq_nonneg (ω - 1)]
  refine le_trans (arctan_le_self' hv0 hv1) ?_
  have hD0 : 0 < D := by nlinarith
  have hdiff : 2 * ω / E = 2 * ω / D + 2 * ω / (E * D) := by
    have hDE : D = E + 1 := by rw [hD, hE]; ring
    rw [hDE] at hD0 ⊢
    rw [div_add_div _ _ hD0.ne' (mul_pos hE0 hD0).ne', eq_comm,
      div_eq_div_iff (mul_pos hD0 (mul_pos hE0 hD0)).ne' hE0.ne']
    ring
  rw [hdiff]
  gcongr
  · nlinarith
  · calc c ^ 4 = c ^ 2 * c ^ 2 := by ring
      _ ≤ E * D := by
          apply mul_le_mul <;> nlinarith

/-- `1/c⁴ ≤ ((c−1)⁻³ − (c+1)⁻³)/6` for `c > 1`. -/
theorem inv_four_le {c : ℝ} (hc : 1 < c) :
    1 / c ^ 4 ≤ (1 / (c - 1) ^ 3 - 1 / (c + 1) ^ 3) / 6 := by
  have h1 : 0 < c - 1 := by linarith
  have h2 : 0 < c + 1 := by linarith
  have h0 : 0 < c := by linarith
  have h3 : 0 < c ^ 2 - 1 := by nlinarith
  have e : 1 / (c - 1) ^ 3 - 1 / (c + 1) ^ 3 = (6 * c ^ 2 + 2) / ((c ^ 2 - 1) ^ 3) := by
    rw [div_sub_div _ _ (pow_pos h1 3).ne' (pow_pos h2 3).ne', div_eq_div_iff
      (mul_pos (pow_pos h1 3) (pow_pos h2 3)).ne' (pow_pos h3 3).ne']
    ring
  rw [e, div_div, div_le_div_iff₀ (by positivity) (mul_pos (pow_pos h3 3) (by norm_num))]
  have h4 : (c ^ 2 - 1) ^ 3 ≤ c ^ 6 := by
    have : c ^ 2 - 1 ≤ c ^ 2 := by linarith
    calc (c ^ 2 - 1) ^ 3 ≤ (c ^ 2) ^ 3 := by gcongr
      _ = c ^ 6 := by ring
  nlinarith [pow_pos h0 6, pow_pos h0 4]

/-- **The tail bracket.** With `c_j = c₀ + 2j`, `ω ≥ 1`, `c₀ > 2` and `c₀² ≥ ω²/3 + 3`,
`arctan(ω/(c₀−1)) − (ω/3)(c₀−1)⁻³ ≤ Σ' j, 2ω/(c_j²+ω²) ≤ arctan(ω/(c₀−1))`. -/
theorem tail_bracket {ω c₀ : ℝ} (hω : 1 ≤ ω) (hc1 : 2 < c₀) (hc : ω ^ 2 / 3 + 3 ≤ c₀ ^ 2) :
    Summable (fun j : ℕ => 2 * ω / ((c₀ + 2 * j) ^ 2 + ω ^ 2)) ∧
    Real.arctan (ω / (c₀ - 1)) - ω / 3 * (1 / (c₀ - 1) ^ 3) ≤
      ∑' j : ℕ, 2 * ω / ((c₀ + 2 * j) ^ 2 + ω ^ 2) ∧
    ∑' j : ℕ, 2 * ω / ((c₀ + 2 * j) ^ 2 + ω ^ 2) ≤ Real.arctan (ω / (c₀ - 1)) := by
  set c : ℕ → ℝ := fun j => c₀ + 2 * j with hcdef
  have hcj : ∀ j, c₀ ≤ c j := fun j => by
    simp only [hcdef]; exact le_add_of_nonneg_right (by positivity)
  have hcs : ∀ j, c (j + 1) = c j + 2 := fun j => by simp only [hcdef]; push_cast; ring
  set T : ℕ → ℝ := fun j => Real.arctan (ω / (c j - 1)) with hT
  have hTanti : Antitone T := by
    refine antitone_nat_of_succ_le fun j => ?_
    apply Real.arctan_mono
    rw [hcs]
    have := hcj j
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have hT0 : Tendsto T atTop (𝓝 0) := by
    have hlin : Tendsto (fun j : ℕ => c j - 1) atTop atTop := by
      simp only [hcdef]
      apply tendsto_atTop_add_const_right
      apply tendsto_atTop_add_const_left
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    have := (tendsto_const_nhds (x := ω)).div_atTop hlin
    simpa [hT] using (Real.continuous_arctan.tendsto 0).comp this |>.congr' (by
      filter_upwards with j; simp)
  have hA := hasSum_telescope hTanti hT0
  have hstep : ∀ j, T j - T (j + 1) = Real.arctan (2 * ω / (c j ^ 2 - 1 + ω ^ 2)) := by
    intro j
    simp only [hT]
    rw [hcs, show c j + 2 - 1 = c j + 1 by ring]
    exact arctan_step (by linarith) (by linarith [hcj j])
  have hcsq : ∀ j, ω ^ 2 / 3 + 3 ≤ c j ^ 2 := fun j => by
    have := hcj j; nlinarith
  have hup : ∀ j, 2 * ω / (c j ^ 2 + ω ^ 2) ≤ T j - T (j + 1) := fun j => by
    rw [hstep]; exact term_le_step (by linarith) (hcsq j)
  have hnn : ∀ j, 0 ≤ 2 * ω / (c j ^ 2 + ω ^ 2) := fun j => by positivity
  have hsum : Summable (fun j => 2 * ω / (c j ^ 2 + ω ^ 2)) :=
    Summable.of_nonneg_of_le hnn hup hA.summable
  -- the correction series
  set B : ℕ → ℝ := fun j => 1 / (c j - 1) ^ 3 with hB
  have hBanti : Antitone B := by
    refine antitone_nat_of_succ_le fun j => ?_
    simp only [hB]
    rw [hcs]
    have := hcj j
    exact one_div_le_one_div_of_le (pow_pos (by linarith) 3)
      (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  have hB0 : Tendsto B atTop (𝓝 0) := by
    have hlin : Tendsto (fun j : ℕ => (c j - 1) ^ 3) atTop atTop := by
      simp only [hcdef]
      refine (tendsto_pow_atTop (by norm_num)).comp ?_
      apply tendsto_atTop_add_const_right
      apply tendsto_atTop_add_const_left
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    refine hlin.inv_tendsto_atTop.congr fun j => ?_
    simp [hB]
  have hBs := (hasSum_telescope hBanti hB0).mul_left (ω / 3)
  have hlow : ∀ j, T j - T (j + 1) - ω / 3 * (B j - B (j + 1)) ≤
      2 * ω / (c j ^ 2 + ω ^ 2) := fun j => by
    have h1 := step_le_term hω (by nlinarith [hcj j] : (2 : ℝ) < c j ^ 2)
    have h2 := inv_four_le (by linarith [hcj j] : (1 : ℝ) < c j)
    rw [hstep]
    have h3 : 2 * ω / c j ^ 4 ≤ ω / 3 * (B j - B (j + 1)) := by
      simp only [hB]; rw [hcs, show c j + 2 - 1 = c j + 1 by ring]
      calc 2 * ω / c j ^ 4 = 2 * ω * (1 / c j ^ 4) := by ring
        _ ≤ 2 * ω * ((1 / (c j - 1) ^ 3 - 1 / (c j + 1) ^ 3) / 6) := by
            apply mul_le_mul_of_nonneg_left h2; linarith
        _ = _ := by ring
    linarith
  have hc00 : c 0 = c₀ := by simp [hcdef]
  have hT00 : T 0 = Real.arctan (ω / (c₀ - 1)) := by simp only [hT, hc00]
  have hB00 : B 0 = 1 / (c₀ - 1) ^ 3 := by simp only [hB, hc00]
  refine ⟨hsum, ?_, ?_⟩
  · have := hasSum_le hlow (hA.sub hBs) hsum.hasSum
    rw [hT00, hB00] at this
    exact this
  · have := hasSum_le hup hsum.hasSum hA
    rw [hT00] at this
    exact this

end AEGIS.CvSArctanTailV1

#print axioms AEGIS.CvSArctanTailV1.arctan_hasSum
#print axioms AEGIS.CvSArctanTailV1.arctan_le_partial
#print axioms AEGIS.CvSArctanTailV1.partial_le_arctan
#print axioms AEGIS.CvSArctanTailV1.arctan_step
#print axioms AEGIS.CvSArctanTailV1.tail_bracket
