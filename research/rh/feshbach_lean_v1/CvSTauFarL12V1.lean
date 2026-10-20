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

import CvSTauPrimeL12V1

/-!
# A sharp bound for `τ_n` far from the low block at L = 6/5

`CvSRowTailV1.tau_abs_le` gives `|τ_n| ≤ 4π(1 + π/4) + π Σ_{j<M} |ppw j|`, which grows with the
prime cutoff and is about 29.5 at `M = 3`. Here the width sum is bounded by `1/ω + π/4`
instead of `1 + π/4`, so `|∫ h₊ S_n| ≤ L/|n| + π²/2`, and at `L = 6/5` only `p = 2, 3`
contribute to the prime part (`CvSTauPrimeL12V1.primeSum_eq`). For `|n| ≥ 71` and every
`M ≥ 3` this gives `|τ_n| ≤ 13`. Not RH.
-/

open Finset
open AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
open AEGIS.CvSTauPrimeL12V1 AEGIS.RHKreinZetaBridgeV3

namespace AEGIS.CvSTauFarL12V1

/-- The width sum is at most `1/ω + π/4`. -/
theorem sum_width_le_inv {ω : ℝ} (hω : 0 < ω) (K : ℕ) :
    ∑ k ∈ range K, ω / (archWidth k ^ 2 + ω ^ 2) ≤ 1 / ω + Real.pi / 4 := by
  have h0 : ω / (archWidth 0 ^ 2 + ω ^ 2) ≤ 1 / ω := by
    rw [div_le_div_iff₀ (by have := archWidth_pos 0; positivity) hω]
    nlinarith [sq_nonneg (archWidth 0)]
  have hstep : ∀ k : ℕ, ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤
      (Real.arctan (2 * ((k : ℝ) + 1) / ω) - Real.arctan (2 * k / ω)) / 2 := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have ha := arctan_sub_ge (a := 2 * ((k : ℝ) + 1) / ω) (b := 2 * k / ω) (by positivity)
      (by gcongr; linarith)
    have e : (2 * ((k : ℝ) + 1) / ω - 2 * k / ω) / (1 + (2 * ((k : ℝ) + 1) / ω) ^ 2) =
        2 * ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    rw [e] at ha
    have hc : archWidth (k + 1) ^ 2 + ω ^ 2 ≥ ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2 := by
      unfold archWidth
      push_cast
      nlinarith
    calc ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤ ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_left hω.le (by positivity) hc
      _ = (2 * ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2)) / 2 := by ring
      _ ≤ _ := by linarith
  rcases K with _ | K
  · simp only [range_zero, sum_empty]
    positivity
  rw [sum_range_succ']
  have htel : ∑ k ∈ range K, ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤
      (Real.arctan (2 * (K : ℝ) / ω) - Real.arctan (2 * ((0 : ℕ) : ℝ) / ω)) / 2 := by
    calc ∑ k ∈ range K, ω / (archWidth (k + 1) ^ 2 + ω ^ 2)
        ≤ ∑ k ∈ range K, (Real.arctan (2 * ((k : ℝ) + 1) / ω) - Real.arctan (2 * k / ω)) / 2 :=
          sum_le_sum fun k _ => hstep k
      _ = (Real.arctan (2 * (K : ℝ) / ω) - Real.arctan (2 * ((0 : ℕ) : ℝ) / ω)) / 2 := by
          rw [← sum_div]
          have := sum_range_sub (fun k : ℕ => Real.arctan (2 * (k : ℝ) / ω)) K
          simp only [Nat.cast_add, Nat.cast_one] at this
          rw [this]
  have hpi := Real.arctan_lt_pi_div_two (2 * (K : ℝ) / ω)
  simp only [Nat.cast_zero, mul_zero, zero_div, Real.arctan_zero, sub_zero] at htel
  linarith

theorem tsum_abs_width_le_inv {ω : ℝ} (hω : ω ≠ 0) :
    ∑' k, |ω| / (archWidth k ^ 2 + ω ^ 2) ≤ 1 / |ω| + Real.pi / 4 := by
  refine Real.tsum_le_of_sum_range_le (fun k => by have := archWidth_pos k; positivity)
    fun K => ?_
  have e : ∀ k, |ω| / (archWidth k ^ 2 + ω ^ 2) = |ω| / (archWidth k ^ 2 + |ω| ^ 2) := fun k => by
    rw [sq_abs]
  simp_rw [e]
  exact sum_width_le_inv (abs_pos.mpr hω) K

/-- **The archimedean source integral is at most `L/|n| + π²/2`.** -/
theorem source_integral_abs_le_inv {L : ℝ} (hL : 0 < L) {n : ℤ} (hn : n ≠ 0) :
    |∫ r, hplus r * sourceS L r n| ≤ L / |(n : ℝ)| + Real.pi ^ 2 / 2 := by
  rw [hplus_source_integral hL n]
  set ω := 2 * Real.pi * n / L with hω
  have hhalf : Real.pi * n / L = ω / 2 := by rw [hω]; ring
  rw [hhalf, half_im_digamma]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hω0 : ω ≠ 0 := by
    rw [hω]; exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn') hL.ne'
  have habs : |ω| = 2 * Real.pi * |(n : ℝ)| / L := by
    rw [hω, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, abs_of_pos hL]
  clear_value ω
  have hs1 : Summable fun k => ω / (archWidth k ^ 2 + ω ^ 2) :=
    ((summable_inv_width ω).mul_left ω).congr fun k => by ring
  have hs2 : Summable fun k => Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by have := archWidth_pos k; positivity)
      (fun k => ?_) (summable_inv_width ω)
    have hc := archWidth_pos k
    gcongr
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hcomb : ∑' k, ω / (archWidth k ^ 2 + ω ^ 2) -
      ω * ∑' k, Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2) =
      ∑' k, ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2) := by
    rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left ω)]
    exact tsum_congr fun k => by ring
  have hb : ∀ k, |ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2)| ≤
      |ω| / (archWidth k ^ 2 + ω ^ 2) := fun k => by
    have hc := archWidth_pos k
    have he1 : Real.exp (-archWidth k * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 < Real.exp (-archWidth k * L) := Real.exp_pos _
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-archWidth k * L)),
      abs_of_pos (show (0 : ℝ) < archWidth k ^ 2 + ω ^ 2 by positivity)]
    gcongr
    calc |ω| * (1 - Real.exp (-archWidth k * L)) ≤ |ω| * 1 := by
          gcongr; linarith
      _ = |ω| := mul_one _
  have hsa : Summable fun k => |ω| / (archWidth k ^ 2 + ω ^ 2) :=
    ((summable_inv_width ω).mul_left |ω|).congr fun k => by ring
  have hsn : Summable fun k => ‖ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2)‖ :=
    hsa.of_nonneg_of_le (fun k => norm_nonneg _) fun k => by rw [Real.norm_eq_abs]; exact hb k
  have hsum : |∑' k, ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2)| ≤
      1 / |ω| + Real.pi / 4 := by
    rw [← Real.norm_eq_abs]
    calc _ ≤ ∑' k, ‖ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2)‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, |ω| / (archWidth k ^ 2 + ω ^ 2) :=
          hsn.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hb k) hsa
      _ ≤ _ := tsum_abs_width_le_inv hω0
  rw [hcomb, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hnpos : 0 < |(n : ℝ)| := abs_pos.mpr hn'
  calc 2 * Real.pi * |∑' k, ω * (1 - Real.exp (-archWidth k * L)) / (archWidth k ^ 2 + ω ^ 2)|
      ≤ 2 * Real.pi * (1 / |ω| + Real.pi / 4) := by gcongr
    _ = L / |(n : ℝ)| + Real.pi ^ 2 / 2 := by
        rw [habs]
        field_simp
        ring

/-- **`|τ_n| ≤ 13` for `|n| ≥ 71` at L = 6/5**, for every prime cutoff `M ≥ 3`. -/
theorem tau_abs_le_far {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn : 71 ≤ |n|) :
    |tau M (6 / 5) n| ≤ 13 := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hnR : (71 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
  have hsrc := source_integral_abs_le_inv (L := 6 / 5) (by norm_num) hn0
  rw [tau, primeSum_eq hM n]
  have w2 := w2_bounds
  have w3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have hw2 : (w2Hi : ℝ) ≤ 981 / 1000 := by norm_num [w2Hi, l2Hi, s2Hi]
  have hw3 : (w3Hi : ℝ) ≤ 1269 / 1000 := by norm_num [w3Hi, l3Hi, s3Hi]
  have hp : |ppw 1 * Real.sin (Real.pi * (5 * n * Real.log 2 / 3)) +
      ppw 2 * Real.sin (Real.pi * (5 * n * Real.log 3 / 3))| ≤ 2250 / 1000 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ppw 1 by linarith [w2.1]),
      abs_of_nonneg (show (0 : ℝ) ≤ ppw 2 by linarith [w3.1])]
    have s1 := Real.abs_sin_le_one (Real.pi * (5 * n * Real.log 2 / 3))
    have s2 := Real.abs_sin_le_one (Real.pi * (5 * n * Real.log 3 / 3))
    have p1 : ppw 1 * |Real.sin (Real.pi * (5 * n * Real.log 2 / 3))| ≤ ppw 1 :=
      mul_le_of_le_one_right (by linarith [w2.1]) s1
    have p2 : ppw 2 * |Real.sin (Real.pi * (5 * n * Real.log 3 / 3))| ≤ ppw 2 :=
      mul_le_of_le_one_right (by linarith [w3.1]) s2
    linarith [w2.2, w3.2]
  have hL : (6 / 5 : ℝ) / |(n : ℝ)| ≤ 6 / 355 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
  calc |(∫ r, hplus r * sourceS (6 / 5) r n) + Real.pi *
        (ppw 1 * Real.sin (Real.pi * (5 * n * Real.log 2 / 3)) +
          ppw 2 * Real.sin (Real.pi * (5 * n * Real.log 3 / 3)))|
      ≤ |∫ r, hplus r * sourceS (6 / 5) r n| + Real.pi *
        |ppw 1 * Real.sin (Real.pi * (5 * n * Real.log 2 / 3)) +
          ppw 2 * Real.sin (Real.pi * (5 * n * Real.log 3 / 3))| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_pos hpi0]
    _ ≤ (6 / 355 + Real.pi ^ 2 / 2) + Real.pi * (2250 / 1000) := by
        gcongr
        linarith
    _ ≤ 13 := by nlinarith

end AEGIS.CvSTauFarL12V1

#print axioms AEGIS.CvSTauFarL12V1.sum_width_le_inv
#print axioms AEGIS.CvSTauFarL12V1.source_integral_abs_le_inv
#print axioms AEGIS.CvSTauFarL12V1.tau_abs_le_far
