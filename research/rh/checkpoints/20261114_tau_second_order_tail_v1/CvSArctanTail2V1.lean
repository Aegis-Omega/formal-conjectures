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
import CvSArctanTailV1

/-!
# A second-order tail for `Σ 2ω/(c_j² + ω²)` (CvS step 7b, second order)

`CvSArctanTailV1.tail_bracket` telescopes `arctan(ω/(c−1)) − arctan(ω/(c+1))`. Its lower bound
loses `(ω/3)(c₀−1)⁻³` and its upper bound needs `c₀² ≥ ω²/3 + 3`, so the head of every `τ_k`
check runs past `c ≈ ω`. Here the telescoped function carries the Euler–Maclaurin term `f'/12`:

  `phi2 ω c = arctan(ω/c) − cω/(3(c²+ω²)²)`,

and each step is within `8ω/(c²+ω²)³` of `2ω/(c²+ω²)` for every `c ≥ 2`, `ω ≥ 1`
(`step2_bounds`). Times `(c²+ω²)³/ω`, the step error is a rational function of `X = c²`,
`Y = ω²` (numerator `stepN`); its two sides become polynomials in `X − 4`, `Y − 1` with
nonnegative integer coefficients (`loQ`, `hiQ`), so `positivity` proves them. With
`ω/(c²+ω²) ≤ (5/8)(arctan(ω/(c−1)) − arctan(ω/(c+1)))` (`inv_sq_le_step`), the errors telescope:

  `|Σ' j, 2ω/(c_j²+ω²) − phi2 ω (c₀−1)| ≤ 5 arctan(ω/(c₀−1)) / (c₀²+ω²)²`   (`tail2_bracket`)

for `c_j = c₀ + 2j`, `c₀ ≥ 2`, `ω ≥ 1`, with no condition between `c₀` and `ω`. Not RH.
-/

open Finset Filter Topology

namespace AEGIS.CvSArctanTail2V1

open AEGIS.CvSArctanTailV1

/-! ### Two polynomial inequalities in `X = c²`, `Y = ω²` -/

/-- The numerator of the step error, in `X = c²`, `Y = ω²`. -/
def stepN (X Y : ℝ) : ℝ :=
  7 * X ^ 5 + 7 * X ^ 4 * Y - 31 * X ^ 4 - 10 * X ^ 3 * Y ^ 2 - 16 * X ^ 3 * Y + 54 * X ^ 3 - 2 * X
  ^ 2 * Y ^ 3 + 26 * X ^ 2 * Y ^ 2 + 6 * X ^ 2 * Y - 46 * X ^ 2 + 19 * X * Y ^ 4 + 40 * X * Y ^ 3 -
  22 * X * Y ^ 2 + 8 * X * Y + 19 * X + 11 * Y ^ 5 + 29 * Y ^ 4 + 26 * Y ^ 3 + 6 * Y ^ 2 - 5 * Y - 3

/-- `((c−1)² + ω²)((c+1)² + ω²)` in `X = c²`, `Y = ω²`. -/
def stepP (X Y : ℝ) : ℝ := (X + Y + 1) ^ 2 - 4 * X

/-- `24 E³ P² − 2 N R²` at `X = s + 4`, `Y = t + 1`. -/
def loQ (s t : ℝ) : ℝ :=
  470400 + 1079680 * t + 875904 * t ^ 2 + 342120 * t ^ 3 + 70224 * t ^ 4 + 7362 * t ^ 5 + 324 * t ^
  6 + 2 * t ^ 7 + 689920 * s + 1420032 * s * t + 982680 * s * t ^ 2 + 312696 * s * t ^ 3 + 49122 * s
  * t ^ 4 + 3552 * s * t ^ 5 + 86 * s * t ^ 6 + 431104 * s ^ 2 + 774392 * s ^ 2 * t + 436648 * s ^ 2
  * t ^ 2 + 105332 * s ^ 2 * t ^ 3 + 11140 * s ^ 2 * t ^ 4 + 410 * s ^ 2 * t ^ 5 + 149832 * s ^ 3 +
  225704 * s ^ 3 * t + 96804 * s ^ 3 * t ^ 2 + 15648 * s ^ 3 * t ^ 3 + 830 * s ^ 3 * t ^ 4 + 31528 *
  s ^ 4 + 37290 * s ^ 4 * t + 10764 * s ^ 4 * t ^ 2 + 870 * s ^ 4 * t ^ 3 + 4058 * s ^ 5 + 3328 * s
  ^ 5 * t + 482 * s ^ 5 * t ^ 2 + 300 * s ^ 6 + 126 * s ^ 6 * t + 10 * s ^ 7

/-- `120 E⁵ P² + 10 N R² E² − 96 Y² R³ P²` at `X = s + 4`, `Y = t + 1`. -/
def hiQ (s t : ℝ) : ℝ :=
  55872000 + 117414400 * t + 110184320 * t ^ 2 + 60244480 * t ^ 3 + 21130080 * t ^ 4 + 4957176 * t ^
  5 + 783648 * t ^ 6 + 80822 * t ^ 7 + 4924 * t ^ 8 + 134 * t ^ 9 + 120793600 * s + 222780160 * s *
  t + 180720000 * s * t ^ 2 + 83750400 * s * t ^ 3 + 24201336 * s * t ^ 4 + 4479336 * s * t ^ 5 +
  521282 * s * t ^ 6 + 35000 * s * t ^ 7 + 1038 * s * t ^ 8 + 116737920 * s ^ 2 + 185724160 * s ^ 2
  * t + 127156800 * s ^ 2 * t ^ 2 + 48314928 * s ^ 2 * t ^ 3 + 10975656 * s ^ 2 * t ^ 4 + 1493502 *
  s ^ 2 * t ^ 5 + 113208 * s ^ 2 * t ^ 6 + 3704 * s ^ 2 * t ^ 7 + 66272640 * s ^ 3 + 89093120 * s ^
  3 * t + 49985008 * s ^ 3 * t ^ 2 + 14907536 * s ^ 3 * t ^ 3 + 2486138 * s ^ 3 * t ^ 4 + 220120 * s
  ^ 3 * t ^ 5 + 8120 * s ^ 3 * t ^ 6 + 24364640 * s ^ 4 + 26929496 * s ^ 4 * t + 11884272 * s ^ 4 *
  t ^ 2 + 2604866 * s ^ 4 * t ^ 3 + 282800 * s ^ 4 * t ^ 4 + 12180 * s ^ 4 * t ^ 5 + 6015256 * s ^ 5
  + 5253768 * s ^ 5 * t + 1710822 * s ^ 5 * t ^ 2 + 244904 * s ^ 5 * t ^ 3 + 12964 * s ^ 5 * t ^ 4 +
  997064 * s ^ 6 + 646026 * s ^ 6 * t + 138120 * s ^ 6 * t ^ 2 + 9688 * s ^ 6 * t ^ 3 + 106974 * s ^
  7 + 45768 * s ^ 7 * t + 4824 * s ^ 7 * t ^ 2 + 6740 * s ^ 8 + 1430 * s ^ 8 * t + 190 * s ^ 9

theorem loQ_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ loQ s t := by
  lift s to NNReal using hs
  lift t to NNReal using ht
  unfold loQ
  positivity

theorem hiQ_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ hiQ s t := by
  lift s to NNReal using hs
  lift t to NNReal using ht
  unfold hiQ
  positivity

theorem lo_poly {X Y : ℝ} (hX : 4 ≤ X) (hY : 1 ≤ Y) :
    2 * stepN X Y * (X + Y) ^ 2 ≤ 24 * (X + Y - 1) ^ 3 * stepP X Y ^ 2 := by
  have h := loQ_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
  have e : 24 * (X + Y - 1) ^ 3 * stepP X Y ^ 2 - 2 * stepN X Y * (X + Y) ^ 2 =
      loQ (X - 4) (Y - 1) := by
    simp only [stepN, stepP, loQ]; ring
  linarith

theorem hi_poly {X Y : ℝ} (hX : 4 ≤ X) (hY : 1 ≤ Y) :
    96 * Y ^ 2 * (X + Y) ^ 3 * stepP X Y ^ 2 ≤
      120 * (X + Y - 1) ^ 5 * stepP X Y ^ 2 + 10 * stepN X Y * (X + Y) ^ 2 * (X + Y - 1) ^ 2 := by
  have h := hiQ_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
  have e : 120 * (X + Y - 1) ^ 5 * stepP X Y ^ 2 + 10 * stepN X Y * (X + Y) ^ 2 * (X + Y - 1) ^ 2 -
      96 * Y ^ 2 * (X + Y) ^ 3 * stepP X Y ^ 2 = hiQ (X - 4) (Y - 1) := by
    simp only [stepN, stepP, hiQ]; ring
  linarith

/-! ### One step -/

/-- The second-order tail function `arctan(ω/c) − cω/(3(c²+ω²)²)`. -/
noncomputable def phi2 (ω c : ℝ) : ℝ := Real.arctan (ω / c) - c * ω / (3 * (c ^ 2 + ω ^ 2) ^ 2)

theorem arctan_le_quintic {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) :
    Real.arctan v ≤ v - v ^ 3 / 3 + v ^ 5 / 5 := by
  have := arctan_le_partial h0 h1 1
  simp only [atTerm, sum_range_succ, sum_range_zero] at this
  norm_num at this
  linarith

/-- The step of `phi2` is `arctan(2ω/E)` plus the two rational corrections. -/
theorem phi2_step {ω c : ℝ} (hω : 0 ≤ ω) (hc : 1 < c) :
    phi2 ω (c - 1) - phi2 ω (c + 1) =
      Real.arctan (2 * ω / (c ^ 2 + ω ^ 2 - 1)) - (c - 1) * ω / (3 * ((c - 1) ^ 2 + ω ^ 2) ^ 2) +
        (c + 1) * ω / (3 * ((c + 1) ^ 2 + ω ^ 2) ^ 2) := by
  have h := arctan_step hω hc
  rw [show c ^ 2 - 1 + ω ^ 2 = c ^ 2 + ω ^ 2 - 1 by ring] at h
  simp only [phi2]
  linarith

/-- The rational part of the step error. -/
theorem step_rational_eq {ω c : ℝ} (hω : 1 ≤ ω) (hc : 2 ≤ c) :
    2 * ω / (c ^ 2 + ω ^ 2 - 1) - (2 * ω / (c ^ 2 + ω ^ 2 - 1)) ^ 3 / 3 - 2 * ω / (c ^ 2 + ω ^ 2) -
        (c - 1) * ω / (3 * ((c - 1) ^ 2 + ω ^ 2) ^ 2) +
        (c + 1) * ω / (3 * ((c + 1) ^ 2 + ω ^ 2) ^ 2) =
      -(2 * ω * stepN (c ^ 2) (ω ^ 2)) /
        (3 * (c ^ 2 + ω ^ 2) * (c ^ 2 + ω ^ 2 - 1) ^ 3 *
          (((c - 1) ^ 2 + ω ^ 2) * ((c + 1) ^ 2 + ω ^ 2)) ^ 2) := by
  have hE : 0 < c ^ 2 + ω ^ 2 - 1 := by nlinarith
  have hR : 0 < c ^ 2 + ω ^ 2 := by nlinarith
  have hm : 0 < (c - 1) ^ 2 + ω ^ 2 := by nlinarith
  have hp : 0 < (c + 1) ^ 2 + ω ^ 2 := by nlinarith
  field_simp
  simp only [stepN]
  ring

/-- **One step.** `|phi2(c−1) − phi2(c+1) − 2ω/(c²+ω²)| ≤ 8ω/(c²+ω²)³` for `c ≥ 2`, `ω ≥ 1`. -/
theorem step2_bounds {ω c : ℝ} (hω : 1 ≤ ω) (hc : 2 ≤ c) :
    |phi2 ω (c - 1) - phi2 ω (c + 1) - 2 * ω / (c ^ 2 + ω ^ 2)| ≤
      8 * ω / (c ^ 2 + ω ^ 2) ^ 3 := by
  have hω0 : 0 < ω := by linarith
  have hE : 0 < c ^ 2 + ω ^ 2 - 1 := by nlinarith
  have hR : 0 < c ^ 2 + ω ^ 2 := by nlinarith
  have hm : 0 < (c - 1) ^ 2 + ω ^ 2 := by nlinarith
  have hp : 0 < (c + 1) ^ 2 + ω ^ 2 := by nlinarith
  have hv0 : 0 ≤ 2 * ω / (c ^ 2 + ω ^ 2 - 1) := by positivity
  have hv1 : 2 * ω / (c ^ 2 + ω ^ 2 - 1) < 1 := by
    rw [div_lt_one hE]; nlinarith [sq_nonneg (ω - 1)]
  have hQ : stepP (c ^ 2) (ω ^ 2) = ((c - 1) ^ 2 + ω ^ 2) * ((c + 1) ^ 2 + ω ^ 2) := by
    simp only [stepP]; ring
  have hlo := lo_poly (X := c ^ 2) (Y := ω ^ 2) (by nlinarith) (by nlinarith)
  have hhi := hi_poly (X := c ^ 2) (Y := ω ^ 2) (by nlinarith) (by nlinarith)
  rw [hQ] at hlo hhi
  set v := 2 * ω / (c ^ 2 + ω ^ 2 - 1) with hv
  set E := c ^ 2 + ω ^ 2 - 1 with hEdef
  set R := c ^ 2 + ω ^ 2 with hRdef
  set Q := ((c - 1) ^ 2 + ω ^ 2) * ((c + 1) ^ 2 + ω ^ 2) with hQdef
  set N := stepN (c ^ 2) (ω ^ 2) with hN
  have hQ0 : 0 < Q := mul_pos hm hp
  have hrat := step_rational_eq hω hc
  rw [phi2_step hω0.le (by linarith)]
  have a1 := sub_cube_le_arctan hv0 hv1
  have a2 := arctan_le_quintic hv0 hv1
  rw [abs_le]
  constructor
  · -- lower: the step error is at least the rational part
    have key : 2 * ω * N / (3 * R * E ^ 3 * Q ^ 2) ≤ 8 * ω / R ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hωR : 0 ≤ ω * R := by positivity
      calc 2 * ω * N * R ^ 3 = (ω * R) * (2 * N * R ^ 2) := by ring
        _ ≤ (ω * R) * (24 * E ^ 3 * Q ^ 2) := mul_le_mul_of_nonneg_left hlo hωR
        _ = 8 * ω * (3 * R * E ^ 3 * Q ^ 2) := by ring
    have hneg : -(2 * ω * N) / (3 * R * E ^ 3 * Q ^ 2) = -(2 * ω * N / (3 * R * E ^ 3 * Q ^ 2)) :=
      neg_div _ _
    rw [hneg] at hrat
    have : -(8 * ω / R ^ 3) ≤ -(2 * ω * N / (3 * R * E ^ 3 * Q ^ 2)) := neg_le_neg key
    have e1 : 8 * ω / R ^ 3 = 8 * ω / (c ^ 2 + ω ^ 2) ^ 3 := rfl
    linarith
  · -- upper: the quintic term on top of the rational part
    have key : v ^ 5 / 5 - 2 * ω * N / (3 * R * E ^ 3 * Q ^ 2) ≤ 8 * ω / R ^ 3 := by
      have e : v ^ 5 / 5 - 2 * ω * N / (3 * R * E ^ 3 * Q ^ 2) =
          ω * (96 * ω ^ 4 * R * Q ^ 2 - 10 * N * E ^ 2) / (15 * R * E ^ 5 * Q ^ 2) := by
        rw [hv]
        field_simp
        ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have hωR : 0 ≤ ω * R := by positivity
      have h2 : 96 * ω ^ 4 * R ^ 3 * Q ^ 2 - 10 * N * E ^ 2 * R ^ 2 ≤ 120 * E ^ 5 * Q ^ 2 := by
        have : (ω ^ 2) ^ 2 = ω ^ 4 := by ring
        rw [this] at hhi
        linarith
      calc ω * (96 * ω ^ 4 * R * Q ^ 2 - 10 * N * E ^ 2) * R ^ 3 =
            (ω * R) * (96 * ω ^ 4 * R ^ 3 * Q ^ 2 - 10 * N * E ^ 2 * R ^ 2) := by ring
        _ ≤ (ω * R) * (120 * E ^ 5 * Q ^ 2) := mul_le_mul_of_nonneg_left h2 hωR
        _ = 8 * ω * (15 * R * E ^ 5 * Q ^ 2) := by ring
    have hneg : -(2 * ω * N) / (3 * R * E ^ 3 * Q ^ 2) = -(2 * ω * N / (3 * R * E ^ 3 * Q ^ 2)) :=
      neg_div _ _
    rw [hneg] at hrat
    have e1 : 8 * ω / R ^ 3 = 8 * ω / (c ^ 2 + ω ^ 2) ^ 3 := rfl
    linarith

/-! ### The telescoping majorant -/

/-- `ω/(c²+ω²) ≤ (5/8)(arctan(ω/(c−1)) − arctan(ω/(c+1)))` for `c ≥ 2`, `ω ≥ 1`. -/
theorem inv_sq_le_step {ω c : ℝ} (hω : 1 ≤ ω) (hc : 2 ≤ c) :
    ω / (c ^ 2 + ω ^ 2) ≤ 5 / 8 * (Real.arctan (ω / (c - 1)) - Real.arctan (ω / (c + 1))) := by
  have hω0 : 0 < ω := by linarith
  rw [arctan_step hω0.le (by linarith), show c ^ 2 - 1 + ω ^ 2 = c ^ 2 + ω ^ 2 - 1 by ring]
  have hE : 0 < c ^ 2 + ω ^ 2 - 1 := by nlinarith
  have hR : 0 < c ^ 2 + ω ^ 2 := by nlinarith
  have hv0 : 0 ≤ 2 * ω / (c ^ 2 + ω ^ 2 - 1) := by positivity
  have hv1 : 2 * ω / (c ^ 2 + ω ^ 2 - 1) < 1 := by
    rw [div_lt_one hE]; nlinarith [sq_nonneg (ω - 1)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sub_cube_le_arctan hv0 hv1) (by norm_num))
  set E := c ^ 2 + ω ^ 2 - 1 with hEdef
  have hR' : c ^ 2 + ω ^ 2 = E + 1 := by rw [hEdef]; ring
  have hωE : ω ^ 2 + 3 ≤ E := by rw [hEdef]; nlinarith
  have e : 5 / 8 * (2 * ω / E - (2 * ω / E) ^ 3 / 3) = 5 * ω * (3 * E ^ 2 - 4 * ω ^ 2) / (12 * E ^ 3) := by
    field_simp
    ring
  rw [e, hR', div_le_div_iff₀ (by linarith) (by positivity)]
  have hpoly : 12 * E ^ 3 ≤ 5 * (3 * E ^ 2 - 4 * ω ^ 2) * (E + 1) := by
    have h1 : 3 * E ^ 2 - 4 * E + 12 ≤ 3 * E ^ 2 - 4 * ω ^ 2 := by nlinarith
    have h2 : 0 ≤ 3 * E ^ 3 - 5 * E ^ 2 + 40 * E + 60 := by nlinarith [sq_nonneg (E - 1)]
    nlinarith
  nlinarith

/-! ### The tail -/

/-- **The second-order tail bracket.** With `c_j = c₀ + 2j`, `c₀ ≥ 2` and `ω ≥ 1`,
`|Σ' j, 2ω/(c_j²+ω²) − phi2 ω (c₀−1)| ≤ 5 arctan(ω/(c₀−1))/(c₀²+ω²)²`. -/
theorem tail2_bracket {ω c₀ : ℝ} (hω : 1 ≤ ω) (hc : 2 ≤ c₀) :
    Summable (fun j : ℕ => 2 * ω / ((c₀ + 2 * j) ^ 2 + ω ^ 2)) ∧
    |∑' j : ℕ, 2 * ω / ((c₀ + 2 * j) ^ 2 + ω ^ 2) - phi2 ω (c₀ - 1)| ≤
      5 * Real.arctan (ω / (c₀ - 1)) / (c₀ ^ 2 + ω ^ 2) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  set c : ℕ → ℝ := fun j => c₀ + 2 * j with hcdef
  have hcj : ∀ j, c₀ ≤ c j := fun j => by
    simp only [hcdef]; exact le_add_of_nonneg_right (by positivity)
  have hcs : ∀ j, c (j + 1) = c j + 2 := fun j => by simp only [hcdef]; push_cast; ring
  have hlin : Tendsto (fun j : ℕ => c j - 1) atTop atTop := by
    simp only [hcdef]
    apply tendsto_atTop_add_const_right
    apply tendsto_atTop_add_const_left
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  -- the arctan majorant
  set T : ℕ → ℝ := fun j => Real.arctan (ω / (c j - 1)) with hT
  have hTanti : Antitone T := by
    refine antitone_nat_of_succ_le fun j => ?_
    apply Real.arctan_mono
    rw [hcs]
    have := hcj j
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have hT0 : Tendsto T atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ω)).div_atTop hlin
    simpa [hT] using (Real.continuous_arctan.tendsto 0).comp this |>.congr' (by
      filter_upwards with j; simp)
  have hA := hasSum_telescope hTanti hT0
  have hTstep : ∀ j, T j - T (j + 1) =
      Real.arctan (ω / (c j - 1)) - Real.arctan (ω / (c j + 1)) := fun j => by
    simp only [hT]; rw [hcs, show c j + 2 - 1 = c j + 1 by ring]
  -- the summand
  set f : ℕ → ℝ := fun j => 2 * ω / (c j ^ 2 + ω ^ 2) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by simp only [hf]; positivity
  have hfle : ∀ j, f j ≤ 5 / 4 * (T j - T (j + 1)) := fun j => by
    have := inv_sq_le_step hω (by linarith [hcj j] : (2 : ℝ) ≤ c j)
    rw [hTstep]
    simp only [hf]
    calc 2 * ω / (c j ^ 2 + ω ^ 2) = 2 * (ω / (c j ^ 2 + ω ^ 2)) := by ring
      _ ≤ 2 * (5 / 8 * (Real.arctan (ω / (c j - 1)) - Real.arctan (ω / (c j + 1)))) := by linarith
      _ = _ := by ring
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfle (hA.summable.mul_left _)
  -- the telescoped function
  set F : ℕ → ℝ := fun j => phi2 ω (c j - 1) with hF
  have hFs : ∀ j, F (j + 1) = phi2 ω (c j + 1) := fun j => by
    simp only [hF]; rw [hcs, show c j + 2 - 1 = c j + 1 by ring]
  have hG0 : Tendsto (fun j => (c j - 1) * ω / (3 * ((c j - 1) ^ 2 + ω ^ 2) ^ 2)) atTop (𝓝 0) := by
    have hcube : Tendsto (fun j : ℕ => (c j - 1) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp hlin
    have hB : Tendsto (fun j : ℕ => ω / 3 * ((c j - 1) ^ 3)⁻¹) atTop (𝓝 0) := by
      simpa using hcube.inv_tendsto_atTop.const_mul (ω / 3)
    refine squeeze_zero (fun j => ?_) (fun j => ?_) hB
    · have := hcj j
      have h1 : 0 < c j - 1 := by linarith
      positivity
    · have := hcj j
      have h1 : 0 < c j - 1 := by linarith
      have h4 : (c j - 1) ^ 4 ≤ ((c j - 1) ^ 2 + ω ^ 2) ^ 2 := by
        have : (c j - 1) ^ 2 ≤ (c j - 1) ^ 2 + ω ^ 2 := by nlinarith
        calc (c j - 1) ^ 4 = ((c j - 1) ^ 2) ^ 2 := by ring
          _ ≤ _ := by gcongr
      rw [div_le_iff₀ (by positivity)]
      have e : ω / 3 * ((c j - 1) ^ 3)⁻¹ * (3 * ((c j - 1) ^ 2 + ω ^ 2) ^ 2) =
          ω * ((c j - 1) ^ 2 + ω ^ 2) ^ 2 / (c j - 1) ^ 3 := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hω0.le h1.le)]
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have := hT0.sub hG0
    simp only [sub_zero] at this
    refine this.congr fun j => ?_
    simp only [hF, hT, phi2]
  -- the step errors
  set d : ℕ → ℝ := fun j => F j - F (j + 1) - f j with hd
  set ρ4 : ℝ := (c₀ ^ 2 + ω ^ 2) ^ 2 with hρ4
  have hρ4pos : 0 < ρ4 := by positivity
  have hdle : ∀ j, |d j| ≤ 5 / ρ4 * (T j - T (j + 1)) := fun j => by
    have hcj2 : (2 : ℝ) ≤ c j := by linarith [hcj j]
    have h1 := step2_bounds hω hcj2
    have h2 := inv_sq_le_step hω hcj2
    have e : d j = phi2 ω (c j - 1) - phi2 ω (c j + 1) - 2 * ω / (c j ^ 2 + ω ^ 2) := by
      show F j - F (j + 1) - f j = _
      rw [hFs]
    rw [e]
    refine le_trans h1 ?_
    rw [hTstep]
    have hR : 0 < c j ^ 2 + ω ^ 2 := by positivity
    have hRR : c₀ ^ 2 + ω ^ 2 ≤ c j ^ 2 + ω ^ 2 := by nlinarith [hcj j]
    have hR2 : ρ4 ≤ (c j ^ 2 + ω ^ 2) ^ 2 := by rw [hρ4]; gcongr
    calc 8 * ω / (c j ^ 2 + ω ^ 2) ^ 3 = 8 / (c j ^ 2 + ω ^ 2) ^ 2 * (ω / (c j ^ 2 + ω ^ 2)) := by
          field_simp
      _ ≤ 8 / ρ4 * (ω / (c j ^ 2 + ω ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) hρ4pos hR2
      _ ≤ 8 / ρ4 * (5 / 8 * (Real.arctan (ω / (c j - 1)) - Real.arctan (ω / (c j + 1)))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 5 / ρ4 * (Real.arctan (ω / (c j - 1)) - Real.arctan (ω / (c j + 1))) := by ring
  have hmaj := hA.mul_left (5 / ρ4)
  have hdabs : Summable fun j => |d j| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hdle hmaj.summable
  have hds : Summable d := hdabs.of_abs
  -- the telescoped series sums to `F 0`
  have hSs : Summable fun j => F j - F (j + 1) :=
    (hfs.add hds).congr fun j => by simp only [hd]; ring
  have hsumF : ∑' j, (F j - F (j + 1)) = F 0 := by
    have h1 := hSs.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun n => ∑ i ∈ range n, (F i - F (i + 1))) atTop (𝓝 (F 0)) := by
      simp_rw [Finset.sum_range_sub']
      simpa using (tendsto_const_nhds (x := F 0)).sub hF0
    exact tendsto_nhds_unique h1 h2
  have hsplit : ∑' j, f j = F 0 - ∑' j, d j := by
    rw [← hsumF, ← hSs.tsum_sub hds]
    exact tsum_congr fun j => by simp only [hd]; ring
  have hc0 : c 0 = c₀ := by simp [hcdef]
  have hF00 : F 0 = phi2 ω (c₀ - 1) := by simp only [hF, hc0]
  have hT00 : T 0 = Real.arctan (ω / (c₀ - 1)) := by simp only [hT, hc0]
  refine ⟨hfs, ?_⟩
  rw [hsplit, hF00, show phi2 ω (c₀ - 1) - ∑' j, d j - phi2 ω (c₀ - 1) = -∑' j, d j by ring, abs_neg]
  calc |∑' j, d j| ≤ ∑' j, |d j| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := d) (by simpa [Real.norm_eq_abs] using hdabs)
    _ ≤ 5 / ρ4 * T 0 := hasSum_le hdle hdabs.hasSum hmaj
    _ = 5 * Real.arctan (ω / (c₀ - 1)) / (c₀ ^ 2 + ω ^ 2) ^ 2 := by
        rw [hT00, hρ4]; ring

end AEGIS.CvSArctanTail2V1

#print axioms AEGIS.CvSArctanTail2V1.step2_bounds
#print axioms AEGIS.CvSArctanTail2V1.inv_sq_le_step
#print axioms AEGIS.CvSArctanTail2V1.tail2_bracket
