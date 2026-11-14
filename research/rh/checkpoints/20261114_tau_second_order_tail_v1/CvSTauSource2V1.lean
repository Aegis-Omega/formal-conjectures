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
import CvSTauSourceV1
import CvSArctanTail2V1
import CvSTauL12V1

/-!
# The source integral with the second-order tail (CvS step 7c, second order)

`CvSTauSourceV1.source_bracket` with `CvSArctanTail2V1.tail2_bracket` in place of the first-order
arctan tail. With `ω = 2πk/L ≥ 1`, the head `H` over `j < J`, `c = c_J ≥ 2`,
`A = arctan(ω/(c − 1))`, `P = phi2 ω (c − 1)` and `ε = 5A/(c² + ω²)²`:

  `H + P − ε − 2 e^{−cL} A ≤ (∫ h₊ S_k)/π ≤ H + P + ε`   (`source_bracket2`).

There is no condition between `c_J` and `ω`, so the head can stop at a fixed `J` for every
large `k`. `atLo`, `atHi` enclose `arctan x` for a rational `x ≥ 0`, `x ≠ 1`, on either side of `1`
(`arctan x = π/2 − arctan(1/x)` for `x > 1`, `at_bounds`). Not RH.
-/

open Finset Filter Topology

namespace AEGIS.CvSTauSource2V1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
  AEGIS.CvSTauSourceV1 AEGIS.CvSArctanTail2V1 AEGIS.CvSArctanTailV1
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds atPartial atPartial_cast)

/-- `phi2 ω d ≤ arctan(ω/d)` for `d > 0`, `ω ≥ 0`. -/
theorem phi2_le_arctan {ω d : ℝ} (hω : 0 ≤ ω) (hd : 0 < d) : phi2 ω d ≤ Real.arctan (ω / d) := by
  simp only [phi2]
  have : 0 ≤ d * ω / (3 * (d ^ 2 + ω ^ 2) ^ 2) := by positivity
  linarith

/-- **Bracket for the source integral, second order.** -/
theorem source_bracket2 {L : ℝ} (hL : 0 < L) (k : ℤ) (J : ℕ)
    (hω : 1 ≤ 2 * Real.pi * k / L) (hJ : 2 ≤ archWidth J) :
    (∑ j ∈ range J, 2 * (2 * Real.pi * k / L) * (1 - Real.exp (-archWidth j * L)) /
        (archWidth j ^ 2 + (2 * Real.pi * k / L) ^ 2)) +
      phi2 (2 * Real.pi * k / L) (archWidth J - 1) -
      5 * Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) /
        (archWidth J ^ 2 + (2 * Real.pi * k / L) ^ 2) ^ 2 -
      2 * Real.exp (-archWidth J * L) * Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) ≤
      (∫ r, hplus r * sourceS L r k) / Real.pi ∧
    (∫ r, hplus r * sourceS L r k) / Real.pi ≤
      (∑ j ∈ range J, 2 * (2 * Real.pi * k / L) * (1 - Real.exp (-archWidth j * L)) /
        (archWidth j ^ 2 + (2 * Real.pi * k / L) ^ 2)) +
      phi2 (2 * Real.pi * k / L) (archWidth J - 1) +
      5 * Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) /
        (archWidth J ^ 2 + (2 * Real.pi * k / L) ^ 2) ^ 2 := by
  rw [source_integral_series hL k, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  set ω := 2 * Real.pi * k / L with hω_def
  set f : ℕ → ℝ := fun j => 2 * ω * (1 - Real.exp (-archWidth j * L)) / (archWidth j ^ 2 + ω ^ 2)
    with hf
  set g : ℕ → ℝ := fun j => 2 * ω / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) with hg
  set e : ℕ → ℝ := fun j => 2 * ω * Real.exp (-archWidth (J + j) * L) /
    ((archWidth J + 2 * j) ^ 2 + ω ^ 2) with he
  obtain ⟨hgs, hgb⟩ := tail2_bracket hω hJ
  set A := Real.arctan (ω / (archWidth J - 1)) with hA
  set ε := 5 * A / (archWidth J ^ 2 + ω ^ 2) ^ 2 with hε
  set P := phi2 ω (archWidth J - 1) with hP
  have hd0 : 0 < archWidth J - 1 := by linarith
  have hA0 : 0 ≤ A := Real.arctan_nonneg.mpr (div_nonneg (by linarith) hd0.le)
  have hPA : P ≤ A := phi2_le_arctan (by linarith) hd0
  have hρ : 16 ≤ (archWidth J ^ 2 + ω ^ 2) ^ 2 := by
    have : 4 ≤ archWidth J ^ 2 + ω ^ 2 := by nlinarith
    nlinarith
  have hεA : ε ≤ A := by
    rw [hε, div_le_iff₀ (by positivity)]; nlinarith
  rw [abs_le] at hgb
  obtain ⟨hglo, hghi⟩ := hgb
  have hfs : Summable f := by
    refine ((summable_inv_width ω).mul_left (2 * ω)).of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    · have hc := archWidth_pos j
      have : Real.exp (-archWidth j * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      simp only [hf]; apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith) (by linarith)
    · have hc := archWidth_pos j
      have h0 : 0 < Real.exp (-archWidth j * L) := Real.exp_pos _
      show 2 * ω * (1 - Real.exp (-archWidth j * L)) / (archWidth j ^ 2 + ω ^ 2) ≤
        2 * ω * (1 / (archWidth j ^ 2 + ω ^ 2))
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
  have htail : ∀ j, f (J + j) = g j - e j := fun j => by
    simp only [hf, hg, he, archWidth_add]
    ring
  have hes : Summable e := by
    refine hgs.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    · simp only [he]; have := archWidth_pos J; positivity
    · have hc := archWidth_pos (J + j)
      have h1 : Real.exp (-archWidth (J + j) * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hd : 0 < (archWidth J + 2 * j) ^ 2 + ω ^ 2 := by have := archWidth_pos J; positivity
      show 2 * ω * Real.exp (-archWidth (J + j) * L) / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) ≤
        2 * ω / ((archWidth J + 2 * j) ^ 2 + ω ^ 2)
      rw [div_le_div_iff_of_pos_right hd]
      nlinarith
  have hsplit : ∑' j, f j = (∑ j ∈ range J, f j) + ((∑' j, g j) - ∑' j, e j) := by
    rw [← hfs.sum_add_tsum_nat_add J]
    congr 1
    rw [← hgs.tsum_sub hes]
    exact tsum_congr fun j => by rw [add_comm j J]; exact htail j
  have he0 : 0 ≤ ∑' j, e j := tsum_nonneg fun j => by
    simp only [he]; have := archWidth_pos J; positivity
  have heup : ∑' j, e j ≤ Real.exp (-archWidth J * L) * ∑' j, g j := by
    rw [← tsum_mul_left]
    refine hes.tsum_le_tsum (fun j => ?_) (hgs.mul_left _)
    show 2 * ω * Real.exp (-archWidth (J + j) * L) / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) ≤
      Real.exp (-archWidth J * L) * (2 * ω / ((archWidth J + 2 * j) ^ 2 + ω ^ 2))
    have hd : 0 < (archWidth J + 2 * j) ^ 2 + ω ^ 2 := by have := archWidth_pos J; positivity
    have hmono : Real.exp (-archWidth (J + j) * L) ≤ Real.exp (-archWidth J * L) := by
      apply Real.exp_le_exp.mpr
      rw [archWidth_add]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    calc 2 * ω * Real.exp (-archWidth (J + j) * L) / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) ≤
        2 * ω * Real.exp (-archWidth J * L) / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by linarith)) hd.le
      _ = Real.exp (-archWidth J * L) * (2 * ω / ((archWidth J + 2 * j) ^ 2 + ω ^ 2)) := by ring
  have hE0 : 0 ≤ Real.exp (-archWidth J * L) := (Real.exp_pos _).le
  have hg2 : ∑' j, g j ≤ 2 * A := by linarith
  rw [hsplit]
  constructor
  · have h1 : Real.exp (-archWidth J * L) * ∑' j, g j ≤ Real.exp (-archWidth J * L) * (2 * A) :=
      mul_le_mul_of_nonneg_left hg2 hE0
    nlinarith
  · linarith

/-! ### arctan of a nonnegative rational on either side of `1` -/

def atLo (x : ℚ) (K : ℕ) : ℚ :=
  if x < 1 then atPartial x (2 * K) else piLo / 2 - atPartial x⁻¹ (2 * K + 1)

def atHi (x : ℚ) (K : ℕ) : ℚ :=
  if x < 1 then atPartial x (2 * K + 1) else piHi / 2 - atPartial x⁻¹ (2 * K)

theorem at_bounds {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≠ 1) (K : ℕ) :
    (atLo x K : ℝ) ≤ Real.arctan x ∧ Real.arctan x ≤ atHi x K := by
  obtain ⟨hpl, hph⟩ := pi_bounds
  by_cases hx : x < 1
  · have hx' : (x : ℝ) < 1 := by exact_mod_cast hx
    have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
    simp only [atLo, atHi]
    rw [if_pos hx, if_pos hx, atPartial_cast, atPartial_cast]
    exact ⟨partial_le_arctan hx0 hx' K, arctan_le_partial hx0 hx' K⟩
  · have hx1 : 1 < x := lt_of_le_of_ne (not_lt.mp hx) (Ne.symm h1)
    have hx1' : (1 : ℝ) < x := by exact_mod_cast hx1
    have hxpos : (0 : ℝ) < x := by linarith
    have hi0 : (0 : ℝ) ≤ (x : ℝ)⁻¹ := inv_nonneg.mpr hxpos.le
    have hi1 : (x : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1'
    have hrel : Real.arctan x = Real.pi / 2 - Real.arctan (x : ℝ)⁻¹ := by
      rw [Real.arctan_inv_of_pos hxpos]; ring
    simp only [atLo, atHi]
    rw [if_neg hx, if_neg hx]
    push_cast
    rw [atPartial_cast, atPartial_cast, hrel]
    push_cast
    have a1 := arctan_le_partial hi0 hi1 K
    have a2 := partial_le_arctan hi0 hi1 K
    constructor <;> linarith

end AEGIS.CvSTauSource2V1

#print axioms AEGIS.CvSTauSource2V1.source_bracket2
#print axioms AEGIS.CvSTauSource2V1.at_bounds
