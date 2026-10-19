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
import CvSDigammaSeriesV1
import CvSArctanTailV1

/-!
# The source integral as a positive series, with a bracket (CvS step 7c, ring tree)

From `CvSDigammaSeriesV1.hplus_source_integral` and `half_im_digamma`,

  `∫ h₊ S_k = π Σ' j, 2ω(1 − e^{−c_j L})/(c_j² + ω²)`,  `ω = 2πk/L`, `c_j = 2j + 1/2`
  (`source_integral_series`),

and with the head over `j < J` and `CvSArctanTailV1.tail_bracket` for the rest,
`source_bracket` encloses `(∫ h₊ S_k)/π` between two explicit expressions. Not RH.
-/

open Finset Filter Topology

namespace AEGIS.CvSTauSourceV1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1 AEGIS.CvSArctanTailV1

theorem summable_exp_width {L : ℝ} (hL : 0 ≤ L) (ω : ℝ) :
    Summable fun j => Real.exp (-archWidth j * L) / (archWidth j ^ 2 + ω ^ 2) := by
  refine Summable.of_nonneg_of_le (fun j => by have := archWidth_pos j; positivity)
    (fun j => ?_) (summable_inv_width ω)
  have hc := archWidth_pos j
  have he : Real.exp (-archWidth j * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact he

/-- **Closed form of the source integral.** `∫ h₊ S_k = π Σ' j, 2ω(1 − e^{−c_j L})/(c_j² + ω²)`
with `ω = 2πk/L`, `c_j = 2j + 1/2`. -/
theorem source_integral_series {L : ℝ} (hL : 0 < L) (k : ℤ) :
    ∫ r, hplus r * sourceS L r k = Real.pi * ∑' j, 2 * (2 * Real.pi * k / L) *
      (1 - Real.exp (-archWidth j * L)) / (archWidth j ^ 2 + (2 * Real.pi * k / L) ^ 2) := by
  rw [hplus_source_integral hL k]
  have hh := half_im_digamma (2 * Real.pi * k / L)
  rw [show 2 * Real.pi * k / L / 2 = Real.pi * k / L by ring] at hh
  rw [hh]
  set ω := 2 * Real.pi * k / L with hω
  have hs1 : Summable fun j => ω / (archWidth j ^ 2 + ω ^ 2) :=
    ((summable_inv_width ω).mul_left ω).congr fun j => by ring
  have hs2 : Summable fun j => ω * (Real.exp (-archWidth j * L) / (archWidth j ^ 2 + ω ^ 2)) :=
    (summable_exp_width hL.le ω).mul_left ω
  rw [← tsum_mul_left, ← hs1.tsum_sub hs2, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext j
  have hc := archWidth_pos j
  have hd : archWidth j ^ 2 + ω ^ 2 ≠ 0 := by positivity
  field_simp

/-- `archWidth (J + j) = archWidth J + 2j`. -/
theorem archWidth_add (J j : ℕ) : archWidth (J + j) = archWidth J + 2 * j := by
  unfold archWidth; push_cast; ring

/-- **Bracket for the source integral.** With `ω = 2πk/L ≥ 1`, `H` the head over `j < J`
and `A = arctan(ω/(c_J − 1))`:
`H + A − (ω/3)(c_J − 1)⁻³ − e^{−c_J L} A ≤ (∫ h₊ S_k)/π ≤ H + A`. -/
theorem source_bracket {L : ℝ} (hL : 0 < L) (k : ℤ) (J : ℕ)
    (hω : 1 ≤ 2 * Real.pi * k / L) (hJ1 : 2 < archWidth J)
    (hJ : (2 * Real.pi * k / L) ^ 2 / 3 + 3 ≤ archWidth J ^ 2) :
    (∑ j ∈ range J, 2 * (2 * Real.pi * k / L) * (1 - Real.exp (-archWidth j * L)) /
        (archWidth j ^ 2 + (2 * Real.pi * k / L) ^ 2)) +
      Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) -
      (2 * Real.pi * k / L) / 3 * (1 / (archWidth J - 1) ^ 3) -
      Real.exp (-archWidth J * L) * Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) ≤
      (∫ r, hplus r * sourceS L r k) / Real.pi ∧
    (∫ r, hplus r * sourceS L r k) / Real.pi ≤
      (∑ j ∈ range J, 2 * (2 * Real.pi * k / L) * (1 - Real.exp (-archWidth j * L)) /
        (archWidth j ^ 2 + (2 * Real.pi * k / L) ^ 2)) +
      Real.arctan ((2 * Real.pi * k / L) / (archWidth J - 1)) := by
  rw [source_integral_series hL k, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  set ω := 2 * Real.pi * k / L with hω_def
  set f : ℕ → ℝ := fun j => 2 * ω * (1 - Real.exp (-archWidth j * L)) / (archWidth j ^ 2 + ω ^ 2)
    with hf
  set g : ℕ → ℝ := fun j => 2 * ω / ((archWidth J + 2 * j) ^ 2 + ω ^ 2) with hg
  set e : ℕ → ℝ := fun j => 2 * ω * Real.exp (-archWidth (J + j) * L) /
    ((archWidth J + 2 * j) ^ 2 + ω ^ 2) with he
  obtain ⟨hgs, hglo, hghi⟩ := tail_bracket hω hJ1 hJ
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
  have he0 : 0 ≤ ∑' j, e j := tsum_nonneg fun j => by simp only [he]; have := archWidth_pos J; positivity
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
  have hA0 : 0 ≤ Real.arctan (ω / (archWidth J - 1)) := by
    apply Real.arctan_nonneg.mpr; apply div_nonneg (by linarith); linarith
  have hE0 : 0 ≤ Real.exp (-archWidth J * L) := (Real.exp_pos _).le
  rw [hsplit]
  constructor
  · have h1 : Real.exp (-archWidth J * L) * ∑' j, g j ≤
        Real.exp (-archWidth J * L) * Real.arctan (ω / (archWidth J - 1)) :=
      mul_le_mul_of_nonneg_left hghi hE0
    linarith
  · linarith

end AEGIS.CvSTauSourceV1

#print axioms AEGIS.CvSTauSourceV1.source_integral_series
#print axioms AEGIS.CvSTauSourceV1.source_bracket
