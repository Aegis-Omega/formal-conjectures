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
import CvSArchDiagV1
import WeilDigammaSeriesHalfPlaneV1
import RHKreinSymbolIntegrationV1

/-!
# The archimedean source value through the repository's `archSymbol` (CvS step 5.2c)

`archSymbol t = Re ψ(1/4 + it/2) − log π` is the archimedean symbol of the repository's
critical-line form (`RHKreinSymbolIntegrationV1`). Using the repository's half-plane digamma
series (`digamma_series_halfPlane_v1`), this file proves, for `ω = 2πn/L` and `c_k = 2k + 1/2`,

`∫ archSymbol(r) S(r, n, L) dr = 2π (½ Im ψ(1/4 + iπn/L) − ω ∑' k, e^{−c_k L}/(c_k² + ω²))`,

which is the closed form `S_n` used by `feshbach_blocks_arb.py` (times `2π`), and for the
diagonal source `D(r)` of `2(1 − y/L) cos(ωy)`,

`∫ archSymbol(r) D(r) dr = 2π archSymbol(ω) + (4π/L) ∑' k, (1 − e^{−c_k L})(c_k² − ω²)/(c_k² + ω²)²`.
-/

open MeasureTheory Set Real Complex

noncomputable section

namespace AEGIS.CvSArchDigammaV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1
open AEGIS.WeilDigammaIntegralReductionV1 (seriesTerm)

theorem quarter_re_pos (t : ℝ) : 0 < ((1 / 4 : ℂ) + (t : ℂ) * I).re := by
  simp

theorem seriesTerm_re (k : ℕ) (r : ℝ) :
    (seriesTerm ((1 / 4 : ℂ) + (r : ℂ) * I / 2) k).re = archTerm k r := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 1 / 4) ^ 2 + (r / 2) ^ 2 ≠ 0 := by positivity
  have h3 : (2 * (k : ℝ) + 1 / 2) ^ 2 + r ^ 2 ≠ 0 := by positivity
  simp [seriesTerm, archTerm, archWidth, Complex.normSq_apply]
  field_simp
  ring

theorem seriesTerm_im (k : ℕ) (t : ℝ) :
    (seriesTerm ((1 / 4 : ℂ) + (t : ℂ) * I) k).im = t / (((k : ℝ) + 1 / 4) ^ 2 + t ^ 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : ((k : ℝ) + 1 / 4) ^ 2 + t ^ 2 ≠ 0 := by positivity
  simp [seriesTerm, Complex.normSq_apply]
  field_simp
  ring

/-- `archSymbol r = ∑' k, a_k(r) − (γ + log π)`. -/
theorem archSymbol_eq_tsum (r : ℝ) :
    AEGIS.RHKreinSymbolIntegrationV1.archSymbol r =
      (∑' k, archTerm k r) - (Real.eulerMascheroniConstant + Real.log π) := by
  have hz : 0 < ((1 / 4 : ℂ) + (r : ℂ) * I / 2).re := by simp
  have h := AEGIS.WeilDigammaSeriesHalfPlaneV1.digamma_series_halfPlane_v1 _ hz
  have hsum := (AEGIS.WeilDigammaSeriesRealV1.summable_norm_seriesTerm_v1 _ hz).of_norm
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.re_tsum hsum] at hre
  simp only [seriesTerm_re, Complex.ofReal_re] at hre
  unfold AEGIS.RHKreinSymbolIntegrationV1.archSymbol
  linarith

/-- `½ Im ψ(1/4 + iω/2) = ∑' k, ω/(c_k² + ω²)`. -/
theorem half_im_digamma (ω : ℝ) :
    (Complex.digamma ((1 / 4 : ℂ) + ((ω / 2 : ℝ) : ℂ) * I)).im / 2 =
      ∑' k, ω / (archWidth k ^ 2 + ω ^ 2) := by
  have hz := quarter_re_pos (ω / 2)
  have h := AEGIS.WeilDigammaSeriesHalfPlaneV1.digamma_series_halfPlane_v1 _ hz
  have hsum := (AEGIS.WeilDigammaSeriesRealV1.summable_norm_seriesTerm_v1 _ hz).of_norm
  have him := congrArg Complex.im h
  rw [Complex.add_im, Complex.im_tsum hsum] at him
  simp only [seriesTerm_im, Complex.ofReal_im, add_zero] at him
  rw [him, ← tsum_div_const]
  refine tsum_congr fun k => ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : ((k : ℝ) + 1 / 4) ^ 2 + (ω / 2) ^ 2 ≠ 0 := by positivity
  have h3 : archWidth k ^ 2 + ω ^ 2 ≠ 0 := by have := archWidth_pos k; positivity
  unfold archWidth at h3 ⊢
  field_simp
  ring

theorem summable_inv_width (ω : ℝ) : Summable fun k => 1 / (archWidth k ^ 2 + ω ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by have := archWidth_pos k; positivity)
    (fun k => ?_) (summable_inv_succ_sq.mul_left 4)
  have hc := archWidth_pos k
  have hsq := archWidth_sq_ge k
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ 4 * archWidth k ^ 2 / ((k : ℝ) + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
    _ ≤ 4 * (1 / ((k : ℝ) + 1) ^ 2) * (archWidth k ^ 2 + ω ^ 2) := by
        rw [mul_one_div, div_mul_eq_mul_div]
        gcongr
        nlinarith [sq_nonneg ω]

/-- **CvS archimedean identification at an integer node.** With `ω = 2πn/L`,
`∫ archSymbol(r) S(r, n, L) dr = 2π (½ Im ψ(1/4 + iπn/L) − ω ∑' k, e^{−c_k L}/(c_k² + ω²))`. -/
theorem archSymbol_source_integral {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∫ r, AEGIS.RHKreinSymbolIntegrationV1.archSymbol r * sourceS L r n =
      2 * π * ((Complex.digamma ((1 / 4 : ℂ) + ((π * n / L : ℝ) : ℂ) * I)).im / 2 -
        (2 * π * n / L) * ∑' k, Real.exp (-archWidth k * L) /
          (archWidth k ^ 2 + (2 * π * n / L) ^ 2)) := by
  simp_rw [archSymbol_eq_tsum]
  rw [arch_series_source hL n]
  have hhalf : π * n / L = (2 * π * n / L) / 2 := by ring
  rw [hhalf, half_im_digamma]
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  rw [hω]
  have hs1 := (summable_inv_width ω).mul_left ω
  have hs2 : Summable fun k => Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by have := archWidth_pos k; positivity)
      (fun k => ?_) (summable_inv_width ω)
    have hc := archWidth_pos k
    gcongr
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← tsum_mul_left, ← (hs1.congr fun k => by ring).tsum_sub (hs2.mul_left ω), ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  ring

/-- **CvS diagonal archimedean identification.** With `ω = 2πn/L`,
`∫ archSymbol(r) D(r) dr = 2π archSymbol(ω) + (4π/L) ∑' k, (1 − e^{−c_k L})(c_k² − ω²)/(c_k² + ω²)²`. -/
theorem archSymbol_diag_integral {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∫ r, AEGIS.RHKreinSymbolIntegrationV1.archSymbol r * diagD L r n =
      2 * π * AEGIS.RHKreinSymbolIntegrationV1.archSymbol (2 * π * n / L) +
        4 * π / L * ∑' k, (1 - Real.exp (-archWidth k * L)) *
          (archWidth k ^ 2 - (2 * π * n / L) ^ 2) / (archWidth k ^ 2 + (2 * π * n / L) ^ 2) ^ 2 := by
  simp_rw [archSymbol_eq_tsum]
  exact arch_series_diag hL n _

end AEGIS.CvSArchDigammaV1

#print axioms AEGIS.CvSArchDigammaV1.seriesTerm_re
#print axioms AEGIS.CvSArchDigammaV1.seriesTerm_im
#print axioms AEGIS.CvSArchDigammaV1.archSymbol_eq_tsum
#print axioms AEGIS.CvSArchDigammaV1.half_im_digamma
#print axioms AEGIS.CvSArchDigammaV1.summable_inv_width
#print axioms AEGIS.CvSArchDigammaV1.archSymbol_source_integral
#print axioms AEGIS.CvSArchDigammaV1.archSymbol_diag_integral
