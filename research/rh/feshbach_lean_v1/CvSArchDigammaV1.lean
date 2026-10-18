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
import RHKreinSymbolIntegrationV1

/-!
# The archimedean source values through the repository's `archSymbol` (CvS step 5.2c)

`archSymbol t = Re ψ(1/4 + it/2) − log π` of `RHKreinSymbolIntegrationV1` is `CvSDigammaSeriesV1.hplus`,
so the source values proved there hold for `archSymbol`:

`∫ archSymbol(r) S(r, n, L) dr = 2π (½ Im ψ(1/4 + iπn/L) − ω ∑' k, e^{−c_k L}/(c_k² + ω²))` and
`∫ archSymbol(r) D(r) dr = 2π archSymbol(ω) + (4π/L) ∑' k, (1 − e^{−c_k L})(c_k² − ω²)/(c_k² + ω²)²`.
-/

open MeasureTheory Set Real Complex

noncomputable section

namespace AEGIS.CvSArchDigammaV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1 AEGIS.CvSDigammaSeriesV1

theorem archSymbol_eq_hplus : AEGIS.RHKreinSymbolIntegrationV1.archSymbol = hplus := by
  funext t
  rfl

/-- **CvS archimedean identification at an integer node.** -/
theorem archSymbol_source_integral {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∫ r, AEGIS.RHKreinSymbolIntegrationV1.archSymbol r * sourceS L r n =
      2 * π * ((Complex.digamma ((1 / 4 : ℂ) + ((π * n / L : ℝ) : ℂ) * I)).im / 2 -
        (2 * π * n / L) * ∑' k, Real.exp (-archWidth k * L) /
          (archWidth k ^ 2 + (2 * π * n / L) ^ 2)) := by
  rw [archSymbol_eq_hplus]
  exact hplus_source_integral hL n

/-- **CvS diagonal archimedean identification.** -/
theorem archSymbol_diag_integral {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∫ r, AEGIS.RHKreinSymbolIntegrationV1.archSymbol r * diagD L r n =
      2 * π * AEGIS.RHKreinSymbolIntegrationV1.archSymbol (2 * π * n / L) +
        4 * π / L * ∑' k, (1 - Real.exp (-archWidth k * L)) *
          (archWidth k ^ 2 - (2 * π * n / L) ^ 2) / (archWidth k ^ 2 + (2 * π * n / L) ^ 2) ^ 2 := by
  rw [archSymbol_eq_hplus]
  exact hplus_diag_integral hL n

end AEGIS.CvSArchDigammaV1

#print axioms AEGIS.CvSArchDigammaV1.archSymbol_eq_hplus
#print axioms AEGIS.CvSArchDigammaV1.archSymbol_source_integral
#print axioms AEGIS.CvSArchDigammaV1.archSymbol_diag_integral
