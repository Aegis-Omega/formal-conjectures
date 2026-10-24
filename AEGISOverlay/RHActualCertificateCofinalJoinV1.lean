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

import AEGISOverlay.AEGIS_RH_Unconditional
import AEGISOverlay.RHCheckpointTrigramPacketSchurV1
import AEGISOverlay.RHActualUniversalFineGramV1
import RHCofinalSchurAdapterV1

/-!
# Direct exact-object Schur-to-cofinal joins from checked RH checkpoints

The same original Weil packet and the same actual zero quadratic are retained.
The existing Schur producer is passed directly to the existing cofinal adapter.
The finite Gram variant retains its *actual signed mixed budget* as an explicit
premise. No global sign, universally quantified producer or RH conclusion is
asserted or imported by an invented axiom.
-/

open Filter Topology
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualCertificateCofinalJoinV1

open AEGIS.RHFeshbachWeilClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- The *existing* 693/2000 packet Schur constructor feeds the *existing*
cofinal terminal without rebuilding either proof. -/
theorem narrow_window_actual_cofinal_certificate
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000)) :
    ∃ (N : ℕ → ℕ) (q normSq : ℕ → ℝ) (limit : ℝ),
      Tendsto N atTop atTop ∧
      Tendsto q atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)) ∧
      Tendsto normSq atTop (𝓝 limit) ∧
      (∀ j : ℕ,
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ q j) := by
  obtain ⟨f, L, hnorm⟩ :=
    AEGIS.RHAssemblyV1.narrow_window_schur_norm_family g hm hw
  exact AEGIS.RHCofinalSchurAdapterV1.cofinal_certificate_of_packet_schur
    g f L hnorm

/-- The stronger source-checked radius-2/5 Trigram margin also feeds the
cofinal adapter, with its true window hypothesis preserved. -/
theorem trigram_actual_cofinal_certificate
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) :
    ∃ (N : ℕ → ℕ) (q normSq : ℕ → ℝ) (limit : ℝ),
      Tendsto N atTop atTop ∧
      Tendsto q atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)) ∧
      Tendsto normSq atTop (𝓝 limit) ∧
      (∀ j : ℕ,
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ q j) := by
  obtain ⟨f, L, hnorm⟩ :=
    AEGIS.RHCheckpointTrigramPacketSchurV1.trigram_packet_schur_norm_family
      g hm r a hr0 hr hw
  exact AEGIS.RHCofinalSchurAdapterV1.cofinal_certificate_of_packet_schur
    g f L hnorm

/-- An independently checked *genuine finite mixed Gram* certificate
constructs the SAME original packet's Schur family; the mixed B terms cannot
be dropped or replaced by diagonals. -/
def packet_schur_of_paid_actual_mixed_gram
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hg : g = packetSum (fun _ => (1 : ℂ)) gs)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hbudget : AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)) :
    PacketSchurFamily g := by
  have hsign : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
    change (B g g).re ≤ 0
    rw [hg]
    exact AEGIS.RHActualUniversalFineGramV1.actual_sign_of_one_fine_mixed_budget
      gs hd hbudget
  have hzero :=
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      g hm).mp hsign
  exact AEGIS.RHCheckpointTrigramPacketSchurV1.packet_schur_of_zero_nonnegative
    g hm hzero

end AEGIS.RHActualCertificateCofinalJoinV1

#print axioms AEGIS.RHActualCertificateCofinalJoinV1.narrow_window_actual_cofinal_certificate
#print axioms AEGIS.RHActualCertificateCofinalJoinV1.trigram_actual_cofinal_certificate
#print axioms AEGIS.RHActualCertificateCofinalJoinV1.packet_schur_of_paid_actual_mixed_gram
