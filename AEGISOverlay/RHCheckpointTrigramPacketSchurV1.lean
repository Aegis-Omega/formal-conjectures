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
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1

/-!
Actual signed Weil trigram checkpoint to genuine PacketSchurFamily.
Preserves the proved width/geometry hypotheses and all genuine zero-side terms.
No added axioms, sorry, admissions, or unconditional RH conclusion.
-/

open Filter Topology
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCheckpointTrigramPacketSchurV1

open AEGIS.RHFeshbachWeilClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2

/-- Scalar Schur family from the proved nonnegative actual Weil zero quadratic
of the very same packet, with no replacement surrogate. -/
def packet_schur_of_zero_nonnegative
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hzero : 0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re) :
    PacketSchurFamily g := by
  let A : ℝ := -(B g g).re
  let E : ℝ := energy g.1
  have hE : 0 ≤ E := energy_nonnegative g.1
  have hrepr : A = (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
    have h :=
      AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
        g hm
    change B g g = -(∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) at h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re] at hre
    dsimp [A]
    linarith
  have hA : 0 ≤ A := by
    rw [hrepr]
    exact hzero
  refine {
    N := fun j => j
    a := fun _ => A
    re_b := fun _ => 0
    q := fun _ => 0
    nv := fun _ => Real.sqrt E
    nw := fun _ => 0
    β := fun _ => 0
    c := fun _ => 1
    μ := fun _ => 0
    normSq := fun _ => E
    normUpper := E
    cofinal := tendsto_id
    reproducesZeroQuadratic := ?_
    eventuallyBounded := Eventually.of_forall (fun _ => le_rfl)
    shiftNonnegative := fun _ => le_rfl
    tailNonnegative := fun _ => le_rfl
    tailCoercivity := ?_
    crossBound := ?_
    betaNonnegative := fun _ => le_rfl
    shiftBelowGap := ?_
    schurLower := ?_
  }
  · simp [hrepr]
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    have he : 0 ≤ FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 j := by
      unfold FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError
      positivity
    have hlower :
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 j) * E ≤ A :=
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) hE).trans hA
    simpa using hlower

/-- Import the genuine trigram margin without introducing any CvS cofinal
approximation hypothesis. Domain 0 ≤ r ≤ 2/5 and HalfWidthAt is retained. -/
def packet_schur_of_trigram_margin
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) :
    PacketSchurFamily g := by
  have hmargin :=
    AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
      g r a hr0 hr hw hm
  have hE : 0 ≤ (1 / 16 : ℝ) * energy g.1 :=
    mul_nonneg (by norm_num) (energy_nonnegative g.1)
  exact packet_schur_of_zero_nonnegative g hm (hE.trans hmargin)

/-- Reuse constant norm-square to provide the explicit convergence witness. -/
theorem trigram_packet_schur_norm_family
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) :
    ∃ f : PacketSchurFamily g,
      ∃ L : ℝ, Tendsto f.normSq atTop (𝓝 L) := by
  refine ⟨packet_schur_of_trigram_margin g hm r a hr0 hr hw, energy g.1, ?_⟩
  change Tendsto (fun _ : ℕ => energy g.1) atTop (𝓝 (energy g.1))
  exact tendsto_const_nhds

end AEGIS.RHCheckpointTrigramPacketSchurV1

#print axioms AEGIS.RHCheckpointTrigramPacketSchurV1.packet_schur_of_zero_nonnegative
#print axioms AEGIS.RHCheckpointTrigramPacketSchurV1.packet_schur_of_trigram_margin
#print axioms AEGIS.RHCheckpointTrigramPacketSchurV1.trigram_packet_schur_norm_family
