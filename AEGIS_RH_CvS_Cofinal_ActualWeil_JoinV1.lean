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
/-
AEGIS Ω — source-bound, additive CvS → actual Weil cofinal adapter.

Targets existing PR #89/#90 source identities without changing either PR.
This file is a source candidate; it has NOT been Lean-kernel compiled here.
The universal approximation premise below is mathematical and is NOT supplied
by the finite CvS certificate. No sorry/admit/axioms or RH assumption.
-/
import CvSProjectedEntryReplayL12V1
import CvSProjectedSchurBridgeL12V1
import CvSActualWeilInteropV1
import RHMomentDecayCofinalJoinV1

open Finset Filter Topology
open scoped BigOperators ComplexConjugate
open AEGIS.CvSProjectedEntryL12V1
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSPackedGramV1

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCvSCofinalActualWeilJoinV1

/-!
The import `CvSProjectedEntryReplayL12V1` provides the proved
`Fact (bigCheck = true)` instance, rather than asserting one as a new axiom.
The finite matrix is the source `projectedEntry M`, not an arbitrary PSD matrix.
-/

/-- The kernel-checked packed projected source is nonnegative for every
    certified prime cutoff and every complex source coefficient vector. -/
theorem certified_source_projectedQ_nonneg
    (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    0 ≤ projectedQ M v := by
  have hpacked :=
    AEGIS.CvSProjectedEntryL12V1.projected_lower_L12_of_check
      (M := M) hM v
  have hmargin : (0 : ℝ) ≤ ((certEps - certEta : ℤ) : ℝ) := by
    exact_mod_cast cert_margin_positive.le
  have hnorm : (0 : ℝ) ≤ ∑ i : Fin 139, ‖v i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hscale : (0 : ℝ) < (2 : ℝ) ^ certQ := by positivity
  have hbound : (0 : ℝ) ≤ (2 : ℝ) ^ certQ * projectedQ M v := by
    have hp : (0 : ℝ) ≤
        ((certEps - certEta : ℤ) : ℝ) * ∑ i : Fin 139, ‖v i‖ ^ 2 :=
      mul_nonneg hmargin hnorm
    apply hp.trans
    simpa only [projectedQ] using hpacked
  by_contra hn
  have hnegative : projectedQ M v < 0 := lt_of_not_ge hn
  have hcontra : (2 : ℝ) ^ certQ * projectedQ M v < 0 :=
    mul_neg_of_pos_of_neg hscale hnegative
  exact (not_lt_of_ge hbound) hcontra

/-- If the true zero quadratic of this ONE packet is the certified source
    quadratic, the already-proved actual signed-Weil finite reconstruction
    follows. The exact source-to-packet equality remains an explicit input. -/
theorem actual_signed_budget_of_exact_projectedQ
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ)
    (htransfer :
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
          projectedQ M v) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = AEGIS.RHGramExpansionV13.packetSum (fun _ => (1 : ℂ)) gs ∧
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, (AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re) := by
  have hzero : 0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
    rw [htransfer]
    exact certified_source_projectedQ_nonneg M hM v
  exact AEGIS.RHCvSActualWeilInteropV1.actual_signed_budget_of_zero_side
    g hm hzero

/-- Source-anchored COFINAL approximation, rather than a assumed zero sign:
    each source zero quadratic is the limit of true 139×139 projected CvS
    forms at prime cutoffs tending to infinity. The only unproved input is
    this same-object approximation/convergence. -/
def UniversalActualCvSCofinalApproximation : Prop :=
  ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
    ∃ (M : ℕ → ℕ) (v : ℕ → Fin 139 → ℂ),
      (∀ j, 3 ≤ M j) ∧
      Tendsto M atTop atTop ∧
      Tendsto (fun j => projectedQ (M j) (v j)) atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re))

/-- Already-proved cofinal limit lemma transfers each certified source sign
    to the canonical zero quadratic of the SAME g, if the actual limit holds. -/
theorem zero_quadratic_nonneg_of_projected_cofinal
    (g : WeilCompactSmoothGV1)
    (M : ℕ → ℕ) (v : ℕ → Fin 139 → ℂ)
    (hM : ∀ j, 3 ≤ M j)
    (hcofinal : Tendsto M atTop atTop)
    (hreproduce : Tendsto (fun j => projectedQ (M j) (v j)) atTop
      (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re))) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact AEGIS.RHMomentDecayCofinalJoinV1.actual_zero_quadratic_nonnegative_of_cofinal_lower_bound
    g (N := M) (q := fun j => projectedQ (M j) (v j))
    (normSq := fun _ => (0 : ℝ)) (normSqLimit := 0)
    hcofinal hreproduce tendsto_const_nhds
    (by
      intro j
      simpa using certified_source_projectedQ_nonneg (M j) (hM j) (v j))

/-- Final canonical RH consumer: NO `hzero` premise, NO assumption of RH,
    NO arbitrary positive matrix substituted for the true CvS source.
    The strictly stronger, source-specific universal convergence hypothesis
    is visible rather than claimed proved. -/
theorem riemannHypothesis_of_universal_actual_cvs_cofinal
    (happrox : UniversalActualCvSCofinalApproximation) :
    RiemannHypothesis := by
  apply
    (AEGIS.RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget).2
  intro g hm
  obtain ⟨M, v, hM, hcofinal, hreproduce⟩ := happrox g hm
  exact AEGIS.RHCvSActualWeilInteropV1.actual_signed_budget_of_zero_side
    g hm (zero_quadratic_nonneg_of_projected_cofinal
      g M v hM hcofinal hreproduce)


/-- Any genuine lower bound on the zero quadratic of this SAME moment-zero
packet gives a quantitative upper bound on its exact reconstructed finite
Weil Gram diagonal plus mixed defect. A historical Krein energy margin may
be supplied as `hmargin` once its separate source theorem has been replayed;
no historical import or global approximation is assumed here. -/
theorem actual_quantitative_signed_budget_of_zero_margin
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (margin : ℝ)
    (hmargin : margin ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = AEGIS.RHGramExpansionV13.packetSum (fun _ => (1 : ℂ)) gs ∧
      (AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs +
        ∑ i, (AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re) ≤ -margin := by
  obtain ⟨n, gs, hpacket, hidentity⟩ :=
    AEGIS.RHCvSActualWeilInteropV1.actual_fine_mixed_defect_eq_neg_zero_side
      g hm
  refine ⟨n, gs, hpacket, ?_⟩
  calc
    _ = -(∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := hidentity
    _ ≤ -margin := neg_le_neg hmargin


/-- The already checked adaptive Krein/trigram certificate yields the exact
energy/16 margin for any moment-zero packet in its width-2/5 domain. Transfer
that genuine source bound through the finite actual-Weil Gram identity. No
historical batch files, cofinal convergence, or RH premise are introduced. -/
theorem actual_quantitative_signed_budget_of_trigram_margin
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = AEGIS.RHGramExpansionV13.packetSum (fun _ => (1 : ℂ)) gs ∧
      (AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs +
        ∑ i, (AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re) ≤
          -((1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1) := by
  exact actual_quantitative_signed_budget_of_zero_margin g hm
    ((1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1)
    (AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
      g r a hr0 hr hw hm)

end AEGIS.RHCvSCofinalActualWeilJoinV1

#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.certified_source_projectedQ_nonneg
#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.actual_signed_budget_of_exact_projectedQ
#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.zero_quadratic_nonneg_of_projected_cofinal
#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.riemannHypothesis_of_universal_actual_cvs_cofinal
#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.actual_quantitative_signed_budget_of_zero_margin
#print axioms AEGIS.RHCvSCofinalActualWeilJoinV1.actual_quantitative_signed_budget_of_trigram_margin
