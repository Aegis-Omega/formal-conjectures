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

import AEGISOverlay.RHTargetPacketMellinGeneralV2
import AEGISOverlay.RHCompactMellinEntireV1
import AEGISOverlay.RHDetectingPacketV1
import AEGISOverlay.RHGenericSpectralShiftV1
import RestrictedWeilCriterionResidueCoefficientV11
import WeilZeroTwoPointV11

/-!
# One fixed *narrow* detecting packet

The source-exact TargetPacketV11 family has moments zero and x-support
within exp(±1/32) for every complex parameter. The already kernel-replayed
general Mellin identity, entire-Mellin lemma, generic real shift, and the
countable bad-ratio argument yield a single narrow packet whose zero-kernel
coefficients detect every nontrivial zeta zero.

This proves no global translated sign, kernel bound, or RH statement.
-/

set_option autoImplicit false
noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace AEGIS.RHNarrowFixedDetectorV1

open AEGIS.RestrictedWeilCriterionResidueWitnessV11
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RHTargetPacketMellinGeneralV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10

private def narrowWindow : Set ℝ :=
  Icc (Real.exp (-(1 / 32 : ℝ))) (Real.exp (1 / 32 : ℝ))

private theorem targetPacket_narrowWindow (alpha : ℂ) :
    tsupport (TargetPacketV11 alpha).1 ⊆ narrowWindow := by
  simpa only [narrowWindow, TargetPacketV11] using
    targetPacketFun_tsupport_subset_v11 alpha

/-- Two explicitly parametrized target packets have no common Mellin zero
in the critical strip; the parameter choice does not enlarge support. -/
theorem exists_narrow_complementary_pair :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      tsupport p.1 ⊆ narrowWindow ∧
      tsupport q.1 ⊆ narrowWindow ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        ¬ (mellin p.1 s = 0 ∧ mellin q.1 s = 0) := by
  let p := TargetPacketV11 (2 : ℂ)
  have hpNonzero : mellin p.1 (2 : ℂ) ≠ 0 := by
    simpa only [p] using targetPacket_mellin_target_ne_zero_v11
      (2 : ℂ) (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ :=
    AEGIS.RHGenericSpectralShiftV1.exists_real_shift_no_common_zero_of_entire
      (mellin p.1) (AEGIS.RHCompactMellinEntireV1.packet_mellin_entire p)
      (2 : ℂ) hpNonzero
  let q := TargetPacketV11 (2 - (a : ℂ))
  refine ⟨p, q, targetPacket_moments_v11 _, targetPacket_moments_v11 _,
    targetPacket_narrowWindow _, targetPacket_narrowWindow _, ?_⟩
  intro s hslo hshi ⟨hpzero, hqzero⟩
  apply ha s
  refine ⟨hpzero, ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hr : s.re = 1 := by simpa using congrArg Complex.re h
    linarith
  have hQformula :
      mellin q.1 s =
        s * (s - 1) * seedMellinV2 (s - (2 - (a : ℂ))) := by
    simpa only [q] using targetPacket_mellin_general_v2 (2 - (a : ℂ)) s
  rw [hQformula] at hqzero
  have hprod :
      (s * (s - 1)) * seedMellinV2 (s - (2 - (a : ℂ))) = 0 := by
    simpa only [mul_assoc] using hqzero
  have hseed : seedMellinV2 (s - (2 - (a : ℂ))) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  change mellin (TargetPacketV11 (2 : ℂ)).1 (s + (a : ℂ)) = 0
  rw [targetPacket_mellin_general_v2]
  have harg : (s + (a : ℂ)) - 2 = s - (2 - (a : ℂ)) := by ring
  rw [harg, hseed]
  simp

/-- Exact support control survives the countable bad-ratio linear combination. -/
theorem exists_narrow_mellin_detecting_packet :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      tsupport g.1 ⊆ narrowWindow ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        mellin g.1 rho.1 ≠ 0 ∧
        mellin g.1 (1 - conj rho.1) ≠ 0 := by
  obtain ⟨p, q, hp, hq, hpsupp, hqsupp, hpair⟩ :=
    exists_narrow_complementary_pair
  let bad₁ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 rho.1 / mellin q.1 rho.1).re)
  let bad₂ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 (1 - conj rho.1) /
      mellin q.1 (1 - conj rho.1)).re)
  have hc₁ : bad₁.Countable := Set.countable_range _
  have hc₂ : bad₂.Countable := Set.countable_range _
  have hex : ∃ b : ℝ, b ∉ bad₁ ∪ bad₂ := by
    by_contra h
    push Not at h
    have heq : bad₁ ∪ bad₂ = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hc₁.union hc₂)
  obtain ⟨b, hb⟩ := hex
  let g := addPacket p (scalePacket (b : ℂ) q)
  have hmoment : WeilMomentConditionsV1 g :=
    addPacket_preserves_moments_v10 p (scalePacket (b : ℂ) q) hp
      (scalePacket_preserves_moments_v10 (b : ℂ) q hq)
  have hsupport : tsupport g.1 ⊆ narrowWindow := by
    intro x hx
    change x ∈ tsupport (addPacket p (scalePacket (b : ℂ) q)).1 at hx
    rcases sum_support p (scalePacket (b : ℂ) q) hx with hx | hx
    · exact hpsupp hx
    · exact hqsupp (scale_support (b : ℂ) q hx)
  refine ⟨g, hmoment, hsupport, ?_⟩
  intro rho
  have hstrip := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hs₀ : 0 < (1 - conj rho.1).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.2]
  have hs₁ : (1 - conj rho.1).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.1]
  have hr₁ : b ≠ (-mellin p.1 rho.1 / mellin q.1 rho.1).re := by
    intro heq
    exact hb (Or.inl ⟨rho, heq.symm⟩)
  have hr₂ : b ≠
      (-mellin p.1 (1 - conj rho.1) / mellin q.1 (1 - conj rho.1)).re := by
    intro heq
    exact hb (Or.inr ⟨rho, heq.symm⟩)
  change mellin (addPacket p (scalePacket (b : ℂ) q)).1 rho.1 ≠ 0 ∧
    mellin (addPacket p (scalePacket (b : ℂ) q)).1
      (1 - conj rho.1) ≠ 0
  rw [mellin_addPacket_v11, mellin_scalePacket_v11,
    mellin_addPacket_v11, mellin_scalePacket_v11]
  constructor
  · exact AEGIS.RHDetectingPacketV1.affine_ne_zero_of_ratio_excluded _ _ b
      (hpair rho.1 hstrip.1 hstrip.2) hr₁
  · exact AEGIS.RHDetectingPacketV1.affine_ne_zero_of_ratio_excluded _ _ b
      (hpair (1 - conj rho.1) hs₀ hs₁) hr₂

/-- A single genuinely narrow compact smooth packet detects every actual
nontrivial-zero translation coefficient. -/
theorem exists_narrow_fixed_detecting_packet :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      tsupport g.1 ⊆ narrowWindow ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        WeilZeroCoefficientV11 g rho ≠ 0 := by
  obtain ⟨g, hm, hsupp, hmel⟩ := exists_narrow_mellin_detecting_packet
  refine ⟨g, hm, hsupp, fun rho => ?_⟩
  unfold WeilZeroCoefficientV11
  rw [autocorrelation_zero_summand_factorization_v11]
  have hmult : (analyticOrderNatAt riemannZeta rho.1 : ℂ) ≠ 0 := by
    exact_mod_cast zeta_analyticOrderNatAt_ne_zero_v11 rho
  exact mul_ne_zero hmult
    (mul_ne_zero (hmel rho).1 ((map_ne_zero conj).mpr (hmel rho).2))

end AEGIS.RHNarrowFixedDetectorV1

#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_complementary_pair
#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_mellin_detecting_packet
#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_fixed_detecting_packet
