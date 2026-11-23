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

import AEGISOverlay.RHActualUniversalFineGramV1
import RestrictedWeilCriterionKernelBridgeV10
import WeilFineDiagonalQuadV1

/-!
AEGIS Ω — the per-packet fine mixed budget does not depend on its constant (Claude Lab, 2026-11-23).

`FineBudget c`: every moment-zero packet has SOME decomposition into moment-zero atoms of log-width 1/128
(`WidthOneOneTwentyEightAt`) with `actualMixedDefect ≤ c · Σ E`.
`StrictWeilSign`: `Re W(g ⋆ g) < 0` for every moment-zero packet with `g ≠ 0`.

* `strictWeilSign_of_fineBudget`: for `c ≤ 43/10`, `FineBudget c → StrictWeilSign`. The diagonal of every atom
  is strictly above `43/10` (`fine_constant_gt`), and `Σ E > 0` for `g ≠ 0`.
* `fineBudget_of_strictWeilSign`: for EVERY real `c`, `StrictWeilSign → FineBudget c`. Replace every atom of the
  operator's decomposition by `K` copies scaled by `1/K`: the Gram total is unchanged, while the diagonal and
  the energies shrink by `1/K`; a large `K` absorbs any constant.
* `fineBudget_iff_strictWeilSign`, `fineBudget_5671_iff_43`: all constants `c ≤ 43/10` give the same condition.
* `operator_per_packet_hcert_of_strictWeilSign`: the hypothesis `hcert` of the operator's
  `riemannHypothesis_of_one_actual_mixed_budget_per_packet` follows from `StrictWeilSign`.
* `riemannHypothesis_of_strictWeilSign`.

Consequence: improving the diagonal constant does not weaken the per-packet budget; its content is exactly the
strict Weil sign. `StrictWeilSign` is NOT proved here, and RH → `StrictWeilSign` is not formalized. Not RH.
-/

open Set Finset Complex MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFineBudgetEquivV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2 AEGIS.WeilMixedClosureV2
open AEGIS.RHGramExpansionV13 AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilLogCoordinateIsometryV21

/-- The per-packet fine mixed budget with constant `c`. -/
def FineBudget (c : ℝ) : Prop :=
  ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤ c * (∑ i, energy (gs i).1)

/-- The strict Weil sign on nonzero moment-zero packets. -/
def StrictWeilSign : Prop :=
  ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g → g.1 ≠ 0 →
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re < 0

/-! ### Elementary facts -/

theorem fine_diag_strict :
    ∃ C : ℝ, 43 / 10 < C ∧ ∀ (g : WeilCompactSmoothGV1) (a : ℝ),
      LogSupportIn g (a - 1 / 256) (a + 1 / 256) → WeilMomentConditionsV1 g →
        C * energy g.1 ≤ -(B g g).re := by
  refine ⟨_, AEGIS.WeilFineDiagonalQuadV1.fine_constant_gt, fun g a hf hm => ?_⟩
  rw [mul_comm]
  exact AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_quad_v1 g a hf hm

theorem energy_pos_of_ne (f : WeilCompactSmoothGV1) (hf : f.1 ≠ 0) : 0 < energy f.1 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hc : Continuous f.1 := f.2.1.continuous
  unfold energy
  have hcs : HasCompactSupport (fun t => ‖f.1 t‖ ^ 2) :=
    f.2.2.1.norm.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    (hc.norm.pow 2) hcs (fun t => by positivity) ?_
  simpa using hx

theorem width_scale (z : ℂ) (p : WeilCompactSmoothGV1) (a : ℝ)
    (hp : AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt p a) :
    AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt (scalePacket z p) a := by
  unfold AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt LogSupportIn at *
  refine subset_trans ?_ hp
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro t ht
  by_contra ha
  apply ht
  have h0 : logLift p.1 t = 0 := image_eq_zero_of_notMem_tsupport ha
  unfold logLift at h0 ⊢
  change (Real.exp (t / 2) : ℂ) * (z * p.1 (Real.exp t)) = 0
  linear_combination z * h0

theorem energy_scale_real (r : ℝ) (p : WeilCompactSmoothGV1) :
    energy (scalePacket (r : ℂ) p).1 = r ^ 2 * energy p.1 := by
  unfold energy
  change (∫ t : ℝ, ‖(r : ℂ) * p.1 t‖ ^ 2) = r ^ 2 * ∫ t : ℝ, ‖p.1 t‖ ^ 2
  have h : ∀ t : ℝ, ‖(r : ℂ) * p.1 t‖ ^ 2 = r ^ 2 * ‖p.1 t‖ ^ 2 := by
    intro t
    rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [h]
  exact integral_const_mul _ _

theorem B_scale_real_re (r : ℝ) (a b : WeilCompactSmoothGV1) :
    (B (scalePacket (r : ℂ) a) (scalePacket (r : ℂ) b)).re = r ^ 2 * (B a b).re := by
  rw [B_scale_left, B_scale_right]
  have hs : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  rw [hs, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem packetSum_one_apply {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) (x : ℝ) :
    (packetSum (fun _ => (1 : ℂ)) gs).1 x = ∑ i, (gs i).1 x := by
  induction n with
  | zero => simp [packetSum, scalePacket]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, ← ih (fun i => gs i.castSucc)]
    simp [packetSum, addPacket, scalePacket]

/-! ### `K`-fold copies -/

/-- `Fin (n+1) × Fin (k+1) ≃ Fin (n (k+1) + k + 1)`. -/
def copyEquiv (n k : ℕ) : Fin (n + 1) × Fin (k + 1) ≃ Fin (n * (k + 1) + k + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- The original atom of a copy. -/
def copyIdx (n k : ℕ) (j : Fin (n * (k + 1) + k + 1)) : Fin (n + 1) :=
  ((copyEquiv n k).symm j).1

/-- `k + 1` copies of every atom, each scaled by `r`. -/
def copyPacket (n k : ℕ) (r : ℝ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (j : Fin (n * (k + 1) + k + 1)) : WeilCompactSmoothGV1 :=
  scalePacket (r : ℂ) (gs (copyIdx n k j))

theorem sum_copy {M : Type*} [AddCommMonoid M] (n k : ℕ) (F : Fin (n + 1) → M) :
    (∑ j, F (copyIdx n k j)) = (k + 1) • ∑ l, F l := by
  rw [← (copyEquiv n k).sum_comp (fun j => F (copyIdx n k j))]
  simp only [copyIdx, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.smul_sum]

theorem sum_copy_real (n k : ℕ) (F : Fin (n + 1) → ℝ) :
    (∑ j, F (copyIdx n k j)) = ((k : ℝ) + 1) * ∑ l, F l := by
  rw [sum_copy, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem sum_copy_complex (n k : ℕ) (F : Fin (n + 1) → ℂ) :
    (∑ j, F (copyIdx n k j)) = ((k : ℂ) + 1) * ∑ l, F l := by
  rw [sum_copy, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem copy_packetSum (n k : ℕ) (r : ℝ) (hrK : r * ((k : ℝ) + 1) = 1)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    packetSum (fun _ => (1 : ℂ)) (copyPacket n k r gs) = packetSum (fun _ => (1 : ℂ)) gs := by
  apply Subtype.ext
  funext x
  rw [packetSum_one_apply, packetSum_one_apply]
  change (∑ j, (r : ℂ) * (gs (copyIdx n k j)).1 x) = _
  rw [← Finset.mul_sum]
  have h : (∑ j, (gs (copyIdx n k j)).1 x) = ((k : ℂ) + 1) * ∑ l, (gs l).1 x :=
    sum_copy_complex n k (fun l => (gs l).1 x)
  have hc : (r : ℂ) * ((k : ℂ) + 1) = 1 := by exact_mod_cast hrK
  rw [h, ← mul_assoc, hc, one_mul]

theorem copy_energy (n k : ℕ) (r : ℝ) (hrK : r * ((k : ℝ) + 1) = 1)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    (∑ j, energy (copyPacket n k r gs j).1) = r * ∑ i, energy (gs i).1 := by
  simp only [copyPacket, energy_scale_real]
  have h : (∑ j, r ^ 2 * energy (gs (copyIdx n k j)).1) =
      ((k : ℝ) + 1) * ∑ l, r ^ 2 * energy (gs l).1 :=
    sum_copy_real n k (fun l => r ^ 2 * energy (gs l).1)
  rw [h, ← Finset.mul_sum]
  have e : ((k : ℝ) + 1) * (r ^ 2 * ∑ i, energy (gs i).1) =
      (r * ((k : ℝ) + 1)) * r * ∑ i, energy (gs i).1 := by ring
  rw [e, hrK, one_mul]

theorem copy_defect (n k : ℕ) (r : ℝ) (hrK : r * ((k : ℝ) + 1) = 1)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect (n * (k + 1) + k) (copyPacket n k r gs) =
      (∑ i, ∑ j, (B (gs i) (gs j)).re) - r * ∑ i, (B (gs i) (gs i)).re := by
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  simp only [Complex.re_sum, copyPacket, B_scale_real_re]
  have hin : ∀ i, (∑ j, r ^ 2 * (B (gs (copyIdx n k i)) (gs (copyIdx n k j))).re) =
      ((k : ℝ) + 1) * ∑ l, r ^ 2 * (B (gs (copyIdx n k i)) (gs l)).re := fun i =>
    sum_copy_real n k (fun l => r ^ 2 * (B (gs (copyIdx n k i)) (gs l)).re)
  simp only [hin]
  have hout : (∑ i, ((k : ℝ) + 1) * ∑ l, r ^ 2 * (B (gs (copyIdx n k i)) (gs l)).re) =
      ((k : ℝ) + 1) * ∑ i, ((k : ℝ) + 1) * ∑ l, r ^ 2 * (B (gs i) (gs l)).re :=
    sum_copy_real n k (fun i => ((k : ℝ) + 1) * ∑ l, r ^ 2 * (B (gs i) (gs l)).re)
  have hdg : (∑ i, r ^ 2 * (B (gs (copyIdx n k i)) (gs (copyIdx n k i))).re) =
      ((k : ℝ) + 1) * ∑ i, r ^ 2 * (B (gs i) (gs i)).re :=
    sum_copy_real n k (fun i => r ^ 2 * (B (gs i) (gs i)).re)
  rw [hout, hdg]
  simp only [← Finset.mul_sum]
  have e1 : ((k : ℝ) + 1) * (((k : ℝ) + 1) * (r ^ 2 * ∑ i, ∑ j, (B (gs i) (gs j)).re)) =
      (r * ((k : ℝ) + 1)) ^ 2 * ∑ i, ∑ j, (B (gs i) (gs j)).re := by ring
  have e2 : ((k : ℝ) + 1) * (r ^ 2 * ∑ i, (B (gs i) (gs i)).re) =
      (r * ((k : ℝ) + 1)) * r * ∑ i, (B (gs i) (gs i)).re := by ring
  rw [e1, e2, hrK]
  ring

/-! ### The equivalence -/

/-- For `c ≤ 43/10` the per-packet budget forces the strict Weil sign. -/
theorem strictWeilSign_of_fineBudget {c : ℝ} (hc : c ≤ 43 / 10) (hb : FineBudget c) :
    StrictWeilSign := by
  intro g hm hg0
  obtain ⟨n, gs, center, hmom, hwidth, hg, hbud⟩ := hb g hm
  obtain ⟨C, hC, hdiag⟩ := fine_diag_strict
  have hs : (∑ i, C * energy (gs i).1) ≤ ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hdiag (gs i) (center i) (hwidth i) (hmom i))
  rw [← Finset.mul_sum, Finset.sum_neg_distrib] at hs
  have hdef : AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
      (∑ i, ∑ j, B (gs i) (gs j)).re - ∑ i, (B (gs i) (gs i)).re := rfl
  have hW : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [hg]
    change (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re = _
    rw [B_packetSum]
    simp
  have hE : ∀ i, 0 ≤ energy (gs i).1 := fun i => energy_nonnegative (gs i).1
  have hSpos : 0 < ∑ i, energy (gs i).1 := by
    by_contra hle
    rw [not_lt] at hle
    have hsum0 : ∑ i, energy (gs i).1 = 0 :=
      le_antisymm hle (Finset.sum_nonneg (fun i _ => hE i))
    have hz : ∀ i, energy (gs i).1 = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hE i)).mp hsum0 i (Finset.mem_univ _)
    apply hg0
    rw [hg]
    funext x
    rw [packetSum_one_apply, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_contra hne
    have hp := energy_pos_of_ne (gs i) (fun h => hne (by rw [h]; rfl))
    linarith [hz i]
  rw [hW]
  have hm2 : 0 < (C - c) * ∑ i, energy (gs i).1 := mul_pos (by linarith) hSpos
  have e : (C - c) * ∑ i, energy (gs i).1 =
      C * ∑ i, energy (gs i).1 - c * ∑ i, energy (gs i).1 := by ring
  linarith

/-- For every real `c`, the strict Weil sign yields the per-packet budget (by `K`-fold copying). -/
theorem fineBudget_of_strictWeilSign (c : ℝ) (hs : StrictWeilSign) : FineBudget c := by
  intro g hm
  by_cases hg0 : g.1 = 0
  · refine ⟨0, fun _ => g, fun _ => 0, fun _ => hm, ?_, ?_, ?_⟩
    · intro i
      show AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt g 0
      unfold AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt LogSupportIn
      have hz : logLift g.1 = 0 := by
        funext t
        simp [logLift, hg0]
      rw [hz, tsupport_zero]
      exact empty_subset _
    · apply Subtype.ext
      funext x
      simp [packetSum, scalePacket]
    · have hE : energy g.1 = 0 := by simp [energy, hg0]
      unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
      simp [hE]
  · obtain ⟨n, gs, center, hmom, _, hwidth, hpacket, hgram⟩ :=
      AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support g hm
    obtain ⟨S, hS⟩ : ∃ S : ℝ, ∑ i, energy (gs i).1 = S := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℝ, ∑ i, (B (gs i) (gs i)).re = D := ⟨_, rfl⟩
    obtain ⟨X, hXd⟩ : ∃ X : ℝ, ∑ i, ∑ j, (B (gs i) (gs j)).re = X := ⟨_, rfl⟩
    have hXneg : X < 0 := by
      have h := hs g hm hg0
      rw [hgram] at h
      simpa only [Complex.re_sum, hXd] using h
    obtain ⟨k, hk⟩ := exists_nat_gt ((c * S + D) / X)
    have hkX : (k : ℝ) * X < c * S + D := (div_lt_iff_of_neg hXneg).mp hk
    have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
    have hrK : r * ((k : ℝ) + 1) = 1 := by rw [hr, one_div, inv_mul_cancel₀ hK.ne']
    have hr0 : 0 < r := by rw [hr]; positivity
    refine ⟨n * (k + 1) + k, copyPacket n k r gs, fun j => center (copyIdx n k j),
      fun j => AEGIS.RestrictedWeilCriterionKernelBridgeV10.scalePacket_preserves_moments_v10 _ _
        (hmom _),
      fun j => width_scale _ _ _ (hwidth _), ?_, ?_⟩
    · rw [copy_packetSum n k r hrK gs]
      exact hpacket
    · rw [copy_defect n k r hrK gs, copy_energy n k r hrK gs, hXd, hD, hS]
      have h1e : ((k : ℝ) + 1) * X = (k : ℝ) * X + X := by ring
      have h1 : ((k : ℝ) + 1) * X < c * S + D := by linarith
      have h2 := mul_lt_mul_of_pos_left h1 hr0
      have e : r * (((k : ℝ) + 1) * X) = X := by rw [← mul_assoc, hrK, one_mul]
      rw [e] at h2
      have e3 : r * (c * S + D) = c * (r * S) + r * D := by ring
      linarith

theorem fineBudget_iff_strictWeilSign {c : ℝ} (hc : c ≤ 43 / 10) :
    FineBudget c ↔ StrictWeilSign :=
  ⟨strictWeilSign_of_fineBudget hc, fineBudget_of_strictWeilSign c⟩

/-- The operator's constant and `43/10` give the same per-packet condition. -/
theorem fineBudget_5671_iff_43 : FineBudget (5671 / 3200) ↔ FineBudget (43 / 10) :=
  (fineBudget_iff_strictWeilSign (by norm_num)).trans
    (fineBudget_iff_strictWeilSign le_rfl).symm

/-- The hypothesis `hcert` of `riemannHypothesis_of_one_actual_mixed_budget_per_packet` follows from the
strict Weil sign. -/
theorem operator_per_packet_hcert_of_strictWeilSign (h : StrictWeilSign) :
    ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
        g = packetSum (fun _ => (1 : ℂ)) gs ∧
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) := by
  intro g hm
  obtain ⟨n, gs, center, _, hwidth, hg, hbud⟩ := fineBudget_of_strictWeilSign (5671 / 3200) h g hm
  exact ⟨n, gs, hg, fun i =>
    AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3 (gs i) (center i) (hwidth i), hbud⟩

theorem riemannHypothesis_of_strictWeilSign (h : StrictWeilSign) : RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  by_cases hg0 : g.1 = 0
  · have hz : g = scalePacket 0 g := by
      apply Subtype.ext
      funext x
      simp [scalePacket, hg0]
    change (B g g).re ≤ 0
    rw [hz, B_scale_left]
    simp
  · exact (h g hm hg0).le

end AEGIS.WeilFineBudgetEquivV1

#print axioms AEGIS.WeilFineBudgetEquivV1.strictWeilSign_of_fineBudget
#print axioms AEGIS.WeilFineBudgetEquivV1.fineBudget_of_strictWeilSign
#print axioms AEGIS.WeilFineBudgetEquivV1.fineBudget_iff_strictWeilSign
#print axioms AEGIS.WeilFineBudgetEquivV1.fineBudget_5671_iff_43
#print axioms AEGIS.WeilFineBudgetEquivV1.operator_per_packet_hcert_of_strictWeilSign
#print axioms AEGIS.WeilFineBudgetEquivV1.riemannHypothesis_of_strictWeilSign
