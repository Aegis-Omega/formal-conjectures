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
import AEGISOverlay.RHFiniteActualGramJoinV1

/-!
# The mixed budget certificate only sees the sign of the packet

`riemannHypothesis_of_one_actual_mixed_budget_per_packet` asks, for every moment-zero packet `g`,
for one decomposition `g = ∑ gs i` into atoms with the diagonal margin `m = 5671/3200` whose mixed
defect is at most `m ∑ E(gs i)`. `MixedBudgetCertificate m g` is that condition for any `m`.

The decomposition is a history and `g` is its outcome. Refining every atom into `N` copies of
itself scaled by `1/N` keeps the outcome and the margins, keeps `Re B(g,g)`, and divides the
excess `∑ (−Re B(gs i, gs i) − m E(gs i))` by `N`. Hence, for every `m`:

* `certificate_of_strict_sign`: a margin-`m` decomposition and `Re B(g,g) < 0` give a certificate;
* `sign_of_certificate`: a certificate gives `Re B(g,g) ≤ 0`.

So a certificate holds exactly when the Weil sign of `g` does, up to the boundary
`Re B(g,g) = 0`, whatever decomposition is used and whatever the margin constant is.
`consumer_hypothesis_of_strict_sign` and `weak_sign_of_consumer_hypothesis` state this for the
hypothesis of the consumer theorem. Nothing here proves RH.
-/

open Finset Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace AEGIS.RHMixedBudgetRefinementV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2 AEGIS.RHGramExpansionV13
open AEGIS.RHActualMixedDefectV1

/-- One decomposition of `g` with margin `m` whose mixed defect is paid by `m` times the energy.
For `m = 5671/3200` this is the body of the consumer hypothesis. -/
def MixedBudgetCertificate (m : ℝ) (g : WeilCompactSmoothGV1) : Prop :=
  ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
    g = packetSum (fun _ => (1 : ℂ)) gs ∧
    (∀ i, m * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
    actualMixedDefect n gs ≤ m * ∑ i, energy (gs i).1

theorem energy_scale_real (r : ℝ) (a : WeilCompactSmoothGV1) :
    energy (scalePacket (r : ℂ) a).1 = r ^ 2 * energy a.1 := by
  unfold energy
  change ∫ t, ‖(r : ℂ) * a.1 t‖ ^ 2 = r ^ 2 * ∫ t, ‖a.1 t‖ ^ 2
  simp_rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact integral_const_mul _ _

theorem B_scale_real (r : ℝ) (a b : WeilCompactSmoothGV1) :
    (B (scalePacket (r : ℂ) a) (scalePacket (r : ℂ) b)).re = r ^ 2 * (B a b).re := by
  rw [B_scale_left, B_scale_right]
  have : (r : ℂ) * (star (r : ℂ) * B a b) = ((r ^ 2 : ℝ) : ℂ) * B a b := by
    rw [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul]

/-- Index of the refinement: `N = r + 1` copies of each of the `n + 1` atoms. -/
def refineIndex (n r : ℕ) : Fin (n * (r + 1) + r + 1) ≃ Fin (n + 1) × Fin (r + 1) :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- Every atom replaced by `r + 1` copies of itself scaled by `1 / (r + 1)`. -/
def refine (n r : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    Fin (n * (r + 1) + r + 1) → WeilCompactSmoothGV1 :=
  fun k => scalePacket (((1 : ℝ) / (r + 1) : ℝ) : ℂ) (gs (refineIndex n r k).1)

theorem sum_refine {M : Type*} [AddCommMonoid M] (n r : ℕ) (f : Fin (n + 1) → M) :
    ∑ k, f (refineIndex n r k).1 = (r + 1) • ∑ i, f i := by
  rw [Fintype.sum_equiv (refineIndex n r) (fun k => f (refineIndex n r k).1) (fun p => f p.1)
    (fun _ => rfl), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.smul_sum]

theorem refine_packet (n r : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    packetSum (fun _ => (1 : ℂ)) (refine n r gs) = packetSum (fun _ => (1 : ℂ)) gs := by
  apply Subtype.ext
  rw [AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply,
    AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply]
  funext x
  change ∑ k, (((1 : ℝ) / (r + 1) : ℝ) : ℂ) * (gs (refineIndex n r k).1).1 x = ∑ i, (gs i).1 x
  rw [sum_refine n r (fun i => (((1 : ℝ) / (r + 1) : ℝ) : ℂ) * (gs i).1 x), ← Finset.mul_sum,
    nsmul_eq_mul, ← mul_assoc]
  have : ((r + 1 : ℕ) : ℂ) * (((1 : ℝ) / (r + 1) : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [this, one_mul]

theorem refine_margin (m : ℝ) (n r : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hdiag : ∀ i, m * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) (k : Fin (n * (r + 1) + r + 1)) :
    m * energy (refine n r gs k).1 ≤ -(B (refine n r gs k) (refine n r gs k)).re := by
  simp only [refine]
  rw [energy_scale_real, B_scale_real]
  have h := hdiag (refineIndex n r k).1
  have hc : 0 ≤ ((1 : ℝ) / (r + 1)) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h hc]

theorem refine_diag_sum (n r : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    ∑ k, (B (refine n r gs k) (refine n r gs k)).re =
      (1 / (r + 1 : ℝ)) * ∑ i, (B (gs i) (gs i)).re := by
  simp only [refine, B_scale_real]
  rw [sum_refine n r (fun i => ((1 : ℝ) / (r + 1)) ^ 2 * (B (gs i) (gs i)).re), ← Finset.mul_sum,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem refine_energy_sum (n r : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    ∑ k, energy (refine n r gs k).1 = (1 / (r + 1 : ℝ)) * ∑ i, energy (gs i).1 := by
  simp only [refine, energy_scale_real]
  rw [sum_refine n r (fun i => ((1 : ℝ) / (r + 1)) ^ 2 * energy (gs i).1), ← Finset.mul_sum,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem packet_gram (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    (∑ i, ∑ j, B (gs i) (gs j)) =
      B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs) := by
  rw [B_packetSum]
  simp

/-- **Refinement.** A margin-`m` decomposition of a packet with strictly negative Weil sign
refines to a certificate, for every margin constant `m`. -/
theorem certificate_of_strict_sign (m : ℝ) (g : WeilCompactSmoothGV1) (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (hpacket : g = packetSum (fun _ => (1 : ℂ)) gs)
    (hdiag : ∀ i, m * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) (hneg : (B g g).re < 0) :
    MixedBudgetCertificate m g := by
  set q := -(B g g).re with hq
  set D := -(∑ i, (B (gs i) (gs i)).re) - m * ∑ i, energy (gs i).1 with hD
  have hqpos : 0 < q := by linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (D / q)
  have hrD : D < (r + 1 : ℝ) * q := by
    have := (div_lt_iff₀ hqpos).mp hr
    nlinarith
  refine ⟨n * (r + 1) + r, refine n r gs, ?_, refine_margin m n r gs hdiag, ?_⟩
  · rw [refine_packet]
    exact hpacket
  · unfold actualMixedDefect
    rw [packet_gram, refine_packet, ← hpacket, refine_diag_sum, refine_energy_sum]
    have hc : 0 < (1 / (r + 1 : ℝ)) := by positivity
    have key : (B g g).re - 1 / (r + 1 : ℝ) * ∑ i, (B (gs i) (gs i)).re -
        m * (1 / (r + 1 : ℝ) * ∑ i, energy (gs i).1) =
        -(1 / (r + 1 : ℝ) * ((r + 1 : ℝ) * q - D)) := by
      rw [hq, hD]
      field_simp
      ring
    have hpos : 0 < 1 / (r + 1 : ℝ) * ((r + 1 : ℝ) * q - D) := mul_pos hc (by linarith)
    linarith

/-- A certificate forces the (weak) Weil sign of the packet. -/
theorem sign_of_certificate (m : ℝ) (g : WeilCompactSmoothGV1)
    (h : MixedBudgetCertificate m g) : (B g g).re ≤ 0 := by
  obtain ⟨n, gs, hpacket, hdiag, hbudget⟩ := h
  have hsum : m * ∑ i, energy (gs i).1 ≤ -∑ i, (B (gs i) (gs i)).re := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => hdiag i)
  unfold actualMixedDefect at hbudget
  rw [packet_gram, ← hpacket] at hbudget
  linarith

theorem certificate_of_zero (m : ℝ) (g : WeilCompactSmoothGV1) (h0 : ∀ x, g.1 x = 0) :
    MixedBudgetCertificate m g := by
  have hg : g = scalePacket 0 g := Subtype.ext (funext fun x => by simp [scalePacket, h0 x])
  have hB : B g g = 0 := by
    conv_lhs => rw [hg]
    rw [B_scale_left, zero_mul]
  have hE : energy g.1 = 0 := by simp [energy, h0]
  refine ⟨0, ![g], ?_, ?_, ?_⟩
  · exact Subtype.ext (funext fun x => by simp [packetSum, scalePacket])
  · intro i
    fin_cases i
    simp [hB, hE]
  · simp [actualMixedDefect, hE]

/-- The strict Weil sign for every nonzero moment-zero packet gives the consumer hypothesis. -/
theorem consumer_hypothesis_of_strict_sign
    (hstrict : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g → (∃ x, g.1 x ≠ 0) →
      (B g g).re < 0) :
    ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      MixedBudgetCertificate (5671 / 3200) g := by
  intro g hm
  by_cases hz : ∃ x, g.1 x ≠ 0
  · obtain ⟨n, gs, _hmom, hdiag, hpacket, _hgram⟩ :=
      AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram g hm
    exact certificate_of_strict_sign _ g n gs hpacket hdiag (hstrict g hm hz)
  · simp only [not_exists, not_not] at hz
    exact certificate_of_zero _ g hz

/-- The consumer hypothesis gives the weak Weil sign for every moment-zero packet. -/
theorem weak_sign_of_consumer_hypothesis
    (hcert : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      MixedBudgetCertificate (5671 / 3200) g) :
    ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g → (B g g).re ≤ 0 :=
  fun g hm => sign_of_certificate _ g (hcert g hm)

/-- `MixedBudgetCertificate (5671/3200)` is literally the consumer's per-packet hypothesis. -/
theorem consumer_of_certificates
    (hcert : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      MixedBudgetCertificate (5671 / 3200) g) : RiemannHypothesis :=
  AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_one_actual_mixed_budget_per_packet hcert

end AEGIS.RHMixedBudgetRefinementV1

#print axioms AEGIS.RHMixedBudgetRefinementV1.refine_packet
#print axioms AEGIS.RHMixedBudgetRefinementV1.certificate_of_strict_sign
#print axioms AEGIS.RHMixedBudgetRefinementV1.sign_of_certificate
#print axioms AEGIS.RHMixedBudgetRefinementV1.consumer_hypothesis_of_strict_sign
#print axioms AEGIS.RHMixedBudgetRefinementV1.weak_sign_of_consumer_hypothesis
#print axioms AEGIS.RHMixedBudgetRefinementV1.consumer_of_certificates
