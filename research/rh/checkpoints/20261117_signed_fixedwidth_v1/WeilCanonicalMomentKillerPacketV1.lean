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

import WeilLogTransportCanonicalV1
import WeilThreeBlockTranslatedPacketsV22

/-!
Canonical AEGIS moment-killer packet transport.

This is a SOURCE composition of existing
  WeilLogTransportCanonicalV1 (guarded log change of variables),
  WeilMomentKillerConstructionV1 (two killed moments), and
  WeilThreeBlockTranslatedPacketsV22 (actual support width).

Unlike the legacy gWitness, every packet here has the ROOT canonical
WeilCompactSmoothGV1 type from WeilCriterionCompactSmoothV1.

No analytic signed prime estimate, new axiom, global Weil sign or RH.
-/

open MeasureTheory Set Complex
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCanonicalMomentKillerPacketV1

open AEGIS.WeilLogTransportCanonicalV1
open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22

/-- Convert a real smooth compact log packet into the ROOT canonical
positive-axis Weil test class using the already-proved transport. -/
def canonicalPacket (φ : ℝ → ℝ) (lo hi : ℝ)
    (hs : ContDiff ℝ ∞ φ)
    (hl : ∀ t, t ≤ lo → φ t = 0)
    (hr : ∀ t, hi ≤ t → φ t = 0) : WeilCompactSmoothGV1 := by
  let f : ℝ → ℂ := fun x => ((mulPacket φ x : ℝ) : ℂ)
  have hfs : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp (mulPacket_contDiff hs hl)
  have hsupport : Function.support f = Function.support (mulPacket φ) := by
    ext x
    simp [f, Function.mem_support, Complex.ofReal_eq_zero]
  have hfc : HasCompactSupport f := by
    rw [HasCompactSupport, tsupport, hsupport, ← tsupport]
    exact mulPacket_hasCompactSupport hl hr
  have hfpos : tsupport f ⊆ Set.Ioi 0 := by
    rw [tsupport, hsupport, ← tsupport]
    refine (tsupport_mulPacket_subset hl hr).trans ?_
    intro x hx
    exact lt_of_lt_of_le (Real.exp_pos _) hx.1
  exact ⟨f, hfs, hfc, hfpos⟩

/-- The canonical packet's logarithmic lift is exactly the real log seed
with the true e^(t/2) isometric weight, not a substitute correlation. -/
theorem canonicalPacket_logLift (φ : ℝ → ℝ) (lo hi : ℝ)
    (hs : ContDiff ℝ ∞ φ)
    (hl : ∀ t, t ≤ lo → φ t = 0)
    (hr : ∀ t, hi ≤ t → φ t = 0) (t : ℝ) :
    logLift (canonicalPacket φ lo hi hs hl hr).1 t =
      (Real.exp (t / 2) : ℂ) * (φ t : ℂ) := by
  change (Real.exp (t / 2) : ℂ) *
    ((mulPacket φ (Real.exp t) : ℝ) : ℂ) = _
  rw [mulPacket_of_pos (Real.exp_pos t), Real.log_exp]

/-- Both canonical Weil moments vanish when the log moments vanish.
Everything is the original Bochner integral and canonical domain. -/
theorem canonicalPacket_moments
    (φ : ℝ → ℝ) (lo hi : ℝ)
    (hs : ContDiff ℝ ∞ φ)
    (hl : ∀ t, t ≤ lo → φ t = 0)
    (hr : ∀ t, hi ≤ t → φ t = 0)
    (h0 : (∫ t : ℝ, φ t) = 0)
    (h1 : (∫ t : ℝ, φ t * Real.exp t) = 0) :
    WeilMomentConditionsV1 (canonicalPacket φ lo hi hs hl hr) := by
  constructor
  · have hreal : (∫ x in Ioi (0 : ℝ), x⁻¹ * mulPacket φ x) = 0 := by
      rw [integral_mulPacket_inv hs.continuous hl hr]
      exact h0
    have hcomplex :
        (∫ x in Ioi (0 : ℝ),
          (canonicalPacket φ lo hi hs hl hr).1 x / (x : ℂ)) =
          ((∫ x in Ioi (0 : ℝ), x⁻¹ * mulPacket φ x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      change ((mulPacket φ x : ℝ) : ℂ) / (x : ℂ) =
        ((x⁻¹ * mulPacket φ x : ℝ) : ℂ)
      rw [Complex.ofReal_mul, Complex.ofReal_inv]
      field_simp
    rw [hcomplex, hreal, Complex.ofReal_zero]
  · have hreal : (∫ x in Ioi (0 : ℝ), mulPacket φ x) = 0 := by
      rw [integral_mulPacket hs.continuous hl hr]
      exact h1
    have hcomplex :
        (∫ x in Ioi (0 : ℝ),
          (canonicalPacket φ lo hi hs hl hr).1 x) =
          ((∫ x in Ioi (0 : ℝ), mulPacket φ x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      rfl
    rw [hcomplex, hreal, Complex.ofReal_zero]

/-- Real support control transfers to the actual V22 log-lift support. -/
theorem canonicalPacket_logSupportIn
    (φ : ℝ → ℝ) (lo hi : ℝ)
    (hs : ContDiff ℝ ∞ φ)
    (hl : ∀ t, t ≤ lo → φ t = 0)
    (hr : ∀ t, hi ≤ t → φ t = 0) :
    LogSupportIn (canonicalPacket φ lo hi hs hl hr) lo hi := by
  unfold LogSupportIn
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra hnot
  have hout : t < lo ∨ hi < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hnot
  have hzero : logLift (canonicalPacket φ lo hi hs hl hr).1 t = 0 := by
    rw [canonicalPacket_logLift]
    rcases hout with h | h
    · rw [hl t h.le]
      simp
    · rw [hr t h.le]
      simp
  exact ht hzero

/-- A moment-killed potential yields a ROOT canonical two-moment packet.
No duplicate domain definitions or imported legacy gWitness. -/
theorem canonicalMomentKiller_moments
    (ψ : ℝ → ℝ) (lo hi : ℝ)
    (hs : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hl : ∀ t, t ≤ lo → momentKiller ψ t = 0)
    (hr : ∀ t, hi ≤ t → momentKiller ψ t = 0) :
    WeilMomentConditionsV1
      (canonicalPacket (momentKiller ψ) lo hi
        (momentKiller_contDiff hs) hl hr) :=
  canonicalPacket_moments (momentKiller ψ) lo hi
    (momentKiller_contDiff hs) hl hr
    (integral_momentKiller hs hc)
    (integral_momentKiller_mul_exp hs hc)

/-- Width 1/32 is an actual total support width, namely half-width 1/64. -/
theorem canonicalMomentKiller_width
    (ψ : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ ψ)
    (hl : ∀ t, t ≤ -(1 / 64 : ℝ) → momentKiller ψ t = 0)
    (hr : ∀ t, (1 / 64 : ℝ) ≤ t → momentKiller ψ t = 0) :
    WidthOneThirtyTwoAt
      (canonicalPacket (momentKiller ψ) (-(1 / 64)) (1 / 64)
        (momentKiller_contDiff hs) hl hr) 0 := by
  simpa [WidthOneThirtyTwoAt] using
    (canonicalPacket_logSupportIn (momentKiller ψ) (-(1 / 64)) (1 / 64)
      (momentKiller_contDiff hs) hl hr)

end AEGIS.WeilCanonicalMomentKillerPacketV1

#print axioms AEGIS.WeilCanonicalMomentKillerPacketV1.canonicalPacket_moments
#print axioms AEGIS.WeilCanonicalMomentKillerPacketV1.canonicalPacket_logSupportIn
#print axioms AEGIS.WeilCanonicalMomentKillerPacketV1.canonicalMomentKiller_moments
#print axioms AEGIS.WeilCanonicalMomentKillerPacketV1.canonicalMomentKiller_width
