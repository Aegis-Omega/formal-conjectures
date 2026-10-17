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

import AEGISOverlay.RHWeilTiltComplementarityV1
import Mathlib

/-!
# Actual Mellin Snowflake: uniform complex compact-window frame

This theorem composes the already source-proved actual moment-zero
complementary pair with its entire Mellin transforms. On EACH nonempty
compact subset of the open critical strip, the two complex Mellin
evaluations have a single strictly positive joint lower bound.

The bound depends on the compact subset. This is NOT a global Fourier
frame on the full unbounded strip and does not imply the actual Weil
quadratic sign. Historical SHA-locked Snowflake / Krein sources are
unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSnowflakeActualMellinFrameV1

open AEGIS.RHWeilTiltComplementarityV1
open AEGIS.RHCompactMellinEntireV1
open MeasureTheory

/-- Entire Mellin transform of an actual compact smooth Weil packet is
continuous on the complete complex plane. -/
theorem actual_mellin_continuous (g : WeilCompactSmoothGV1) :
    Continuous (mellin g.1) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro z
  exact ((packet_mellin_entire g) z (Set.mem_univ z)).continuousAt

/-- Positive joint norm bound on any compact set where the actual Mellin
transforms have no common complex zero. The source functions are genuine
Weil packets rather than unrelated sinc surrogate symbols. -/
theorem actual_mellin_pair_compact_lower_bound
    (p q : WeilCompactSmoothGV1)
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hno : ∀ z : ℂ, z ∈ K →
      ¬ (mellin p.1 z = 0 ∧ mellin q.1 z = 0)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ K →
        δ ≤ ‖mellin p.1 z‖ ^ 2 + ‖mellin q.1 z‖ ^ 2 := by
  let F : ℂ → ℝ := fun z =>
    ‖mellin p.1 z‖ ^ 2 + ‖mellin q.1 z‖ ^ 2
  have hF : Continuous F :=
    (((actual_mellin_continuous p).norm).pow 2).add
      (((actual_mellin_continuous q).norm).pow 2)
  have hpositive : ∀ z : ℂ, z ∈ K → 0 < F z := by
    intro z hz
    have hnoz := hno z hz
    have hsqP : 0 ≤ ‖mellin p.1 z‖ ^ 2 :=
      sq_nonneg _
    have hsqQ : 0 ≤ ‖mellin q.1 z‖ ^ 2 :=
      sq_nonneg _
    by_contra hnot
    have hval : F z ≤ 0 := le_of_not_gt hnot
    have hpnorm : ‖mellin p.1 z‖ = 0 := by
      dsimp [F] at hval
      nlinarith [sq_nonneg (‖mellin p.1 z‖)]
    have hqnorm : ‖mellin q.1 z‖ = 0 := by
      dsimp [F] at hval
      nlinarith [sq_nonneg (‖mellin q.1 z‖)]
    exact hnoz ⟨norm_eq_zero.mp hpnorm, norm_eq_zero.mp hqnorm⟩
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hF.continuousOn
  refine ⟨F z, hpositive z hz, ?_⟩
  intro w hw
  exact hmin hw

/-- An UNCONDITIONALLY EXISTING pair of smooth moment-zero Weil packets
simultaneously detects every spectral point on a fixed compact subset
of the open critical strip, with a positive lower frame bound.
No global-in-K lower constant is asserted. -/
theorem unconditional_actual_mellin_compact_frame
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hstrip : ∀ z : ℂ, z ∈ K → 0 < z.re ∧ z.re < 1) :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℂ, z ∈ K →
          δ ≤ ‖mellin p.1 z‖ ^ 2 + ‖mellin q.1 z‖ ^ 2 := by
  obtain ⟨p, q, hp, hq, hno⟩ :=
    unconditional_moment_zero_complementary_pair
  obtain ⟨δ, hδ, hbound⟩ :=
    actual_mellin_pair_compact_lower_bound p q K hK hne
      (fun z hz => hno z (hstrip z hz).1 (hstrip z hz).2)
  exact ⟨p, q, hp, hq, δ, hδ, hbound⟩

/-- The SAME two actual smooth moment-zero packets work for EVERY
nonempty compact subset of the open critical strip. Only the strictly
positive frame constant is allowed to depend on the compact set.
This is stronger than choosing new packets separately for each K,
and explicitly preserves the source quantifier order. -/
theorem one_actual_pair_all_strip_compacts :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∀ (K : Set ℂ), IsCompact K → K.Nonempty →
        (∀ z : ℂ, z ∈ K → 0 < z.re ∧ z.re < 1) →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ z : ℂ, z ∈ K →
            δ ≤ ‖mellin p.1 z‖ ^ 2 + ‖mellin q.1 z‖ ^ 2 := by
  obtain ⟨p, q, hp, hq, hno⟩ :=
    unconditional_moment_zero_complementary_pair
  refine ⟨p, q, hp, hq, ?_⟩
  intro K hK hne hstrip
  exact actual_mellin_pair_compact_lower_bound p q K hK hne
    (fun z hz => hno z (hstrip z hz).1 (hstrip z hz).2)

/-- The SAME two genuine moment-zero Weil packets satisfy both:
(1) a positive lower frame bound on every compact subset of the open
critical strip, and (2) an unconditional cubic-decay UPPER bound on
all vertical lines throughout the closed strip. The upper bound is
imported from the existing AEGIS MellinDecayEstimateV1 theorem.
Neither bound is a positivity assumption on the Weil quadratic form. -/
theorem one_actual_pair_complex_frame_with_cubic_tail :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      (∀ (K : Set ℂ), IsCompact K → K.Nonempty →
        (∀ z : ℂ, z ∈ K → 0 < z.re ∧ z.re < 1) →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ z : ℂ, z ∈ K →
            δ ≤ ‖mellin p.1 z‖ ^ 2 + ‖mellin q.1 z‖ ^ 2) ∧
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ σ : ℝ, σ ∈ Set.Icc 0 1 → ∀ γ : ℝ,
          (1 + |γ|) ^ 3 *
            (‖mellin p.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ +
             ‖mellin q.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖) ≤ D := by
  obtain ⟨p, q, hp, hq, hno⟩ :=
    unconditional_moment_zero_complementary_pair
  obtain ⟨Dp, hDp, hdecayp⟩ :=
    weil_compact_smooth_mellin_vertical_cubic_decay_v1 p
  obtain ⟨Dq, hDq, hdecayq⟩ :=
    weil_compact_smooth_mellin_vertical_cubic_decay_v1 q
  refine ⟨p, q, hp, hq, ?_, Dp + Dq, add_nonneg hDp hDq, ?_⟩
  · intro K hK hne hstrip
    exact actual_mellin_pair_compact_lower_bound p q K hK hne
      (fun z hz => hno z (hstrip z hz).1 (hstrip z hz).2)
  · intro σ hσ γ
    calc
      (1 + |γ|) ^ 3 *
          (‖mellin p.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ +
           ‖mellin q.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖) =
        (1 + |γ|) ^ 3 *
          ‖mellin p.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ +
        (1 + |γ|) ^ 3 *
          ‖mellin q.1 ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := by ring
      _ ≤ Dp + Dq := add_le_add (hdecayp σ hσ γ) (hdecayq σ hσ γ)


/-! ## Genuine Mellin pair: exact complex pointwise Bézout

This is a pointwise complex-algebra reconstruction from the two
source-proved genuine moment-zero Weil packets. The coefficients are
conjugate-normalized and are NOT claimed holomorphic or compactly
supported: they must not be used as an unconditional Weil-sign bridge.
-/

/-- A no-common-zero pair of genuine Mellin transforms admits an exact
pointwise normalized conjugate Bézout identity throughout the open
critical strip. This is not a holomorphic Bézout theorem. -/
theorem actual_mellin_pair_complex_pointwise_bezout
    (p q : WeilCompactSmoothGV1)
    (hno : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      ¬ (mellin p.1 z = 0 ∧ mellin q.1 z = 0)) :
    ∃ A B : ℂ → ℂ,
      ∀ z : ℂ, 0 < z.re → z.re < 1 →
        A z * mellin p.1 z + B z * mellin q.1 z = 1 := by
  let F : ℂ → ℂ := fun z => mellin p.1 z
  let G : ℂ → ℂ := fun z => mellin q.1 z
  let d : ℂ → ℝ := fun z => ‖F z‖ ^ 2 + ‖G z‖ ^ 2
  have hpositive (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
      0 < d z := by
    have hn := hno z hz0 hz1
    have hF : 0 ≤ ‖F z‖ ^ 2 := sq_nonneg _
    have hG : 0 ≤ ‖G z‖ ^ 2 := sq_nonneg _
    by_contra hnot
    have hle : d z ≤ 0 := le_of_not_gt hnot
    have hFzero : ‖F z‖ = 0 := by
      dsimp [d] at hle
      nlinarith
    have hGzero : ‖G z‖ = 0 := by
      dsimp [d] at hle
      nlinarith
    exact hn ⟨norm_eq_zero.mp hFzero, norm_eq_zero.mp hGzero⟩
  refine ⟨fun z => Complex.conj (F z) / (d z : ℂ),
          fun z => Complex.conj (G z) / (d z : ℂ), ?_⟩
  intro z hz0 hz1
  have hne : (d z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hpositive z hz0 hz1))
  change
    Complex.conj (F z) / (d z : ℂ) * F z +
    Complex.conj (G z) / (d z : ℂ) * G z = 1
  calc
    Complex.conj (F z) / (d z : ℂ) * F z +
      Complex.conj (G z) / (d z : ℂ) * G z =
      (Complex.conj (F z) * F z + Complex.conj (G z) * G z) /
        (d z : ℂ) := by ring
    _ = 1 := by
      rw [Complex.conj_mul', Complex.conj_mul']
      have heq :
          ((‖F z‖ : ℂ) ^ 2 + (‖G z‖ : ℂ) ^ 2) = (d z : ℂ) := by
        simp [d, ← Complex.ofReal_pow]
      rw [heq]
      exact div_self hne

/-- One fixed pair of actual smooth moment-zero Weil packets gives
a global pointwise complex identity in the open critical strip.
The A/B coefficient functions depend on the spectral parameter;
their holomorphy and corresponding test-space stability are NOT claimed. -/
theorem one_actual_pair_complex_pointwise_bezout :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∃ A B : ℂ → ℂ,
        ∀ z : ℂ, 0 < z.re → z.re < 1 →
          A z * mellin p.1 z + B z * mellin q.1 z = 1 := by
  obtain ⟨p, q, hp, hq, hno⟩ :=
    unconditional_moment_zero_complementary_pair
  obtain ⟨A, B, hAB⟩ :=
    actual_mellin_pair_complex_pointwise_bezout p q hno
  exact ⟨p, q, hp, hq, A, B, hAB⟩

end AEGIS.RHSnowflakeActualMellinFrameV1

#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.actual_mellin_continuous
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.actual_mellin_pair_compact_lower_bound
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.unconditional_actual_mellin_compact_frame
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.one_actual_pair_all_strip_compacts
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.one_actual_pair_complex_frame_with_cubic_tail
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.actual_mellin_pair_complex_pointwise_bezout
#print axioms AEGIS.RHSnowflakeActualMellinFrameV1.one_actual_pair_complex_pointwise_bezout
