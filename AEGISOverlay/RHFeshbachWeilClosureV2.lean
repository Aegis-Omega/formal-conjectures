/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-/

import RHExistingProofFusionV1
import Mathlib

/-!
# The cofinal Feshbach / actual Weil packet assembly

The earlier fusion required norm convergence and shifted-form convergence.
Here the norm-square sequence is only eventually bounded above, while a
nonnegative spectral shift permits transfer to the unshifted quadratic form.
The theorem at the end is conditional on genuinely constructing the stated
Schur families for all relevant Weil test packets. It is not a proof of RH.
-/

open Filter Topology

namespace AEGIS.RHFeshbachWeilClosureV2

theorem nonneg_of_vanishing_error_eventually_bounded
    {q eps normSq : ℕ → ℝ} {Q C : ℝ}
    (hq : Tendsto q atTop (𝓝 Q))
    (heps : Tendsto eps atTop (𝓝 0))
    (hepsNonneg : ∀ j, 0 ≤ eps j)
    (hbound : ∀ᶠ j in atTop, normSq j ≤ C)
    (hlower : ∀ j, -(eps j) * normSq j ≤ q j) :
    0 ≤ Q := by
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun j => -(eps j) * C) atTop (𝓝 0) := by
    simpa using heps.neg.mul hconst
  apply le_of_tendsto_of_tendsto' hzero hq
  filter_upwards [hbound] with j hj
  have hmul : eps j * normSq j ≤ eps j * C :=
    mul_le_mul_of_nonneg_left hj (hepsNonneg j)
  calc
    -(eps j) * C = -(eps j * C) := by ring
    _ ≤ -(eps j * normSq j) := neg_le_neg hmul
    _ = -(eps j) * normSq j := by ring
    _ ≤ q j := hlower j

theorem cofinal_feshbach_unshifted_eventually_bounded_nonnegative
    {N : ℕ → ℕ}
    {a re_b q nv nw β c μ normSq : ℕ → ℝ}
    {Q C : ℝ}
    (hN : Tendsto N atTop atTop)
    (hUnshiftLim : Tendsto
      (fun j => a j + 2 * re_b j + q j) atTop (𝓝 Q))
    (hNormBound : ∀ᶠ j in atTop, normSq j ≤ C)
    (hμ0 : ∀ j, 0 ≤ μ j)
    (hnw : ∀ j, 0 ≤ nw j)
    (hq : ∀ j, c j * nw j ^ 2 ≤ q j)
    (hb : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2)
    (hβ : ∀ j, 0 ≤ β j)
    (hμ : ∀ j, μ j < c j)
    (hSchur : ∀ j,
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j ≤
      a j - μ j * nv j ^ 2 - β j / (c j - μ j)) :
    0 ≤ Q := by
  refine nonneg_of_vanishing_error_eventually_bounded
    hUnshiftLim
    (FormalConjecturesUtil.FixedWindowLimitBridge.tendsto_invFourthError_along_cofinal hN)
    (fun j => ?_) hNormBound (fun j => ?_)
  · unfold FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError
    positivity
  · have hshift : 0 ≤ μ j * (nv j ^ 2 + nw j ^ 2) :=
      mul_nonneg (hμ0 j) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ a j - μ j * nv j ^ 2 - β j / (c j - μ j) :=
        hSchur j
      _ ≤ a j + 2 * re_b j + q j -
          μ j * (nv j ^ 2 + nw j ^ 2) :=
        AEGIS.RHFeshbachCoreV1.feshbach_lower
          (a j) (re_b j) (q j) (nv j) (nw j) (β j) (c j) (μ j)
          (hnw j) (hq j) (hb j) (hβ j) (hμ j)
      _ ≤ a j + 2 * re_b j + q j := sub_le_self _ hshift

/-- Exact packet-indexed assumptions for the as-yet-unconstructed
cofinal Schur certificates, including analytic identification of the limit. -/
structure PacketSchurFamily (g : WeilCompactSmoothGV1) where
  N : ℕ → ℕ
  a : ℕ → ℝ
  re_b : ℕ → ℝ
  q : ℕ → ℝ
  nv : ℕ → ℝ
  nw : ℕ → ℝ
  β : ℕ → ℝ
  c : ℕ → ℝ
  μ : ℕ → ℝ
  normSq : ℕ → ℝ
  normUpper : ℝ
  cofinal : Tendsto N atTop atTop
  reproducesWeil : Tendsto
    (fun j => a j + 2 * re_b j + q j) atTop
    (𝓝 (-(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re))
  eventuallyBounded : ∀ᶠ j in atTop, normSq j ≤ normUpper
  shiftNonnegative : ∀ j, 0 ≤ μ j
  tailNonnegative : ∀ j, 0 ≤ nw j
  tailCoercivity : ∀ j, c j * nw j ^ 2 ≤ q j
  crossBound : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2
  betaNonnegative : ∀ j, 0 ≤ β j
  shiftBelowGap : ∀ j, μ j < c j
  schurLower : ∀ j,
    -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
      normSq j ≤
    a j - μ j * nv j ^ 2 - β j / (c j - μ j)

theorem packet_weil_nonpositive (g : WeilCompactSmoothGV1)
    (h : PacketSchurFamily g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
  have hQ : 0 ≤
      -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re :=
    cofinal_feshbach_unshifted_eventually_bounded_nonnegative
      h.cofinal h.reproducesWeil h.eventuallyBounded h.shiftNonnegative
      h.tailNonnegative h.tailCoercivity h.crossBound h.betaNonnegative
      h.shiftBelowGap h.schurLower
  exact neg_nonneg.mp hQ

/-- Direct connection to the existing cofinal-window RH equivalence.
This implication is conditional; no packet family is silently postulated. -/
theorem riemannHypothesis_of_window_schur_families
    (h : ∀ n : ℕ, 0 < n →
      ∀ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g →
        AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g
          ((n : ℝ) * Real.pi) →
        PacketSchurFamily g) :
    RiemannHypothesis := by
  apply AEGIS.RHExistingProofFusionV1.rh_iff_pi_nat_windows.mpr
  intro n hn g hm hw
  exact packet_weil_nonpositive g (h n hn g hm hw)

end AEGIS.RHFeshbachWeilClosureV2

#print axioms AEGIS.RHFeshbachWeilClosureV2.nonneg_of_vanishing_error_eventually_bounded
#print axioms AEGIS.RHFeshbachWeilClosureV2.cofinal_feshbach_unshifted_eventually_bounded_nonnegative
#print axioms AEGIS.RHFeshbachWeilClosureV2.packet_weil_nonpositive
#print axioms AEGIS.RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families
