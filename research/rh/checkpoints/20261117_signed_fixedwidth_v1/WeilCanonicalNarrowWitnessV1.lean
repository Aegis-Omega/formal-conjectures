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

import WeilCanonicalMomentKillerPacketV1
import WeilSeparatedArchBridgeV31
import Mathlib.Tactic

/-!
An existing AEGIS moment-killer bump, with its potential rescaled by 2,
gives a NONZERO canonical Weil test packet of width <= 1/32.

This reuses the exact upstream AEGIS psi0 and the already-kernel-checked
moment construction and canonical log-transport; no new bump model is needed.

The existing V31 theorem gives a genuine Archimedean bound for all dyadic
gaps k >= 1. The signed prime-power witnesses in the Python certificates
are *different* sources and are NOT identified with this bump packet here.
No RH or sign claim is inferred.
-/

open Set MeasureTheory Complex
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCanonicalNarrowWitnessV1

open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilCanonicalMomentKillerPacketV1
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2

/-- Reuse the old smooth bump as a narrower potential, without dilating the
moment-killed output (which would destroy the weighted moment). -/
def psiHalf : ℝ → ℝ := fun t => psi0 (2 * t)

theorem psiHalf_contDiff : ContDiff ℝ ∞ psiHalf := by
  have hd : ContDiff ℝ ∞ (fun t : ℝ => (2 : ℝ) * t) :=
    contDiff_const.mul contDiff_id
  exact psi0_contDiff.comp hd

theorem psiHalf_tsupport :
    tsupport psiHalf ⊆ Icc (-(1 / 80 : ℝ)) (1 / 80) := by
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  have hne : psi0 (2 * t) ≠ 0 := by simpa [psiHalf] using ht
  have hm : 2 * t ∈ tsupport psi0 := subset_tsupport _ hne
  rw [psi0_tsupport, Real.closedBall_eq_Icc] at hm
  constructor <;> nlinarith [hm.1, hm.2]

theorem psiHalf_hasCompactSupport : HasCompactSupport psiHalf :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) psiHalf_tsupport

theorem psiHalf_at_zero : psiHalf 0 = 1 := by
  simpa [psiHalf] using psi0_ne_zero

def phiHalf : ℝ → ℝ := momentKiller psiHalf

theorem phiHalf_tsupport :
    tsupport phiHalf ⊆ Icc (-(1 / 80 : ℝ)) (1 / 80) :=
  (tsupport_momentKiller_subset psiHalf).trans psiHalf_tsupport

theorem phiHalf_vanishes_below :
    ∀ t : ℝ, t ≤ -(1 / 64 : ℝ) → phiHalf t = 0 := by
  intro t ht
  refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
  have hh := phiHalf_tsupport h
  linarith [hh.1]

theorem phiHalf_vanishes_above :
    ∀ t : ℝ, (1 / 64 : ℝ) ≤ t → phiHalf t = 0 := by
  intro t ht
  refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
  have hh := phiHalf_tsupport h
  linarith [hh.2]

def gHalf : WeilCompactSmoothGV1 :=
  canonicalPacket phiHalf (-(1 / 64)) (1 / 64)
    (momentKiller_contDiff psiHalf_contDiff)
    phiHalf_vanishes_below phiHalf_vanishes_above

theorem gHalf_moments : WeilMomentConditionsV1 gHalf := by
  exact canonicalMomentKiller_moments
    psiHalf (-(1 / 64)) (1 / 64)
    psiHalf_contDiff psiHalf_hasCompactSupport
    phiHalf_vanishes_below phiHalf_vanishes_above

theorem gHalf_width : WidthOneThirtyTwoAt gHalf 0 := by
  exact canonicalMomentKiller_width
    psiHalf psiHalf_contDiff phiHalf_vanishes_below phiHalf_vanishes_above

theorem phiHalf_ne_zero : phiHalf ≠ 0 := by
  intro h
  have hz := eq_zero_of_momentKiller_eq_zero
    psiHalf_contDiff psiHalf_hasCompactSupport h 0
  rw [psiHalf_at_zero] at hz
  norm_num at hz

theorem gHalf_ne_zero : gHalf.1 ≠ 0 := by
  intro h
  apply phiHalf_ne_zero
  funext t
  have hh := congrFun h (Real.exp t)
  have hc : ((mulPacket phiHalf (Real.exp t) : ℝ) : ℂ) = 0 := hh
  rw [AEGIS.WeilLogTransportCanonicalV1.mulPacket_of_pos (Real.exp_pos t),
      Real.log_exp] at hc
  exact_mod_cast hc

/-- Actual V31 Archimedean integral of the genuine AEGIS mixed pairing,
not a surrogate Gram entry. It holds for all positive dyadic gaps. -/
theorem gHalf_arch_dyadic (k : ℕ) (hk : 1 ≤ k) :
    ‖WeilArchimedeanIntegralV1
      (mixed (translatePacket gHalf 0)
        (translatePacket gHalf (k * Real.log 2)))‖ ≤
      (1 / 100 : ℝ) * energy gHalf.1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hk'
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    simpa using h
  exact AEGIS.WeilSeparatedArchBridgeV31.translated_arch_norm_bound
    gHalf 0 0 (k * Real.log 2) gHalf_width gHalf_moments
    (by simpa using hd)

end AEGIS.WeilCanonicalNarrowWitnessV1

#print axioms AEGIS.WeilCanonicalNarrowWitnessV1.gHalf_moments
#print axioms AEGIS.WeilCanonicalNarrowWitnessV1.gHalf_width
#print axioms AEGIS.WeilCanonicalNarrowWitnessV1.gHalf_ne_zero
#print axioms AEGIS.WeilCanonicalNarrowWitnessV1.gHalf_arch_dyadic
