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

import RHLocalKreinPartitionV1

/-!
# Exact localization of an actual moment-zero Weil packet

Reuses the existing V13 compact Krein factor and the already proved
Leibniz/partition/moment lemmas. Both logarithmic moments of every atom
vanish; the sum reconstructs the *actual* logarithmic lift, without a
remainder and without an extra Schur or RH premise.

No universal sign conclusion is asserted. The next existing-source
composition step is transport of these atoms back to the typed
`WeilCompactSmoothGV1` carrier and use of the actual mixed Gram form.
-/

open Set MeasureTheory
open scoped ContDiff BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualKreinFactorJoinV1

open AEGIS.RHKreinFactorV13
open AEGIS.RHLocalKreinPartitionV1

/-- Every actual two-moment Weil packet has an *exact* binary localization.
Both localized Krein atoms retain both exponential moment cancellations. -/
theorem actual_packet_binary_krein_localization
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (a b : ℝ) (hab : a ≤ b)
    (hs : tsupport (lift g.1) ⊆ Icc a b)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ φ : ℝ → ℂ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      lift g.1 =
        (fun x => kreinAtom (fun y => χ y * φ y) x +
          kreinAtom (fun y => (1 - χ y) * φ y) x) ∧
      ((∫ x : ℝ, (Real.exp (-x / 2) : ℂ) *
            kreinAtom (fun y => χ y * φ y) x) = 0 ∧
        (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
            kreinAtom (fun y => χ y * φ y) x) = 0) ∧
      ((∫ x : ℝ, (Real.exp (-x / 2) : ℂ) *
            kreinAtom (fun y => (1 - χ y) * φ y) x) = 0 ∧
        (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
            kreinAtom (fun y => (1 - χ y) * φ y) x) = 0) := by
  obtain ⟨φ, hφ, hc, heq⟩ :=
    actual_packet_has_compact_krein_factor g hm a b hab hs
  refine ⟨φ, hφ, hc, ?_, ?_⟩
  · exact heq.trans (kreinAtom_partition_two φ χ hφ hχ).symm
  · exact kreinAtom_partition_moments φ χ hφ hχ hc

/-- The same exact reconstruction and both moments for an arbitrary finite
smooth partition of unity. The partition assumption is a concrete equality
of the selected cutoff functions, not a new positivity certificate. -/
theorem actual_packet_finite_krein_localization
    {ι : Type*} (s : Finset ι)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (a b : ℝ) (hab : a ≤ b)
    (hs : tsupport (lift g.1) ⊆ Icc a b)
    (χ : ι → ℝ → ℂ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i ∈ s, χ i x = 1) :
    ∃ φ : ℝ → ℂ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      lift g.1 =
        (fun x => ∑ i ∈ s, kreinAtom (fun y => χ i y * φ y) x) ∧
      ∀ i ∈ s,
        (∫ x : ℝ, (Real.exp (-x / 2) : ℂ) *
          kreinAtom (fun y => χ i y * φ y) x) = 0 ∧
        (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
          kreinAtom (fun y => χ i y * φ y) x) = 0 := by
  obtain ⟨φ, hφ, hc, heq⟩ :=
    actual_packet_has_compact_krein_factor g hm a b hab hs
  refine ⟨φ, hφ, hc, ?_, ?_⟩
  · exact heq.trans
      (kreinAtom_finite_partition s φ χ hφ hχ (fun x _ => hpart x))
  · intro i _
    exact kreinAtom_moments (fun y => χ i y * φ y)
      ((hχ i).mul hφ) hc.mul_left

end AEGIS.RHActualKreinFactorJoinV1

#print axioms AEGIS.RHActualKreinFactorJoinV1.actual_packet_binary_krein_localization
#print axioms AEGIS.RHActualKreinFactorJoinV1.actual_packet_finite_krein_localization
