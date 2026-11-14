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

import RHRepresentationHypothesisEquivalenceV1

open Filter Topology
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCofinalRepresentationEquivalenceV1

open AEGIS.RHRepresentationHypothesisEquivalenceV1

/-- Cofinal variant, in the shape of `UniversalActualCvSCofinalApproximation`
    and `UniversalActualCvSLowBlockApproximation`: the cutoffs must tend to
    infinity. If the forms are nonnegative and strictly positive at one fixed
    vector for every cutoff from `3` on, the hypothesis is still equivalent to
    "every `zeroSide g` is nonnegative".

    The reverse direction uses cutoffs `j + 3` and, at each cutoff, the real
    multiple of `v0` on which the form takes the value `zeroSide g`. The
    vectors are not tied to `g`, so the hypothesis restates the sign claim. -/
theorem cofinal_representation_iff_nonneg
    {G : Type*} {n : ℕ} (E : ℕ → Fin n → Fin n → ℝ) (zeroSide : G → ℝ)
    (hnonneg : ∀ M : ℕ, 3 ≤ M → ∀ v : Fin n → ℂ, 0 ≤ quadRe (E M) v)
    (v0 : Fin n → ℂ) (hpos : ∀ M : ℕ, 3 ≤ M → 0 < quadRe (E M) v0) :
    (∀ g : G,
      ∃ (M : ℕ → ℕ) (v : ℕ → Fin n → ℂ),
        (∀ j, 3 ≤ M j) ∧
        Tendsto M atTop atTop ∧
        Tendsto (fun j => quadRe (E (M j)) (v j))
          atTop (𝓝 (zeroSide g)))
      ↔ ∀ g : G, 0 ≤ zeroSide g := by
  constructor
  · intro hrep g
    obtain ⟨M, v, hM, -, hconv⟩ := hrep g
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hzero hconv
      (fun j => hnonneg (M j) (hM j) (v j))
  · intro h g
    have hq : ∀ j : ℕ, 0 < quadRe (E (j + 3)) v0 :=
      fun j => hpos (j + 3) (Nat.le_add_left 3 j)
    have hval : ∀ j : ℕ,
        quadRe (E (j + 3)) (fun i =>
          ((Real.sqrt (zeroSide g / quadRe (E (j + 3)) v0) : ℝ) : ℂ) * v0 i)
          = zeroSide g := by
      intro j
      have hs := quadRe_smul (E (j + 3))
        (Real.sqrt (zeroSide g / quadRe (E (j + 3)) v0)) v0
      rw [Real.sq_sqrt (div_nonneg (h g) (hq j).le)] at hs
      exact hs.trans (div_mul_cancel₀ _ (hq j).ne')
    refine ⟨fun j => j + 3,
      fun j => fun i =>
        ((Real.sqrt (zeroSide g / quadRe (E (j + 3)) v0) : ℝ) : ℂ) * v0 i,
      fun j => Nat.le_add_left 3 j, tendsto_add_atTop_nat 3, ?_⟩
    exact Tendsto.congr (fun j => (hval j).symm) tendsto_const_nhds

end AEGIS.RHCofinalRepresentationEquivalenceV1

#print axioms AEGIS.RHCofinalRepresentationEquivalenceV1.cofinal_representation_iff_nonneg
