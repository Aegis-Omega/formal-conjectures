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

import Mathlib

open Filter Topology
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHRepresentationHypothesisEquivalenceV1

/-- Real part of a sesquilinear expression with real entries. This is the exact
    shape of `AEGIS.CvSProjectedSchurBridgeL12V1.projectedQ`, with the entry
    matrix left abstract. -/
def quadRe {n : ℕ} (E : Fin n → Fin n → ℝ) (v : Fin n → ℂ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n,
    v i * (starRingEnd ℂ) (v j) * (E i j : ℂ)).re

/-- Real scaling of the vector scales the expression quadratically. -/
theorem quadRe_smul {n : ℕ} (E : Fin n → Fin n → ℝ) (c : ℝ) (v : Fin n → ℂ) :
    quadRe E (fun i => (c : ℂ) * v i) = c ^ 2 * quadRe E v := by
  unfold quadRe
  have h : ∀ i j : Fin n,
      ((c : ℂ) * v i) * (starRingEnd ℂ) ((c : ℂ) * v j) * (E i j : ℂ)
        = ((c ^ 2 : ℝ) : ℂ) *
          (v i * (starRingEnd ℂ) (v j) * (E i j : ℂ)) := by
    intro i j
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp only [h, ← Finset.mul_sum]
  exact Complex.re_ofReal_mul _ _

/-- For a family of forms that is nonnegative from cutoff `3` on and takes one
    strictly positive value at cutoff `3`, the hypothesis "every `zeroSide g`
    is a limit of values of the forms" is equivalent to "every `zeroSide g` is
    nonnegative".

    The reverse direction uses a constant sequence: cutoff `3` and a real
    multiple of `v0`. The vectors of the sequence are not tied to `g` in any
    way, so a hypothesis of this shape is a restatement of the sign claim, not
    a reduction of it. -/
theorem representation_iff_nonneg
    {G : Type*} {n : ℕ} (E : ℕ → Fin n → Fin n → ℝ) (zeroSide : G → ℝ)
    (hnonneg : ∀ M : ℕ, 3 ≤ M → ∀ v : Fin n → ℂ, 0 ≤ quadRe (E M) v)
    (v0 : Fin n → ℂ) (hpos : 0 < quadRe (E 3) v0) :
    (∀ g : G,
      ∃ (M : ℕ → ℕ) (v : ℕ → Fin n → ℂ),
        (∀ j, 3 ≤ M j) ∧
        Tendsto (fun j => quadRe (E (M j)) (v j))
          atTop (𝓝 (zeroSide g)))
      ↔ ∀ g : G, 0 ≤ zeroSide g := by
  constructor
  · intro hrep g
    obtain ⟨M, v, hM, hconv⟩ := hrep g
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hzero hconv
      (fun j => hnonneg (M j) (hM j) (v j))
  · intro h g
    have hnn : 0 ≤ zeroSide g / quadRe (E 3) v0 :=
      div_nonneg (h g) hpos.le
    have hval :
        quadRe (E 3) (fun i =>
          ((Real.sqrt (zeroSide g / quadRe (E 3) v0) : ℝ) : ℂ) * v0 i)
          = zeroSide g := by
      have hs := quadRe_smul (E 3)
        (Real.sqrt (zeroSide g / quadRe (E 3) v0)) v0
      rw [Real.sq_sqrt hnn] at hs
      exact hs.trans (div_mul_cancel₀ _ hpos.ne')
    refine ⟨fun _ => 3,
      fun _ => fun i =>
        ((Real.sqrt (zeroSide g / quadRe (E 3) v0) : ℝ) : ℂ) * v0 i,
      fun _ => le_refl 3, ?_⟩
    exact Tendsto.congr (fun _ => hval.symm) tendsto_const_nhds

end AEGIS.RHRepresentationHypothesisEquivalenceV1

#print axioms AEGIS.RHRepresentationHypothesisEquivalenceV1.quadRe_smul
#print axioms AEGIS.RHRepresentationHypothesisEquivalenceV1.representation_iff_nonneg
