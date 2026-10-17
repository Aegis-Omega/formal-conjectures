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
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import WeilCriterionCompactSmoothV1

/-!
# The actual Weil prime sum, split by Dirichlet characters

`ResidueClassFactorizationV1` (AEGIS) records that residue information enters the explicit
formula through characters. Here the actual prime term `WeilPrimeTermV1 f n` (the term of the
integer `n + 1`) restricted to a unit residue class `a` mod `q` is written as the average of its
`χ`-twisted terms, pointwise and for the whole series.
-/

open scoped BigOperators

namespace AEGIS.WeilPrimeSumCharacterV1

/-- The prime term of `n + 1`, kept only when `n + 1 ≡ a (mod q)`. -/
noncomputable def classTerm (q : ℕ) (a : ZMod q) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  if a = ((n + 1 : ℕ) : ZMod q) then WeilPrimeTermV1 f n else 0

/-- Pointwise orthogonality applied to the actual prime term. -/
theorem classTerm_eq_character_average (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (f : ℝ → ℂ) (n : ℕ) :
    classTerm q a f n = ((q.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * χ ((n + 1 : ℕ) : ZMod q) * WeilPrimeTermV1 f n := by
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  unfold classTerm
  split_ifs
  · field_simp
  · simp

/-- Each twisted series is summable when the prime series is absolutely summable. -/
theorem twisted_summable (q : ℕ) [NeZero q] (a : ZMod q) (f : ℝ → ℂ)
    (hs : Summable (fun n => ‖WeilPrimeTermV1 f n‖)) (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ => χ a⁻¹ * χ ((n + 1 : ℕ) : ZMod q) * WeilPrimeTermV1 f n) := by
  refine Summable.of_norm_bounded hs (fun n => ?_)
  rw [norm_mul, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ a⁻¹
  have h2 := DirichletCharacter.norm_le_one χ ((n + 1 : ℕ) : ZMod q)
  have h0 : 0 ≤ ‖WeilPrimeTermV1 f n‖ := norm_nonneg _
  calc ‖χ a⁻¹‖ * ‖χ ((n + 1 : ℕ) : ZMod q)‖ * ‖WeilPrimeTermV1 f n‖
      ≤ 1 * 1 * ‖WeilPrimeTermV1 f n‖ := by gcongr
    _ = ‖WeilPrimeTermV1 f n‖ := by ring

/-- The class-`a` part of the actual Weil prime sum is the average over the `φ(q)`
Dirichlet characters mod `q` of the `χ`-twisted prime sums. -/
theorem classSum_eq_character_average (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (f : ℝ → ℂ) (hs : Summable (fun n => ‖WeilPrimeTermV1 f n‖)) :
    ∑' n, classTerm q a f n = ((q.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q,
        ∑' n : ℕ, χ a⁻¹ * χ ((n + 1 : ℕ) : ZMod q) * WeilPrimeTermV1 f n := by
  simp_rw [classTerm_eq_character_average q ha f]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun χ _ => twisted_summable q a f hs χ)]

end AEGIS.WeilPrimeSumCharacterV1

#print axioms AEGIS.WeilPrimeSumCharacterV1.classTerm_eq_character_average
#print axioms AEGIS.WeilPrimeSumCharacterV1.twisted_summable
#print axioms AEGIS.WeilPrimeSumCharacterV1.classSum_eq_character_average
