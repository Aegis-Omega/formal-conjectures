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

import CvSTraceCramerV1
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# K3: the two-sample minor implies nondegeneracy of the truncated Gram matrix.

The theorem is independent of the Fourier coefficient closed-form proof.
-/

open scoped InnerProductSpace ComplexConjugate
noncomputable section

namespace AEGIS.CvSK3DetGBridgeV2

open AEGIS.CvSTraceCramerV1

theorem detG_ne_zero_of_two_sample_minor {LT : ℝ} (hLT : 0 < LT) (N : ℕ)
    (hk0 : (0 : ℤ) ∈ K N) (hk1 : (1 : ℤ) ∈ K N)
    (hminor : q hLT 0 0 * q hLT 1 1 - q hLT 1 0 * q hLT 0 1 ≠ 0) :
    detG hLT N ≠ 0 := by
  classical
  let ι := ↥(K N)
  letI : Fintype ι := Finset.fintypeCoeSort (K N)
  let j0 : ι := ⟨0, hk0⟩
  let j1 : ι := ⟨1, hk1⟩
  let v : Fin 2 → EuclideanSpace ℂ ι :=
    fun s => WithLp.toLp 2 (fun k : ι => q hLT s k.1)
  have hLI : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have heq (j : ι) :
        a 0 * q hLT 0 j.1 + a 1 * q hLT 1 j.1 = 0 := by
      have hj := congrArg (fun w : EuclideanSpace ℂ ι => w j) ha
      simpa [v, Fin.sum_univ_two, smul_eq_mul] using hj
    have h0 : a 0 * q hLT 0 0 + a 1 * q hLT 1 0 = 0 := heq j0
    have h1 : a 0 * q hLT 0 1 + a 1 * q hLT 1 1 = 0 := heq j1
    have ha0 : a 0 * (q hLT 0 0 * q hLT 1 1 - q hLT 1 0 * q hLT 0 1) = 0 := by
      calc
        _ = (a 0 * q hLT 0 0 + a 1 * q hLT 1 0) * q hLT 1 1 -
              (a 0 * q hLT 0 1 + a 1 * q hLT 1 1) * q hLT 1 0 := by ring
        _ = 0 := by rw [h0, h1]; ring
    have ha1 : a 1 * (q hLT 0 0 * q hLT 1 1 - q hLT 1 0 * q hLT 0 1) = 0 := by
      calc
        _ = (a 0 * q hLT 0 1 + a 1 * q hLT 1 1) * q hLT 0 0 -
              (a 0 * q hLT 0 0 + a 1 * q hLT 1 0) * q hLT 0 1 := by ring
        _ = 0 := by rw [h0, h1]; ring
    have hz0 : a 0 = 0 := by
      rcases mul_eq_zero.mp ha0 with h | h
      · exact h
      · exact (hminor h).elim
    have hz1 : a 1 = 0 := by
      rcases mul_eq_zero.mp ha1 with h | h
      · exact h
      · exact (hminor h).elim
    funext s
    fin_cases s
    · exact hz0
    · exact hz1
  have hGram : (Matrix.gram ℂ v).det ≠ 0 :=
    (Matrix.det_gram_ne_zero_iff_linearIndependent).2 hLI
  have hentry (s r : Fin 2) :
      gram hLT N s r = (LT : ℂ) * (Matrix.gram ℂ v) s r := by
    have he : (Matrix.gram ℂ v) s r =
        ∑ k ∈ K N, q hLT r k * conj (q hLT s k) := by
      calc
        _ = ∑ k : ι, conj (q hLT s k.1) * q hLT r k.1 := by
          simp only [Matrix.gram_apply, PiLp.inner_apply, RCLike.inner_apply',
            v, PiLp.toLp_apply]
        _ = ∑ k ∈ K N, conj (q hLT s k) * q hLT r k := by
          rw [Finset.univ_eq_attach (K N), Finset.sum_attach]
        _ = ∑ k ∈ K N, q hLT r k * conj (q hLT s k) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    simp only [gram, he]
  have hdet : detG hLT N = (LT : ℂ) ^ 2 * (Matrix.gram ℂ v).det := by
    unfold detG
    rw [hentry 0 0, hentry 1 1, hentry 0 1, hentry 1 0,
      Matrix.det_fin_two]
    ring
  rw [hdet]
  have hL : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  exact mul_ne_zero (pow_ne_zero 2 hL) hGram

theorem detG70_ne_zero_of_minor {LT : ℝ} (hLT : 0 < LT)
    (hminor : q hLT 0 0 * q hLT 1 1 - q hLT 1 0 * q hLT 0 1 ≠ 0) :
    detG hLT 70 ≠ 0 := by
  exact detG_ne_zero_of_two_sample_minor hLT 70
    (by simp [K]) (by simp [K]) hminor

end AEGIS.CvSK3DetGBridgeV2

#print axioms AEGIS.CvSK3DetGBridgeV2.detG_ne_zero_of_two_sample_minor
#print axioms AEGIS.CvSK3DetGBridgeV2.detG70_ne_zero_of_minor
