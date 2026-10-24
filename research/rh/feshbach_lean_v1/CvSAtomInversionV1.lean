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

import CvSMomentBasisV1

/-!
# Second-difference inversion onto the sinSq moment atoms (CvS step K3c)

`momentAtom L n = −E_{n−1}/4 + E_n/2 − E_{n+1}/4` with `E_k = (iω_k² − 1/4) e^{iω_k x}`
(`momentAtom_eq`). For `b` on `K = [−N, N]` with `Σ_K b = 0` and `Σ_K k b = 0`, the
coefficients `α_p = −4 Σ_{j<p} (p − j) b_{j−N}` (`p = n + N`) satisfy

* `atom_sum`: `Σ_{i<2N−1} α_{i+1} · momentAtom L (i + 1 − N) = Σ_K b_k E_k`.

Not RH.
-/

open Complex Finset

noncomputable section

namespace AEGIS.CvSAtomInversionV1

open AEGIS.CvSMomentBasisV1

/-- `E_k(x) = (iω_k² − 1/4) e^{iω_k x}`. -/
def Ez (L : ℝ) (k : ℤ) (x : ℝ) : ℂ := (iw L k * iw L k - 1 / 4) * cexp (iw L k * x)

theorem momentAtom_eq (L : ℝ) (n : ℤ) (x : ℝ) :
    momentAtom L n x = -(1 / 4) * Ez L (n - 1) x + (1 / 2) * Ez L n x - (1 / 4) * Ez L (n + 1) x := by
  simp only [momentAtom, basisFun, expSum, sinSqSupport, Ez]
  have h1 : n - 1 ∉ ({n, n + 1} : Finset ℤ) := by simp; omega
  have h2 : n ∉ ({n + 1} : Finset ℤ) := by simp
  rw [sum_insert h1, sum_insert h2, sum_singleton, sum_insert h1, sum_insert h2, sum_singleton]
  simp only [sinSqWeight]
  have e1 : (n - 1 = n) = False := by simp
  have e2 : (n + 1 = n) = False := by simp
  simp only [e1, e2, if_true, if_false, true_or, or_true]
  ring

/-- `D(p) = Σ_{j<p} (p − j) b_j`. -/
def dsum (b : ℕ → ℂ) (p : ℕ) : ℂ := ∑ j ∈ range p, ((p : ℂ) - j) * b j

theorem dsum_zero (b : ℕ → ℂ) : dsum b 0 = 0 := by simp [dsum]

theorem dsum_succ (b : ℕ → ℂ) (p : ℕ) : dsum b (p + 1) = dsum b p + ∑ j ∈ range (p + 1), b j := by
  simp only [dsum]
  rw [sum_range_succ, sum_range_succ (fun j => b j)]
  have e : ∑ j ∈ range p, (((p + 1 : ℕ) : ℂ) - j) * b j =
      ∑ j ∈ range p, ((p : ℂ) - j) * b j + ∑ j ∈ range p, b j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e]
  push_cast
  ring

theorem dsum_second (b : ℕ → ℂ) (p : ℕ) :
    dsum b (p + 2) - 2 * dsum b (p + 1) + dsum b p = b (p + 1) := by
  rw [show p + 2 = (p + 1) + 1 by ring, dsum_succ, dsum_succ, sum_range_succ _ (p + 1)]
  ring

theorem dsum_end (b : ℕ → ℂ) (Q : ℕ) :
    dsum b Q = Q * ∑ j ∈ range (Q + 1), b j - ∑ j ∈ range (Q + 1), (j : ℂ) * b j := by
  simp only [dsum]
  rw [sum_range_succ (fun j => b j), sum_range_succ (fun j => (j : ℂ) * b j), mul_add, mul_sum]
  have e : ∑ j ∈ range Q, ((Q : ℂ) - j) * b j =
      ∑ j ∈ range Q, (Q : ℂ) * b j - ∑ j ∈ range Q, (j : ℂ) * b j := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [e]
  ring

/-- **Summation by parts for the three-point atoms.** -/
theorem shift_sum (α E : ℕ → ℂ) (M : ℕ) (h0 : α 0 = 0) (h1 : α (M + 1) = 0) (h2 : α (M + 2) = 0) :
    ∑ i ∈ range M, α (i + 1) * (-(1 / 4) * E i + (1 / 2) * E (i + 1) - (1 / 4) * E (i + 2)) =
      ∑ p ∈ range (M + 2),
        ((1 / 2) * α p - (1 / 4) * α (p - 1) - (1 / 4) * α (p + 1)) * E p := by
  have a : ∑ p ∈ range (M + 2), α p * E p = ∑ i ∈ range M, α (i + 1) * E (i + 1) := by
    rw [sum_range_succ, sum_range_succ', h1, h0]
    simp
  have b : ∑ p ∈ range (M + 2), α (p + 1) * E p = ∑ i ∈ range M, α (i + 1) * E i := by
    rw [sum_range_succ, sum_range_succ, h1, h2]
    simp
  have c : ∑ p ∈ range (M + 2), α (p - 1) * E p = ∑ i ∈ range M, α (i + 1) * E (i + 2) := by
    rw [sum_range_succ', sum_range_succ']
    simp [h0]
  have lhs : ∑ i ∈ range M, α (i + 1) * (-(1 / 4) * E i + (1 / 2) * E (i + 1) - (1 / 4) * E (i + 2)) =
      -(1 / 4) * ∑ i ∈ range M, α (i + 1) * E i + (1 / 2) * ∑ i ∈ range M, α (i + 1) * E (i + 1) -
        (1 / 4) * ∑ i ∈ range M, α (i + 1) * E (i + 2) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have rhs : ∑ p ∈ range (M + 2), ((1 / 2) * α p - (1 / 4) * α (p - 1) - (1 / 4) * α (p + 1)) * E p =
      (1 / 2) * ∑ p ∈ range (M + 2), α p * E p - (1 / 4) * ∑ p ∈ range (M + 2), α (p - 1) * E p -
        (1 / 4) * ∑ p ∈ range (M + 2), α (p + 1) * E p := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [lhs, rhs, a, b, c]
  ring

/-- `Σ_{k ∈ [−N, N]} f k = Σ_{j < 2N+1} f (j − N)`. -/
theorem sum_Icc_eq_range (N : ℕ) (f : ℤ → ℂ) :
    ∑ k ∈ Icc (-(N : ℤ)) N, f k = ∑ j ∈ range (2 * N + 1), f ((j : ℤ) - N) := by
  refine sum_nbij' (fun k => (k + N).toNat) (fun j => (j : ℤ) - N) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_Icc] at hk
    rw [mem_range]
    omega
  · intro j hj
    rw [mem_range] at hj
    rw [mem_Icc]
    omega
  · intro k hk
    rw [mem_Icc] at hk
    omega
  · intro j hj
    omega
  · intro k hk
    rw [mem_Icc] at hk
    congr 1
    omega

/-- The atom coefficients `α_p = −4 D(p)` for `b_j = b(j − N)`. -/
def alpha (N : ℕ) (b : ℤ → ℂ) (p : ℕ) : ℂ := -4 * dsum (fun j => b ((j : ℤ) - N)) p

/-- **The atoms reproduce every `b` with the two moment conditions.** -/
theorem atom_sum (L : ℝ) {N : ℕ} (hN : 1 ≤ N) (b : ℤ → ℂ)
    (hb0 : ∑ k ∈ Icc (-(N : ℤ)) N, b k = 0) (hb1 : ∑ k ∈ Icc (-(N : ℤ)) N, (k : ℂ) * b k = 0)
    (x : ℝ) :
    ∑ i ∈ range (2 * N - 1), alpha N b (i + 1) * momentAtom L (((i + 1 : ℕ) : ℤ) - N) x =
      ∑ k ∈ Icc (-(N : ℤ)) N, b k * Ez L k x := by
  set b' : ℕ → ℂ := fun j => b ((j : ℤ) - N) with hb'
  set M := 2 * N - 1 with hM
  have hM2 : M + 2 = 2 * N + 1 := by omega
  have c0 : ∑ j ∈ range (2 * N + 1), b' j = 0 := by rw [← sum_Icc_eq_range]; exact hb0
  have c1 : ∑ j ∈ range (2 * N + 1), (j : ℂ) * b' j = 0 := by
    have e : ∑ j ∈ range (2 * N + 1), (j : ℂ) * b' j =
        ∑ k ∈ Icc (-(N : ℤ)) N, ((k : ℂ) + N) * b k := by
      rw [sum_Icc_eq_range]
      refine sum_congr rfl fun j _ => ?_
      simp only [hb']
      push_cast
      ring
    rw [e]
    simp only [add_mul, sum_add_distrib, hb1, zero_add]
    rw [← mul_sum, hb0, mul_zero]
  have hα0 : alpha N b 0 = 0 := by simp [alpha, dsum_zero]
  have hα1 : alpha N b (M + 1) = 0 := by
    have hQ : M + 1 = 2 * N := by omega
    rw [hQ]
    simp only [alpha]
    rw [dsum_end, show 2 * N + 1 = 2 * N + 1 from rfl]
    rw [show (fun j : ℕ => b ((j : ℤ) - N)) = b' from rfl, c0, c1]
    ring
  have hα2 : alpha N b (M + 2) = 0 := by
    rw [hM2]
    simp only [alpha]
    rw [dsum_succ, dsum_end, show (fun j : ℕ => b ((j : ℤ) - N)) = b' from rfl, c0, c1]
    ring
  have hatom : ∀ i : ℕ, momentAtom L (((i + 1 : ℕ) : ℤ) - N) x =
      -(1 / 4) * Ez L ((i : ℤ) - N) x + (1 / 2) * Ez L (((i + 1 : ℕ) : ℤ) - N) x -
        (1 / 4) * Ez L (((i + 2 : ℕ) : ℤ) - N) x := by
    intro i
    rw [momentAtom_eq]
    push_cast
    ring_nf
  simp_rw [hatom]
  have hs := shift_sum (alpha N b) (fun p => Ez L ((p : ℤ) - N) x) M hα0 hα1 hα2
  rw [hs, hM2, sum_Icc_eq_range]
  refine sum_congr rfl fun p hp => ?_
  congr 1
  simp only [alpha]
  rcases Nat.eq_zero_or_pos p with h | h
  · subst h
    simp [dsum]
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have := dsum_second (fun j : ℕ => b ((j : ℤ) - N)) p'
    simp only [show p' + 1 - 1 = p' by omega, show p' + 1 + 1 = p' + 2 by ring]
    linear_combination this

end AEGIS.CvSAtomInversionV1

#print axioms AEGIS.CvSAtomInversionV1.momentAtom_eq
#print axioms AEGIS.CvSAtomInversionV1.dsum_second
#print axioms AEGIS.CvSAtomInversionV1.shift_sum
#print axioms AEGIS.CvSAtomInversionV1.sum_Icc_eq_range
#print axioms AEGIS.CvSAtomInversionV1.atom_sum
