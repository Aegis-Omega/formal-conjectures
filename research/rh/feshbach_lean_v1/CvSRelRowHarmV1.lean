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

/-!
# Row sums of `1/|x − m|` and integer roundings

* `inv_sum_le`: for `A ⊆ [x − K₁, x + K₂] \ {x}`, `Σ_{m ∈ A} 1/|x − m| ≤ H_{K₁} + H_{K₂}`;
* `harmonic_le_hup`: `H_K ≤ hupN K / 2^64` with the integer `hupN K = Σ_{k<K} ⌈2^64/(k+1)⌉`;
* `ediv_err`: `|a/b − ⌊a/b⌋_ℤ| < 1` for Lean's `Int./` and `b ≠ 0`.
Not RH.
-/

open Finset

namespace AEGIS.CvSRelRowHarmV1

/-- `Σ_{k<K} ⌈2^64/(k+1)⌉`. -/
def hupN (K : ℕ) : ℕ := ∑ k ∈ range K, (2 ^ 64 + k) / (k + 1)

theorem inv_le_ceil (k : ℕ) : (1 : ℝ) / ((k : ℝ) + 1) ≤ (((2 ^ 64 + k) / (k + 1) : ℕ) : ℝ) / 2 ^ 64 := by
  have h := Nat.div_add_mod (2 ^ 64 + k) (k + 1)
  have hr := Nat.mod_lt (2 ^ 64 + k) (show k + 1 > 0 by omega)
  have key : 2 ^ 64 ≤ (k + 1) * ((2 ^ 64 + k) / (k + 1)) := by omega
  have key' : (2 : ℝ) ^ 64 ≤ ((k : ℝ) + 1) * (((2 ^ 64 + k) / (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast key
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem harmonic_le_hup (K : ℕ) : (harmonic K : ℝ) ≤ (hupN K : ℝ) / 2 ^ 64 := by
  simp only [harmonic, hupN]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have := inv_le_ceil k
  rw [one_div] at this
  exact_mod_cast this

/-- The sum over `x + 1, …, x + K`. -/
theorem sum_right (x : ℤ) (K : ℕ) :
    ∑ m ∈ Icc (x + 1) (x + K), (1 : ℝ) / |(x : ℝ) - m| = (harmonic K : ℝ) := by
  simp only [harmonic]
  push_cast
  refine sum_nbij' (fun m => (m - x - 1).toNat) (fun k => x + 1 + k) ?_ ?_ ?_ ?_ ?_
  · intro m hm; rw [mem_Icc] at hm; rw [mem_range]; omega
  · intro k hk; rw [mem_range] at hk; rw [mem_Icc]; omega
  · intro m hm; rw [mem_Icc] at hm; omega
  · intro k _; omega
  · intro m hm
    rw [mem_Icc] at hm
    have e : ((m - x - 1).toNat : ℝ) = (m : ℝ) - x - 1 := by
      have : ((m - x - 1).toNat : ℤ) = m - x - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [e, abs_sub_comm, abs_of_pos (by
      have : (x : ℝ) + 1 ≤ m := by exact_mod_cast hm.1
      linarith), one_div]
    ring_nf

/-- The sum over `x − K, …, x − 1`. -/
theorem sum_left (x : ℤ) (K : ℕ) :
    ∑ m ∈ Icc (x - K) (x - 1), (1 : ℝ) / |(x : ℝ) - m| = (harmonic K : ℝ) := by
  simp only [harmonic]
  push_cast
  refine sum_nbij' (fun m => (x - 1 - m).toNat) (fun k => x - 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro m hm; rw [mem_Icc] at hm; rw [mem_range]; omega
  · intro k hk; rw [mem_range] at hk; rw [mem_Icc]; omega
  · intro m hm; rw [mem_Icc] at hm; omega
  · intro k _; omega
  · intro m hm
    rw [mem_Icc] at hm
    have e : ((x - 1 - m).toNat : ℝ) = (x : ℝ) - 1 - m := by
      have : ((x - 1 - m).toNat : ℤ) = x - 1 - m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [e, abs_of_pos (by
      have : (m : ℝ) ≤ x - 1 := by exact_mod_cast hm.2
      linarith), one_div]
    ring_nf

/-- **Row sums of `1/|x − m|`.** -/
theorem inv_sum_le (x : ℤ) (A : Finset ℤ) (K₁ K₂ : ℕ)
    (hA : ∀ m ∈ A, m ≠ x ∧ x - K₁ ≤ m ∧ m ≤ x + K₂) :
    ∑ m ∈ A, (1 : ℝ) / |(x : ℝ) - m| ≤ (harmonic K₁ : ℝ) + harmonic K₂ := by
  have hsub : A ⊆ Icc (x - K₁) (x - 1) ∪ Icc (x + 1) (x + K₂) := by
    intro m hm
    obtain ⟨h1, h2, h3⟩ := hA m hm
    rw [mem_union, mem_Icc, mem_Icc]
    omega
  have hdisj : Disjoint (Icc (x - K₁) (x - 1)) (Icc (x + 1) (x + K₂)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    rw [mem_Icc] at h1 h2
    omega
  calc ∑ m ∈ A, (1 : ℝ) / |(x : ℝ) - m|
      ≤ ∑ m ∈ Icc (x - K₁) (x - 1) ∪ Icc (x + 1) (x + K₂), (1 : ℝ) / |(x : ℝ) - m| :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = _ := by rw [sum_union hdisj, sum_left, sum_right]

/-- Lean's `Int./` is within `1` of the real quotient. -/
theorem ediv_err (a b : ℤ) (hb : b ≠ 0) : |(a : ℝ) / b - ((a / b : ℤ) : ℝ)| < 1 := by
  have h := Int.emod_add_mul_ediv a b
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have e : (a : ℝ) / b - ((a / b : ℤ) : ℝ) = ((a % b : ℤ) : ℝ) / b := by
    have : (a : ℝ) = ((a % b : ℤ) : ℝ) + b * ((a / b : ℤ) : ℝ) := by exact_mod_cast h.symm
    rw [this]
    field_simp
    ring
  rw [e, abs_div]
  have hr0 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h0
  have hr1 : ((a % b : ℤ) : ℝ) < |(b : ℝ)| := by
    have : a % b < |b| := by rw [Int.abs_eq_natAbs]; exact h1
    exact_mod_cast this
  rw [abs_of_nonneg hr0, div_lt_one (abs_pos.mpr hb')]
  exact hr1

end AEGIS.CvSRelRowHarmV1

#print axioms AEGIS.CvSRelRowHarmV1.harmonic_le_hup
#print axioms AEGIS.CvSRelRowHarmV1.inv_sum_le
#print axioms AEGIS.CvSRelRowHarmV1.ediv_err
