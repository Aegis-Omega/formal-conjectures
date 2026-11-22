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
import RHLogFreeRowDecayV1

/-!
AEGIS Ω — a finite smooth partition with lattice centres (Claude Lab, 2026-11-21).

`AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition` takes its centres from an arbitrary finite
subcover, so nothing bounds how many centres fall in a unit interval. A row of the fine Gram can then carry
arbitrarily many log-free links (`eighty_five_log_free_links_exceed_fixed_row_budget`).

Here the centres are the lattice points `-L + i/192`. The cutoffs keep the support radius `1/256` used by
`WidthOneOneTwentyEightAt`, which needs lattice spacing below `2 · 1/256`. On this lattice,
`lattice_row_charge_le` bounds the distance-dependent log-free charge of any row by `4/5 < 57430/65536`.

Partition of unity and finite sums only; no Weil form, prime sum or sign. Not RH.
-/

open Set Finset
open scoped ContDiff BigOperators Manifold
set_option autoImplicit false
noncomputable section
namespace AEGIS.RHLatticeFinePartitionV1

open AEGIS.WeilSeparatedArchL1BridgeV32

/-- Lattice centre of index `i`, spacing `1/192`. -/
def latticeCenter (L : ℝ) (i : ℕ) : ℝ := -L + (i : ℝ) / 192

theorem exists_finite_smooth_lattice_partition (L : ℝ) :
    ∃ (n : ℕ) (χ : Fin (n + 1) → ℝ → ℂ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1) ∧
      (∀ i : Fin (n + 1), tsupport (χ i) ⊆
        Icc (latticeCenter L i - 1 / 256) (latticeCenter L i + 1 / 256)) := by
  classical
  let n : ℕ := ⌈384 * L⌉₊
  let U (i : Fin (n + 1)) : Set ℝ :=
    Ioo (latticeCenter L i - 1 / 256) (latticeCenter L i + 1 / 256)
  have hU : Icc (-L) L ⊆ ⋃ i : Fin (n + 1), U i := by
    intro x hx
    have ht0 : (0 : ℝ) ≤ (x + L) * 192 + 1 / 2 := by nlinarith [hx.1]
    have hk1 : (⌊(x + L) * 192 + 1 / 2⌋₊ : ℝ) ≤ (x + L) * 192 + 1 / 2 := Nat.floor_le ht0
    have hk2 : (x + L) * 192 + 1 / 2 < (⌊(x + L) * 192 + 1 / 2⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hkn : ⌊(x + L) * 192 + 1 / 2⌋₊ < n + 1 := by
      have hn : 384 * L ≤ (n : ℝ) := Nat.le_ceil _
      have h : (⌊(x + L) * 192 + 1 / 2⌋₊ : ℝ) < (n : ℝ) + 1 := by nlinarith [hx.2]
      exact_mod_cast h
    refine mem_iUnion.mpr ⟨⟨⌊(x + L) * 192 + 1 / 2⌋₊, hkn⟩, ?_⟩
    simp only [U, latticeCenter, Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ))
      isClosed_Icc U (fun _ => isOpen_Ioo) hU
  let χ (i : Fin (n + 1)) : ℝ → ℂ := Complex.ofRealCLM ∘ (ρ i)
  refine ⟨n, χ, ?_, ?_, ?_⟩
  · intro i
    exact Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp (ρ i).contMDiff)
  · intro x hx
    have hs : (∑ i : Fin (n + 1), ρ i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    change (∑ i : Fin (n + 1), (ρ i x : ℂ)) = 1
    exact_mod_cast hs
  · intro i x hx
    have hsmall : tsupport (χ i) ⊆ U i :=
      (tsupport_comp_subset rfl (ρ i)).trans (hρ i)
    exact ⟨(hsmall hx).1.le, (hsmall hx).2.le⟩

/-- **Row bound on the lattice.** Every row's distance-dependent log-free charge is `≤ 4/5`. -/
theorem lattice_row_charge_le (L : ℝ) (n : ℕ) (i : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hS : ∀ j ∈ S, (35 / 128 : ℝ) ≤ |latticeCenter L j - latticeCenter L i|) :
    ∑ j ∈ S, archRemainderV32 (|latticeCenter L j - latticeCenter L i| - 1 / 128) / 256 ≤ 4 / 5 := by
  classical
  have hdist : ∀ j : Fin (n + 1), latticeCenter L j - latticeCenter L i =
      ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ) / 192 := by
    intro j
    simp only [latticeCenter]
    push_cast
    ring
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) S := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by omega)
  have hrw : ∀ j ∈ S,
      archRemainderV32 (|latticeCenter L j - latticeCenter L i| - 1 / 128) / 256 =
        archRemainderV32 (|((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ)| / 192 - 1 / 128) / 256 := by
    intro j _
    rw [hdist j, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 192)]
  rw [Finset.sum_congr rfl hrw,
    ← Finset.sum_image (f := fun d : ℤ => archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256) hinj]
  apply AEGIS.RHLogFreeRowDecayV1.offsets_row_charge_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
  have h := hS j hj
  rw [hdist j, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 192)] at h
  have h1 : (105 / 2 : ℝ) ≤ |((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ)| := by linarith
  rw [← Int.cast_abs] at h1
  have h2 : (52 : ℤ) < |((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| := by
    have h3 : (52 : ℝ) < ((|((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| : ℤ) : ℝ) := by linarith
    exact_mod_cast h3
  show 53 ≤ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ∨ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≤ -53
  rcases le_or_gt 0 (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) with h0 | h0
  · rw [abs_of_nonneg h0] at h2
    left
    omega
  · rw [abs_of_neg h0] at h2
    right
    omega

end AEGIS.RHLatticeFinePartitionV1

#print axioms AEGIS.RHLatticeFinePartitionV1.exists_finite_smooth_lattice_partition
#print axioms AEGIS.RHLatticeFinePartitionV1.lattice_row_charge_le
