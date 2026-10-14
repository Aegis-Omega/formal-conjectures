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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A finite smooth partition on any compact real interval, subordinate
to arbitrarily small intervals. This supplies the actual finite cutoff
data required by the existing moment-zero Krein localization. -/

open Set Finset Complex
open scoped ContDiff BigOperators Manifold
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFiniteFinePartitionV1

theorem exists_finite_smooth_local_partition
    (L r : ℝ) (hr : 0 < r) :
    ∃ (n : ℕ) (χ : Fin (n + 1) → ℝ → ℂ)
      (center : Fin (n + 1) → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1) ∧
      (∀ i, tsupport (χ i) ⊆ Icc (center i - r) (center i + r)) := by
  classical
  let U (c : ℝ) : Set ℝ := Ioo (c - r) (c + r)
  have hcover : Icc (-L) L ⊆ ⋃ c : ℝ, U c := by
    intro x _hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    change x - r < x ∧ x < x + r
    constructor <;> linarith
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover U
    (fun _ => isOpen_Ioo) hcover
  let ι := ↥(insert (0 : ℝ) t)
  have hcard : 1 ≤ Fintype.card ι := by
    apply Nat.succ_le_of_lt
    exact Fintype.card_pos_iff.mpr ⟨⟨0, mem_insert_self 0 t⟩⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 :=
    Nat.exists_eq_add_of_le' hcard
  let e : Fin (n + 1) ≃ ι :=
    (finCongr hn.symm).trans (Fintype.equivFin ι).symm
  let center (i : Fin (n + 1)) : ℝ := (e i).1
  have hU : Icc (-L) L ⊆ ⋃ i : Fin (n + 1), U (center i) := by
    intro x hx
    rcases mem_iUnion.mp (ht hx) with ⟨c, hc⟩
    rcases mem_iUnion.mp hc with ⟨hct, hxc⟩
    let c' : ι := ⟨c, mem_insert_of_mem hct⟩
    refine mem_iUnion.mpr ⟨e.symm c', ?_⟩
    simpa only [center, e.apply_symm_apply] using hxc
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ))
      isClosed_Icc (fun i : Fin (n + 1) => U (center i))
      (fun _ => isOpen_Ioo) hU
  let χ (i : Fin (n + 1)) : ℝ → ℂ :=
    Complex.ofRealCLM ∘ (ρ i)
  refine ⟨n, χ, center, ?_, ?_, ?_⟩
  · intro i
    exact Complex.ofRealCLM.contDiff.comp
      (contMDiff_iff_contDiff.mp (ρ i).contMDiff)
  · intro x hx
    have hs : (∑ i : Fin (n + 1), ρ i x) = 1 := by
      simpa only [finsum_eq_sum] using ρ.sum_eq_one hx
    change (∑ i : Fin (n + 1), (ρ i x : ℂ)) = 1
    exact_mod_cast hs
  · intro i x hx
    have hsmall : tsupport (χ i) ⊆ U (center i) :=
      (tsupport_comp_subset rfl (ρ i)).trans (hρ i)
    exact ⟨(hsmall hx).1.le, (hsmall hx).2.le⟩

end AEGIS.RHFiniteFinePartitionV1

#print axioms AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition
