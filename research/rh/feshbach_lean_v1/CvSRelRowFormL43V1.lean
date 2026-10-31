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
import CvSRelRowPsdL43V1
import CvSMomentBasisV1
import CvSLowBlockMatrixV1

/-!
# The check matrix at `L = 4/3` as a form in the low-block coefficients

For the 139 atoms `momentAtom (4/3) (i - 69)` and a coefficient vector `c`, let
`u_n = Σ_i c_i β_i(n)` (the sinSq weights) and `â_n = (φ_n / 2^72) u_n`. Then
`Re Σ c_i conj(c_j) Pm i j = 2^360 Re Σ_{n,m} â_n conj(â_m) Zt n m − 2^148 Σ_j γ_j ‖Σ_n â_n V_j(n)‖²`
(`Pform_eq`), so `CvSRelRowPsdL43V1.Pm_psd` gives the midpoint inequality `midpoint_ge`. Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowCheckL43V1 AEGIS.CvSRelRowPsdL43V1
  AEGIS.CvSMomentBasisV1 AEGIS.CvSLowBlockMatrixV1

noncomputable section

namespace AEGIS.CvSRelRowFormL43V1

set_option exponentiation.threshold 1000

/-- The atom centres `-69, …, 69`. -/
def ctr (i : Fin 139) : ℤ := (i : ℤ) - 69

/-- The low frequencies `-70, …, 70`. -/
abbrev F : Finset ℤ := Icc (-70) 70

/-- The weight of atom `i` at frequency `n`. -/
def wt (n : ℤ) (i : Fin 139) : ℂ :=
  if n ∈ sinSqSupport (ctr i) then sinSqWeight (ctr i) n else 0

/-- `u_n = Σ_i c_i β_i(n)`. -/
def uvec (c : Fin 139 → ℂ) (n : ℤ) : ℂ := ∑ i, c i * wt n i

/-- The midpoint coefficients `â_n = (φ_n / 2^72) u_n`. -/
noncomputable def ahat (c : Fin 139 → ℂ) (n : ℤ) : ℂ := (((phi n : ℝ) / 2 ^ 72 : ℝ) : ℂ) * uvec c n

theorem support_sub (i : Fin 139) : sinSqSupport (ctr i) ⊆ F := by
  intro n hn
  have hi := i.isLt
  simp only [sinSqSupport, ctr, Finset.mem_insert, Finset.mem_singleton] at hn
  simp only [F, Finset.mem_Icc]
  omega

theorem mem_F_of_bounds {n : ℤ} (h1 : -70 ≤ n) (h2 : n ≤ 70) : ∃ i : Fin 139, n ∈ sinSqSupport (ctr i) := by
  by_cases h : n = -70
  · refine ⟨⟨0, by norm_num⟩, ?_⟩
    simp [sinSqSupport, ctr, h]
  by_cases h' : n = 70
  · refine ⟨⟨138, by norm_num⟩, ?_⟩
    simp [sinSqSupport, ctr, h']
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = n + 69 := ⟨(n + 69).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨⟨k, by omega⟩, ?_⟩
    simp only [sinSqSupport, ctr, Finset.mem_insert, Finset.mem_singleton]
    omega

theorem lowFreq_eq : lowFreq (fun i : Fin 139 => sinSqSupport (ctr i)) = F := by
  ext n
  simp only [lowFreq, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩; exact support_sub i hi
  · intro hn
    rw [Finset.mem_Icc] at hn
    exact mem_F_of_bounds hn.1 hn.2

/-- One atom: `Σ_s w_s g(i - 70 + s) = 4 Σ_n β_i(n) g(n)`. -/
theorem atom_window (i : Fin 139) (g : ℤ → ℂ) :
    ∑ s ∈ range 3, (wq s : ℂ) * g ((i : ℤ) - 70 + s) = 4 * ∑ n ∈ F, wt n i * g n := by
  have e1 : ∑ n ∈ F, wt n i * g n = ∑ n ∈ sinSqSupport (ctr i), wt n i * g n :=
    (sum_subset (support_sub i) fun n _ hn => by simp only [wt, if_neg hn, zero_mul]).symm
  have e2 : ∑ n ∈ sinSqSupport (ctr i), wt n i * g n =
      ∑ n ∈ sinSqSupport (ctr i), sinSqWeight (ctr i) n * g n :=
    sum_congr rfl fun n hn => by simp only [wt, if_pos hn]
  rw [e1, e2]
  have hne1 : ctr i - 1 ∉ ({ctr i, ctr i + 1} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hne2 : ctr i ∉ ({ctr i + 1} : Finset ℤ) := by simp
  simp only [sinSqSupport]
  rw [sum_insert hne1, sum_insert hne2, sum_singleton]
  have w1 : sinSqWeight (ctr i) (ctr i - 1) = -1 / 4 := by
    simp only [sinSqWeight, show ctr i - 1 ≠ ctr i by omega, if_false, true_or, if_true]
  have w2 : sinSqWeight (ctr i) (ctr i) = 1 / 2 := by simp [sinSqWeight]
  have w3 : sinSqWeight (ctr i) (ctr i + 1) = -1 / 4 := by
    simp only [sinSqWeight, show ctr i + 1 ≠ ctr i by omega, if_false, or_true, if_true]
  rw [w1, w2, w3]
  have a0 : (i : ℤ) - 70 + ((0 : ℕ) : ℤ) = ctr i - 1 := by simp only [ctr]; push_cast; ring
  have a1 : (i : ℤ) - 70 + ((1 : ℕ) : ℤ) = ctr i := by simp only [ctr]; push_cast; ring
  have a2 : (i : ℤ) - 70 + ((2 : ℕ) : ℤ) = ctr i + 1 := by simp only [ctr]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, a0, a1, a2, wq]
  norm_num
  ring

/-- **Reindexing.** `Σ_i c_i Σ_s w_s g(i - 70 + s) = 4 Σ_n u_n g(n)`. -/
theorem reindex (c : Fin 139 → ℂ) (g : ℤ → ℂ) :
    ∑ i : Fin 139, c i * ∑ s ∈ range 3, (wq s : ℂ) * g ((i : ℤ) - 70 + s) =
      4 * ∑ n ∈ F, uvec c n * g n := by
  simp_rw [atom_window]
  simp only [uvec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring

theorem reindex_conj (c : Fin 139 → ℂ) (g : ℤ → ℂ) :
    ∑ j : Fin 139, conj (c j) * ∑ t ∈ range 3, (wq t : ℂ) * g ((j : ℤ) - 70 + t) =
      4 * ∑ m ∈ F, conj (uvec c m) * g m := by
  have h := reindex (fun j => conj (c j)) g
  have e : ∀ m, uvec (fun j => conj (c j)) m = conj (uvec c m) := by
    intro m
    simp only [uvec, map_sum, map_mul]
    refine sum_congr rfl fun j _ => ?_
    congr 1
    simp only [wt, sinSqWeight]
    split_ifs <;> simp [map_div₀, map_neg, map_one, map_ofNat]
  simpa only [e] using h

theorem phi_ahat (c : Fin 139 → ℂ) (n : ℤ) :
    uvec c n * (phi n : ℂ) = 2 ^ 72 * ahat c n := by
  simp only [ahat]
  push_cast
  field_simp

theorem phi_ahat_conj (c : Fin 139 → ℂ) (m : ℤ) :
    conj (uvec c m) * (phi m : ℂ) = 2 ^ 72 * conj (ahat c m) := by
  simp only [ahat, map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

/-- The `U` vectors in the coefficients `â`. -/
theorem U_sum (c : Fin 139 → ℂ) (jj : ℕ) :
    ∑ i : Fin 139, c i * (U jj i : ℂ) = 4 * 2 ^ 72 * ∑ n ∈ F, ahat c n * (Vq jj n : ℂ) := by
  have h := reindex c (fun n => (phi n : ℂ) * (Vq jj n : ℂ))
  have e : ∀ i : Fin 139, (U jj i : ℂ) =
      ∑ s ∈ range 3, (wq s : ℂ) * ((phi ((i : ℤ) - 70 + s) : ℂ) * (Vq jj ((i : ℤ) - 70 + s) : ℂ)) := by
    intro i; simp only [U]; push_cast; rfl
  simp_rw [e, h, mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← mul_assoc (uvec c n), phi_ahat]
  ring

theorem U_sum_conj (c : Fin 139 → ℂ) (jj : ℕ) :
    ∑ j : Fin 139, conj (c j) * (U jj j : ℂ) =
      4 * 2 ^ 72 * conj (∑ n ∈ F, ahat c n * (Vq jj n : ℂ)) := by
  have h := congrArg conj (U_sum c jj)
  rw [map_sum] at h
  simp only [map_mul, map_intCast, map_pow, map_ofNat] at h
  exact h

/-- **Double reindexing.** -/
theorem double_reindex (c : Fin 139 → ℂ) (K : ℤ → ℤ → ℂ) :
    ∑ i : Fin 139, ∑ j : Fin 139, c i * conj (c j) *
      (∑ s ∈ range 3, ∑ t ∈ range 3, (wq s : ℂ) * (wq t : ℂ) * K ((i : ℤ) - 70 + s) ((j : ℤ) - 70 + t)) =
      16 * ∑ n ∈ F, ∑ m ∈ F, uvec c n * conj (uvec c m) * K n m := by
  have split : ∀ i : Fin 139, ∑ j : Fin 139, c i * conj (c j) *
      (∑ s ∈ range 3, ∑ t ∈ range 3, (wq s : ℂ) * (wq t : ℂ) * K ((i : ℤ) - 70 + s) ((j : ℤ) - 70 + t)) =
      c i * ∑ s ∈ range 3, (wq s : ℂ) * (4 * ∑ m ∈ F, conj (uvec c m) * K ((i : ℤ) - 70 + s) m) := by
    intro i
    simp only [← reindex_conj c]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun t _ => ?_
    ring
  simp_rw [split]
  rw [reindex c (fun n => 4 * ∑ m ∈ F, conj (uvec c m) * K n m)]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring

theorem rank_one_sum (c : Fin 139 → ℂ) (G : ℂ) (a : Fin 139 → ℂ) :
    ∑ i : Fin 139, ∑ j : Fin 139, c i * conj (c j) * (G * a i * a j) =
      G * ((∑ i : Fin 139, c i * a i) * ∑ j : Fin 139, conj (c j) * a j) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The check form in the coefficients `â`.** -/
theorem Pform_eq (c : Fin 139 → ℂ) :
    ∑ i : Fin 139, ∑ j : Fin 139, c i * conj (c j) * ((Pm i j : ℝ) : ℂ) =
      2 ^ 360 * ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (Zt n m : ℂ) -
        2 ^ 148 * ((G1q : ℂ) * ((∑ n ∈ F, ahat c n * (Vq 0 n : ℂ)) *
            conj (∑ n ∈ F, ahat c n * (Vq 0 n : ℂ))) +
          (G2q : ℂ) * ((∑ n ∈ F, ahat c n * (Vq 1 n : ℂ)) *
            conj (∑ n ∈ F, ahat c n * (Vq 1 n : ℂ)))) := by
  have e : ∀ i j : Fin 139, c i * conj (c j) * ((Pm i j : ℝ) : ℂ) =
      2 ^ 212 * (c i * conj (c j) * (∑ s ∈ range 3, ∑ t ∈ range 3, (wq s : ℂ) * (wq t : ℂ) *
        (Zf ((i : ℤ) - 70 + s) ((j : ℤ) - 70 + t) : ℂ))) -
      c i * conj (c j) * ((G1q : ℂ) * (U 0 i : ℂ) * (U 0 j : ℂ)) -
      c i * conj (c j) * ((G2q : ℂ) * (U 1 i : ℂ) * (U 1 j : ℂ)) := by
    intro i j
    simp only [Pm]
    push_cast
    ring
  simp only [e, Finset.sum_sub_distrib]
  rw [rank_one_sum, rank_one_sum]
  simp only [← Finset.mul_sum]
  rw [double_reindex c (fun n m => (Zf n m : ℂ)), U_sum, U_sum_conj, U_sum, U_sum_conj]
  have hZ : ∑ n ∈ F, ∑ m ∈ F, uvec c n * conj (uvec c m) * (Zf n m : ℂ) =
      2 ^ 144 * ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (Zt n m : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e0 : (Zf n m : ℂ) = (phi n : ℂ) * (phi m : ℂ) * (Zt n m : ℂ) := by
      simp only [Zf]; push_cast; ring
    rw [e0]
    have e1 := phi_ahat c n
    have e2 := phi_ahat_conj c m
    calc uvec c n * conj (uvec c m) * ((phi n : ℂ) * (phi m : ℂ) * (Zt n m : ℂ)) =
        (uvec c n * (phi n : ℂ)) * (conj (uvec c m) * (phi m : ℂ)) * (Zt n m : ℂ) := by ring
      _ = _ := by rw [e1, e2]; ring
  rw [hZ]
  ring

theorem normSq_eq_mul_conj (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **The midpoint inequality**, from the kernel-checked positivity of `Pm`. -/
theorem midpoint_ge (c : Fin 139 → ℂ) :
    ((G1q : ℝ) / 2 ^ 64) * ‖∑ n ∈ F, ahat c n * ((Vq 0 n : ℝ) / 2 ^ 138 : ℝ)‖ ^ 2 +
      ((G2q : ℝ) / 2 ^ 64) * ‖∑ n ∈ F, ahat c n * ((Vq 1 n : ℝ) / 2 ^ 138 : ℝ)‖ ^ 2 ≤
      (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * ((Zt n m : ℝ) / 2 ^ 128 : ℝ)).re := by
  have h := Pm_psd c
  rw [Pform_eq] at h
  have s1 : ∀ jj : ℕ, ∑ n ∈ F, ahat c n * (((Vq jj n : ℝ) / 2 ^ 138 : ℝ) : ℂ) =
      (1 / 2 ^ 138 : ℂ) * ∑ n ∈ F, ahat c n * (Vq jj n : ℂ) := by
    intro jj; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by push_cast; ring
  have s2 : ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (((Zt n m : ℝ) / 2 ^ 128 : ℝ) : ℂ) =
      (1 / 2 ^ 128 : ℂ) * ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (Zt n m : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by push_cast; ring
  rw [s1, s1, s2]
  set A := ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (Zt n m : ℂ)
  set V0 := ∑ n ∈ F, ahat c n * (Vq 0 n : ℂ)
  set V1 := ∑ n ∈ F, ahat c n * (Vq 1 n : ℂ)
  have hre : (2 ^ 360 * A - 2 ^ 148 * ((G1q : ℂ) * (V0 * conj V0) + (G2q : ℂ) * (V1 * conj V1))).re =
      2 ^ 360 * A.re - 2 ^ 148 * ((G1q : ℝ) * ‖V0‖ ^ 2 + (G2q : ℝ) * ‖V1‖ ^ 2) := by
    have c360 : (2 : ℂ) ^ 360 = (((2 : ℝ) ^ 360 : ℝ) : ℂ) := by norm_cast
    have c148 : (2 : ℂ) ^ 148 = (((2 : ℝ) ^ 148 : ℝ) : ℂ) := by norm_cast
    have g1 : (G1q : ℂ) = ((G1q : ℝ) : ℂ) := by norm_cast
    have g2 : (G2q : ℂ) = ((G2q : ℝ) : ℂ) := by norm_cast
    rw [c360, c148, g1, g2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, normSq_eq_mul_conj,
      normSq_eq_mul_conj]
  rw [hre] at h
  have hnc : ‖(1 / 2 ^ 138 : ℂ)‖ = 1 / 2 ^ 138 := by simp [norm_pow]
  have hn1 : ‖(1 / 2 ^ 138 : ℂ) * V0‖ ^ 2 = ‖V0‖ ^ 2 / 2 ^ 276 := by
    rw [norm_mul, hnc]; ring
  have hn2 : ‖(1 / 2 ^ 138 : ℂ) * V1‖ ^ 2 = ‖V1‖ ^ 2 / 2 ^ 276 := by
    rw [norm_mul, hnc]; ring
  have hA : ((1 / 2 ^ 128 : ℂ) * A).re = A.re / 2 ^ 128 := by
    rw [show (1 / 2 ^ 128 : ℂ) = ((1 / 2 ^ 128 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [hn1, hn2, hA]
  have h2 : (0 : ℝ) < 2 ^ 360 := by positivity
  have key : 2 ^ 148 * ((G1q : ℝ) * ‖V0‖ ^ 2 + (G2q : ℝ) * ‖V1‖ ^ 2) ≤ 2 ^ 360 * A.re := by linarith
  have e360 : (2 : ℝ) ^ 360 * A.re = 2 ^ 148 * (2 ^ 212 * A.re) := by ring
  rw [e360] at key
  have k2 : (G1q : ℝ) * ‖V0‖ ^ 2 + (G2q : ℝ) * ‖V1‖ ^ 2 ≤ 2 ^ 212 * A.re :=
    le_of_mul_le_mul_left key (by positivity)
  have : (G1q : ℝ) / 2 ^ 64 * (‖V0‖ ^ 2 / 2 ^ 276) + (G2q : ℝ) / 2 ^ 64 * (‖V1‖ ^ 2 / 2 ^ 276) =
      ((G1q : ℝ) * ‖V0‖ ^ 2 + (G2q : ℝ) * ‖V1‖ ^ 2) / 2 ^ 340 := by ring
  rw [this, div_le_iff₀ (by positivity)]
  calc (G1q : ℝ) * ‖V0‖ ^ 2 + (G2q : ℝ) * ‖V1‖ ^ 2 ≤ 2 ^ 212 * A.re := k2
    _ = A.re / 2 ^ 128 * 2 ^ 340 := by ring

end AEGIS.CvSRelRowFormL43V1

#print axioms AEGIS.CvSRelRowFormL43V1.Pform_eq
#print axioms AEGIS.CvSRelRowFormL43V1.midpoint_ge
