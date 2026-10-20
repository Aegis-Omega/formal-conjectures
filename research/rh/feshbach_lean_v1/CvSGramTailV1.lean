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
import CvSRowTailV1

/-!
# The Gram tail of the cross rows (CvS step 6k)

For `F ⊆ [−R, R]`, `R < NP` and any `v`, the rows `|m| > NP` of the Hilbert-type operator
`v ↦ (Σ_n v_n/(n − m))_m` have total energy at most the Hermitian form of the rational kernel
`gramUp NP` (`gram_tail_le`):

  `Σ_{NP<|m|≤N} |Σ_n v_n/(n − m)|² ≤ Re Σ_{n,n'} v_n conj(v_n') gramUp NP n n'`,

with `gramUp NP n n' = (H(NP−n') − H(NP−n) + H(NP+n) − H(NP+n'))/(n − n')` off the diagonal
(`H` the harmonic numbers; this is the exact value of `Σ_{|m|>NP} 1/((m−n)(m−n'))`) and
`1/(NP + 1/2 − n) + 1/(NP + 1/2 + n)` on it (an upper bound for `ψ'(NP+1−n) + ψ'(NP+1+n)`).
The finite sums differ from the kernel by `O(1/(N − R))` off the diagonal and are below it on
the diagonal; letting `N' → ∞` gives the bound for every `N`.

Writing a row off `F` as `(L/π)(X_m − τ_m Y_m)` with `X = Σ a_n τ_n/(n − m)`,
`Y = Σ a_n/(n − m)` (`crossRow_off`) and `|τ_m| ≤ T` for `|m| > NP` gives the row tail
`gramTail` (`rows_gram_le`), and `window_of_certificate_gram` is
`CvSRowTailV1.window_of_certificate_tail` with `rowTail` replaced by `gramTail`. Not RH.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSGramTailV1

open AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1

/-- Harmonic numbers on `ℤ`: `H u = Σ_{1 ≤ j ≤ u} 1/j` (`0` for `u ≤ 0`). -/
def H (u : ℤ) : ℝ := (harmonic u.toNat : ℝ)

theorem H_succ {u : ℤ} (hu : 0 ≤ u) : H (u + 1) = H u + 1 / ((u : ℝ) + 1) := by
  have h1 : (u + 1).toNat = u.toNat + 1 := by omega
  have h2 : ((u.toNat : ℕ) : ℝ) = u := by exact_mod_cast Int.toNat_of_nonneg hu
  simp only [H, h1, harmonic_succ]
  push_cast
  rw [h2, one_div]

/-- `0 ≤ H(a + t) − H a ≤ t/c` when every new term `1/j` has `j ≥ c`. -/
theorem H_add_le {a : ℤ} (ha : 0 ≤ a) {c : ℝ} (hc : 0 < c) (hca : c ≤ (a : ℝ) + 1) (t : ℕ) :
    0 ≤ H (a + t) - H a ∧ H (a + t) - H a ≤ t / c := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := H_succ (u := a + t) (by omega)
    have e : a + ((t + 1 : ℕ) : ℤ) = a + t + 1 := by push_cast; ring
    rw [e, hs]
    have hat : (c : ℝ) ≤ ((a + t : ℤ) : ℝ) + 1 := by
      push_cast
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
    have hpos : 0 < ((a + t : ℤ) : ℝ) + 1 := lt_of_lt_of_le hc hat
    have hle : 1 / (((a + t : ℤ) : ℝ) + 1) ≤ 1 / c := one_div_le_one_div_of_le hc hat
    have h0 : 0 ≤ 1 / (((a + t : ℤ) : ℝ) + 1) := by positivity
    push_cast at ih hle h0 ⊢
    constructor
    · linarith [ih.1]
    · have : (t : ℝ) / c + 1 / c = ((t : ℝ) + 1) / c := by ring
      linarith [ih.2]

/-- `|H x − H y| ≤ |x − y|/c` when `x, y ≥ c − 1 ≥ 0`. -/
theorem H_sub_abs_le {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) {c : ℝ} (hc : 0 < c)
    (hcx : c ≤ (x : ℝ) + 1) (hcy : c ≤ (y : ℝ) + 1) :
    |H x - H y| ≤ |(x : ℝ) - y| / c := by
  rcases le_total y x with h | h
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, x = y + t := ⟨(x - y).toNat, by omega⟩
    have := H_add_le hy hc hcy t
    rw [abs_of_nonneg this.1]
    push_cast
    rw [show (y : ℝ) + t - y = t by ring, abs_of_nonneg (Nat.cast_nonneg t)]
    exact this.2
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, y = x + t := ⟨(y - x).toNat, by omega⟩
    have := H_add_le hx hc hcx t
    rw [abs_sub_comm, abs_of_nonneg this.1]
    push_cast
    rw [show (x : ℝ) - (x + t) = -t by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg t)]
    exact this.2

/-- `Σ_{NP<k≤N} 1/(k − u) = H(N − u) − H(NP − u)` for `u ≤ NP`. -/
theorem sum_inv_sub {u : ℤ} {NP : ℕ} (hu : u ≤ NP) {N : ℕ} (hN : NP ≤ N) :
    ∑ k ∈ Finset.Ioc NP N, 1 / ((k : ℝ) - u) = H (N - u) - H (NP - u) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, ih]
    have e : ((N + 1 : ℕ) : ℤ) - u = ((N : ℤ) - u) + 1 := by push_cast; ring
    rw [e, H_succ (by omega)]
    push_cast
    ring

/-- `Σ_{NP<k≤N} 1/(k − u)² ≤ 1/(NP − u + 1/2)` for `u ≤ NP`. -/
theorem sum_inv_sub_sq_le {u : ℤ} {NP : ℕ} (hu : u ≤ NP) (N : ℕ) :
    ∑ k ∈ Finset.Ioc NP N, 1 / ((k : ℝ) - u) ^ 2 ≤ 1 / ((NP : ℝ) - u + 1 / 2) := by
  have hu' : (u : ℝ) ≤ NP := by exact_mod_cast hu
  rcases le_or_gt NP N with hN | hN
  · set g : ℕ → ℝ := fun k => 1 / ((k : ℝ) - u + 1 / 2)
    have h := sum_Ioc_telescope (f := fun k => 1 / ((k : ℝ) - u) ^ 2) (g := g) hN fun k hk => by
      have hk1 : (NP : ℝ) + 1 ≤ k := by
        have : NP + 1 ≤ k := hk
        exact_mod_cast this
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      simp only [g, hcast]
      have ha : (0 : ℝ) < k - 1 - u + 1 / 2 := by linarith
      have hb : (0 : ℝ) < k - u + 1 / 2 := by linarith
      have hc : (0 : ℝ) < k - u := by linarith
      rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hgN : 0 ≤ g N := by
      simp only [g]
      have : (NP : ℝ) ≤ N := by exact_mod_cast hN
      have : (0 : ℝ) < N - u + 1 / 2 := by linarith
      positivity
    have hg : g NP = 1 / ((NP : ℝ) - u + 1 / 2) := rfl
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have : (0 : ℝ) < NP - u + 1 / 2 := by linarith
    positivity

/-- A sum over `NP < |m| ≤ N` is a sum over `k ∈ (NP, N]` of the values at `±k`. -/
theorem tail_sum_eq {β : Type*} [AddCommMonoid β] (g : ℤ → β) (NP N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), g m =
      ∑ k ∈ Finset.Ioc NP N, (g k + g (-(k : ℤ))) := by
  rw [Finset.sum_add_distrib]
  have hA : ∑ k ∈ Finset.Ioc NP N, g (k : ℤ) =
      ∑ m ∈ (Finset.Ioc NP N).image (fun k : ℕ => (k : ℤ)), g m := by
    rw [Finset.sum_image fun x _ y _ h => by exact_mod_cast h]
  have hB : ∑ k ∈ Finset.Ioc NP N, g (-(k : ℤ)) =
      ∑ m ∈ (Finset.Ioc NP N).image (fun k : ℕ => -(k : ℤ)), g m := by
    rw [Finset.sum_image fun x _ y _ h => by simpa using h]
  rw [hA, hB, ← Finset.sum_union]
  · congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases Int.natAbs_eq m with h | h
      · exact Or.inl ⟨m.natAbs, ⟨h3, by omega⟩, h.symm⟩
      · exact Or.inr ⟨m.natAbs, ⟨h3, by omega⟩, by omega⟩
    · rintro (⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
      · exact ⟨⟨by omega, by omega⟩, by simpa using hk1⟩
      · exact ⟨⟨by omega, by omega⟩, by simpa using hk1⟩
  · rw [Finset.disjoint_left]
    intro m hA hB
    simp only [Finset.mem_image, Finset.mem_Ioc] at hA hB
    obtain ⟨k, ⟨hk1, -⟩, rfl⟩ := hA
    obtain ⟨k', ⟨hk1', -⟩, h⟩ := hB
    omega

/-- `|Σ_n v_n w_n|² = Re Σ_{n,n'} v_n conj(v_n') w_n w_n'` for real weights `w`. -/
theorem norm_sq_sum_eq (F : Finset ℤ) (v : ℤ → ℂ) (w : ℤ → ℝ) :
    ‖∑ n ∈ F, v n * (w n : ℂ)‖ ^ 2 =
      (∑ n ∈ F, ∑ n' ∈ F, v n * conj (v n') * ((w n * w n' : ℝ) : ℂ)).re := by
  rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
    Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The Hermitian form `Re Σ_{n,n'} v_n conj(v_n') G(n, n')` of a real kernel `G`. -/
def gform (F : Finset ℤ) (v : ℤ → ℂ) (G : ℤ → ℤ → ℝ) : ℝ :=
  (∑ n ∈ F, ∑ n' ∈ F, v n * conj (v n') * (G n n' : ℂ)).re

/-- **Comparison of Hermitian forms**: below on the diagonal and within `δ` off it. -/
theorem gform_le (F : Finset ℤ) (v : ℤ → ℂ) {G₁ G₂ : ℤ → ℤ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ n ∈ F, G₁ n n ≤ G₂ n n)
    (ho : ∀ n ∈ F, ∀ n' ∈ F, n ≠ n' → |G₁ n n' - G₂ n n'| ≤ δ) :
    gform F v G₁ ≤ gform F v G₂ + δ * (∑ n ∈ F, ‖v n‖) ^ 2 := by
  have hsplit : gform F v G₁ = gform F v G₂ +
      ∑ n ∈ F, ∑ n' ∈ F, (v n * conj (v n') * ((G₁ n n' - G₂ n n' : ℝ) : ℂ)).re := by
    simp only [gform, ← Complex.re_sum, ← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    push_cast
    ring
  have hterm : ∀ n ∈ F, ∀ n' ∈ F,
      (v n * conj (v n') * ((G₁ n n' - G₂ n n' : ℝ) : ℂ)).re ≤ δ * (‖v n‖ * ‖v n'‖) := by
    intro n hn n' hn'
    by_cases h : n = n'
    · subst h
      rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      have h1 : G₁ n n - G₂ n n ≤ 0 := by linarith [hd n hn]
      have h2 : 0 ≤ Complex.normSq (v n) := Complex.normSq_nonneg _
      nlinarith [mul_nonneg hδ (mul_nonneg (norm_nonneg (v n)) (norm_nonneg (v n)))]
    · refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have := ho n hn n' hn' h
      have h0 : 0 ≤ ‖v n‖ * ‖v n'‖ := by positivity
      nlinarith
  rw [hsplit, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n' hn' => hterm n hn n' hn'

/-- The weight `1/(n − m)` of the Hilbert-type rows. -/
abbrev wt (n m : ℤ) : ℝ := 1 / ((n : ℝ) - m)

/-- The kernel of the rows `|m| > NP`: off the diagonal the exact value of
`Σ_{|m|>NP} 1/((m − n)(m − n'))`, on it an upper bound. -/
def gramUp (NP : ℕ) (n n' : ℤ) : ℝ :=
  if n = n' then 1 / ((NP : ℝ) - n + 1 / 2) + 1 / ((NP : ℝ) + n + 1 / 2)
  else (H (NP - n') - H (NP - n) + (H (NP + n) - H (NP + n'))) / ((n : ℝ) - n')

/-- The finite kernel of the rows `NP < |m| ≤ N`. -/
def gramN (NP N : ℕ) (n n' : ℤ) : ℝ :=
  ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), wt n m * wt n' m

theorem tail_energy_eq (F : Finset ℤ) (v : ℤ → ℂ) (NP N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖∑ n ∈ F, v n * (wt n m : ℂ)‖ ^ 2 = gform F v (gramN NP N) := by
  simp_rw [norm_sq_sum_eq F v (fun n => wt _ _)]
  rw [← Complex.re_sum, gform]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [gramN, ← Finset.mul_sum, Complex.ofReal_sum]

theorem gramN_diag_le {NP : ℕ} {n : ℤ} (hn : |(n : ℝ)| < NP) (N : ℕ) :
    gramN NP N n n ≤ gramUp NP n n := by
  have h1 : n ≤ (NP : ℤ) := by
    have : (n : ℝ) < NP := lt_of_le_of_lt (le_abs_self _) hn
    exact_mod_cast this.le
  have h2 : -n ≤ (NP : ℤ) := by
    have : -(n : ℝ) < NP := lt_of_le_of_lt (neg_le_abs _) hn
    exact_mod_cast this.le
  rw [gramN, tail_sum_eq, Finset.sum_add_distrib, gramUp, if_pos rfl]
  have e1 : ∀ k : ℕ, wt n k * wt n k = 1 / ((k : ℝ) - n) ^ 2 := fun k => by
    simp only [wt, Int.cast_natCast]
    rw [div_mul_div_comm, one_mul, ← sq, sub_sq_comm]
  have e2 : ∀ k : ℕ, wt n (-(k : ℤ)) * wt n (-(k : ℤ)) = 1 / ((k : ℝ) - -(n : ℝ)) ^ 2 :=
    fun k => by
      simp only [wt]
      push_cast
      rw [div_mul_div_comm, one_mul, ← sq]
      congr 1
      ring
  simp_rw [e1, e2]
  have := sum_inv_sub_sq_le h1 N
  have := sum_inv_sub_sq_le h2 N
  push_cast at this
  rw [show (NP : ℝ) + n + 1 / 2 = NP - -n + 1 / 2 by ring]
  linarith

/-- Off the diagonal the finite kernel is within `2/(N − R)` of `gramUp`. -/
theorem gramN_off_le {R NP : ℕ} (hRNP : R < NP) {n n' : ℤ} (hn : |(n : ℝ)| ≤ R)
    (hn' : |(n' : ℝ)| ≤ R) (hne : n ≠ n') {N : ℕ} (hN : NP ≤ N) :
    |gramN NP N n n' - gramUp NP n n'| ≤ 2 / ((N : ℝ) - R) := by
  have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
  have hNR : (NP : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hn1, hn2⟩ := abs_le.mp hn
  obtain ⟨hn1', hn2'⟩ := abs_le.mp hn'
  have hd : ((n : ℝ) - n') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have toZ : ∀ x : ℤ, (x : ℝ) ≤ NP → x ≤ (NP : ℤ) := fun x h => by exact_mod_cast h
  have i1 := toZ n (by linarith)
  have i2 := toZ n' (by linarith)
  have i3 := toZ (-n) (by push_cast; linarith)
  have i4 := toZ (-n') (by push_cast; linarith)
  have hk : ∀ k ∈ Finset.Ioc NP N, wt n k * wt n' k + wt n (-(k : ℤ)) * wt n' (-(k : ℤ)) =
      (1 / ((n : ℝ) - n')) * ((1 / ((k : ℝ) - n) - 1 / ((k : ℝ) - n')) -
        (1 / ((k : ℝ) - ((-n : ℤ) : ℝ)) - 1 / ((k : ℝ) - ((-n' : ℤ) : ℝ)))) := by
    intro k hk
    have hk' : (NP : ℝ) < k := by
      have := (Finset.mem_Ioc.mp hk).1
      exact_mod_cast this
    have a1 : (n : ℝ) - k ≠ 0 := by linarith
    have a2 : (n' : ℝ) - k ≠ 0 := by linarith
    have a3 : (n : ℝ) + k ≠ 0 := by linarith
    have a4 : (n' : ℝ) + k ≠ 0 := by linarith
    have b1 : (k : ℝ) - n ≠ 0 := by linarith
    have b2 : (k : ℝ) - n' ≠ 0 := by linarith
    have b3 : (k : ℝ) + n ≠ 0 := by linarith
    have b4 : (k : ℝ) + n' ≠ 0 := by linarith
    simp only [wt]
    push_cast
    simp only [sub_neg_eq_add]
    field_simp
    ring
  have hsum : gramN NP N n n' = (1 / ((n : ℝ) - n')) *
      ((H (N - n) - H (NP - n) - (H (N - n') - H (NP - n'))) -
        (H (N - -n) - H (NP - -n) - (H (N - -n') - H (NP - -n')))) := by
    rw [gramN, tail_sum_eq, Finset.sum_congr rfl hk, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_inv_sub i1 hN, sum_inv_sub i2 hN,
      sum_inv_sub i3 hN, sum_inv_sub i4 hN]
  set A := H (N - n) - H (N - n')
  set B := H (N + n') - H (N + n)
  have hdiff : gramN NP N n n' - gramUp NP n n' = (A + B) / ((n : ℝ) - n') := by
    rw [hsum, gramUp, if_neg hne]
    simp only [A, B, sub_neg_eq_add]
    field_simp
    ring
  have hc : (0 : ℝ) < N - R := by linarith
  have hA : |A| ≤ |(n : ℝ) - n'| / ((N : ℝ) - R) := by
    have := H_sub_abs_le (x := N - n) (y := N - n') (by omega) (by omega) hc
      (by push_cast; linarith) (by push_cast; linarith)
    push_cast at this
    rwa [show (N : ℝ) - n - (N - n') = -((n : ℝ) - n') by ring, abs_neg] at this
  have hB : |B| ≤ |(n : ℝ) - n'| / ((N : ℝ) - R) := by
    have := H_sub_abs_le (x := N + n') (y := N + n) (by omega) (by omega) hc
      (by push_cast; linarith) (by push_cast; linarith)
    push_cast at this
    rwa [show (N : ℝ) + n' - (N + n) = -((n : ℝ) - n') by ring, abs_neg] at this
  have hpos : 0 < |(n : ℝ) - n'| := abs_pos.mpr hd
  rw [hdiff, abs_div, div_le_iff₀ hpos]
  calc |A + B| ≤ |A| + |B| := abs_add_le A B
    _ ≤ |(n : ℝ) - n'| / ((N : ℝ) - R) + |(n : ℝ) - n'| / ((N : ℝ) - R) := add_le_add hA hB
    _ = 2 / ((N : ℝ) - R) * |(n : ℝ) - n'| := by ring

/-- **The Gram tail.** For `F ⊆ [−R, R]` and `R < NP`, the rows `NP < |m| ≤ N` of
`v ↦ Σ_n v_n/(n − m)` have total energy at most the form of `gramUp NP`, for every `N`. -/
theorem gram_tail_le {F : Finset ℤ} {R NP : ℕ} (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP)
    (v : ℤ → ℂ) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖∑ n ∈ F, v n * (wt n m : ℂ)‖ ^ 2 ≤ gform F v (gramUp NP) := by
  set E : ℕ → ℝ := fun N => ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
    ‖∑ n ∈ F, v n * (wt n m : ℂ)‖ ^ 2 with hE
  set C := (∑ n ∈ F, ‖v n‖) ^ 2
  have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
  have hmono : ∀ N', N ≤ N' → E N ≤ E N' := fun N' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      omega) fun _ _ _ => sq_nonneg _
  have hbound : ∀ N', NP ≤ N' → E N' ≤ gform F v (gramUp NP) + 2 / ((N' : ℝ) - R) * C :=
    fun N' hN' => by
      have hNR : (R : ℝ) < N' := lt_of_lt_of_le hR (by exact_mod_cast hN')
      simp only [hE]
      rw [tail_energy_eq]
      refine gform_le F v (by have : (0 : ℝ) < N' - R := by linarith
                              positivity)
        (fun n hn => gramN_diag_le (lt_of_le_of_lt (hF n hn) hR) N')
        (fun n hn n' hn' hne => gramN_off_le hRNP (hF n hn) (hF n' hn') hne hN')
  have hC : 0 ≤ C := sq_nonneg _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * C / δ)
  have hN' : NP ≤ max N NP + K := le_trans (le_max_right N NP) (Nat.le_add_right _ _)
  have hNN : N ≤ max N NP + K := le_trans (le_max_left N NP) (Nat.le_add_right _ _)
  have hgap : (K : ℝ) + 1 ≤ ((max N NP + K : ℕ) : ℝ) - R := by
    have : (NP : ℝ) ≤ max (N : ℝ) NP := le_max_right _ _
    push_cast
    have : (R : ℝ) + 1 ≤ NP := by exact_mod_cast hRNP
    linarith
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hsmall : 2 / (((max N NP + K : ℕ) : ℝ) - R) * C ≤ δ := by
    have h1 : 2 * C / δ < (K : ℝ) + 1 := by linarith
    have h2 : 2 * C < δ * ((K : ℝ) + 1) := by
      rw [div_lt_iff₀ hδ] at h1
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (lt_of_lt_of_le hKpos hgap)]
    nlinarith
  calc E N ≤ E (max N NP + K) := hmono _ hNN
    _ ≤ gform F v (gramUp NP) + 2 / (((max N NP + K : ℕ) : ℝ) - R) * C := hbound _ hN'
    _ ≤ gform F v (gramUp NP) + δ := by linarith

/-- Off `F` a row is `(L/π)(X_m − τ_m Y_m)` with `X_m = Σ a_n τ_n/(n − m)`, `Y_m = Σ a_n/(n − m)`. -/
theorem crossRow_eq_sub (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} (a : ℤ → ℂ) {m : ℤ}
    (hm : m ∉ F) :
    crossRow M L F a m = ((L / Real.pi : ℝ) : ℂ) *
      (∑ n ∈ F, (a n * (tau M L n : ℂ)) * (wt n m : ℂ) -
        (tau M L m : ℂ) * ∑ n ∈ F, a n * (wt n m : ℂ)) := by
  rw [crossRow_off M hL a hm]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnm : ((n : ℝ) - m) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast fun h : n = m => hm (h ▸ hn))
  simp only [wt]
  push_cast
  field_simp

/-- `‖x − t y‖² ≤ (1 + ε)‖x‖² + (1 + 1/ε) T² ‖y‖²` for `|t| ≤ T`, `ε > 0`. -/
theorem norm_sub_mul_sq_le (x y : ℂ) {t T ε : ℝ} (ht : |t| ≤ T) (hε : 0 < ε) :
    ‖x - (t : ℂ) * y‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 + (1 + 1 / ε) * T ^ 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x - (t : ℂ) * y‖ ≤ ‖x‖ + T * ‖y‖ := by
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  set p := ‖x‖
  set q := T * ‖y‖ with hq
  have hp : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := by positivity
  have key : 2 * p * q - ε * p ^ 2 ≤ q ^ 2 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [sq_nonneg (ε * p - q)]
  have e : (1 + 1 / ε) * T ^ 2 * ‖y‖ ^ 2 = q ^ 2 + q ^ 2 / ε := by
    rw [hq]
    field_simp
  calc ‖x - (t : ℂ) * y‖ ^ 2 ≤ (p + q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (1 + ε) * p ^ 2 + (q ^ 2 + q ^ 2 / ε) := by nlinarith
    _ = _ := by rw [e]

/-- The Gram row tail: `(L/π)² ((1 + ε) ⟨aτ, G aτ⟩ + (1 + 1/ε) T² ⟨a, G a⟩)` with `G = gramUp NP`. -/
def gramTail (M : ℕ) (L : ℝ) (F : Finset ℤ) (a : ℤ → ℂ) (T ε : ℝ) (NP : ℕ) : ℝ :=
  (L / Real.pi) ^ 2 * ((1 + ε) * gform F (fun n => a n * (tau M L n : ℂ)) (gramUp NP) +
    (1 + 1 / ε) * T ^ 2 * gform F a (gramUp NP))

/-- **The tail of the rows from the Gram kernel**, with `|τ_m| ≤ T` only for `|m| > NP`. -/
theorem rows_gram_le (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} {R NP : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP) (a : ℤ → ℂ) {T : ℝ}
    (hT : ∀ m : ℤ, NP < m.natAbs → |tau M L m| ≤ T) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖crossRow M L F a m‖ ^ 2 ≤ gramTail M L F a T ε NP := by
  have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
  have hLπ : 0 ≤ L / Real.pi := (div_pos hL Real.pi_pos).le
  have hpt : ∀ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
      ‖crossRow M L F a m‖ ^ 2 ≤ (L / Real.pi) ^ 2 *
        ((1 + ε) * ‖∑ n ∈ F, (a n * (tau M L n : ℂ)) * (wt n m : ℂ)‖ ^ 2 +
          (1 + 1 / ε) * T ^ 2 * ‖∑ n ∈ F, a n * (wt n m : ℂ)‖ ^ 2) := by
    intro m hm
    have hm' := (Finset.mem_filter.mp hm).2
    have hmF : m ∉ F := fun h => by
      have h1 := hF m h
      have h2 : |(m : ℝ)| = (m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      have h3 : (NP : ℝ) < m.natAbs := by exact_mod_cast hm'
      linarith
    rw [crossRow_eq_sub M hL a hmF, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hLπ]
    exact mul_le_mul_of_nonneg_left (norm_sub_mul_sq_le _ _ (hT m hm') hε) (sq_nonneg _)
  have hε' : 0 ≤ 1 + 1 / ε := by
    have := one_div_pos.mpr hε
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, gramTail]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (gram_tail_le hF hRNP (fun n => a n * (tau M L n : ℂ)) N)
      (by linarith))
    (mul_le_mul_of_nonneg_left (gram_tail_le hF hRNP a N) (mul_nonneg hε' (sq_nonneg T)))

open AEGIS.CvSMomentBasisV1 AEGIS.CvSTraceV1 AEGIS.CvSWindowCertV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3 in
/-- **`window_of_certificate_tail` with the Gram tail.** The rows `|m| ≤ NP` and `gramTail`
(with `|τ_m| ≤ Tτ` for `|m| > NP` only) bound the cross block. -/
theorem window_of_certificate_gram (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin p → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (R NP : ℕ) (hRι : ∀ i, |ι i| + 1 ≤ (R : ℤ)) (hRNP : R < NP)
    {Tτ : ℝ} (hTτ : ∀ x : ℤ, NP < x.natAbs → |tau M LT x| ≤ Tτ) {ε : ℝ} (hε : 0 < ε)
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2) +
      gramTail M LT (lowFreq fun i => sinSqSupport (ι i))
        (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) Tτ ε NP ≤
        Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  set S : Fin p → Finset ℤ := fun i => sinSqSupport (ι i)
  set β : Fin p → ℤ → ℂ := fun i => sinSqWeight (ι i)
  have hF : ∀ n ∈ lowFreq S, |(n : ℝ)| ≤ R := by
    intro n hn
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hn
    have hn' : n = ι i - 1 ∨ n = ι i ∨ n = ι i + 1 := by
      simpa [S, sinSqSupport] using hi
    have h1 := hRι i
    have h2 := neg_abs_le (ι i)
    have h3 := le_abs_self (ι i)
    have hz : |n| ≤ (R : ℤ) := by
      rw [abs_le]
      rcases hn' with h | h | h <;> subst h <;> constructor <;> linarith
    have := (Int.cast_le (R := ℝ)).mpr hz
    rwa [Int.cast_abs, Int.cast_natCast] at this
  refine window_of_certificate_rows M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos lam Brow (fun c N => ?_) hlow g hm r a hw h2r
  have hz : ∀ x : ℤ, NP < x.natAbs → ∑ i, lam c i * atomRow LT S β i x = 0 := by
    intro x hx
    have hxF : x ∉ lowFreq S := fun h => by
      have h1 := hF x h
      have h2 : |(x : ℝ)| = (x.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      have h3 : (NP : ℝ) < x.natAbs := by exact_mod_cast hx
      have h4 : (R : ℝ) < NP := by exact_mod_cast hRNP
      linarith
    exact Finset.sum_eq_zero fun i _ => by rw [atomRow, lowCoeff_eq_zero LT S β _ hxF, mul_zero]
  refine (rows_split hz N).trans ?_
  refine le_trans (add_le_add le_rfl ?_) (hfin c)
  exact rows_gram_le M hLT0 hF hRNP _ hTτ hε N

end AEGIS.CvSGramTailV1

#print axioms AEGIS.CvSGramTailV1.gram_tail_le
#print axioms AEGIS.CvSGramTailV1.rows_gram_le
#print axioms AEGIS.CvSGramTailV1.window_of_certificate_gram
