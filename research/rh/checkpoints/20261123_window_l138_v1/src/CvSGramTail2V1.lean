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
import CvSGramTailV1

/-!
# The Gram tail with a sharp diagonal

`CvSGramTailV1.gramUp NP` puts `1/(NP + 1/2 − n) + 1/(NP + 1/2 + n)` on the diagonal, an upper bound for
`ψ'(NP + 1 − n) + ψ'(NP + 1 + n)` that is high by about `1/(12 (NP − n)³)` per side. In the row certificates
this excess acts like a diagonal term of up to `100 K'` near `|n| = KK` at `NP = 2000` (`L = 13/8`) and is
what forced `NP = 8000` there. Here the diagonal is

  `psiUp x = 1/x + 1/(2x²) + 1/(6x³)`,   `psiUp x − psiUp (x + 1) − 1/x² = 1/(6x³(x+1)³) > 0`  (`psiUp_step`),

so `Σ_{j ≥ x} 1/j² ≤ psiUp x` by telescoping, high by about `1/(30x⁵)` (`sum_inv_sub_sq_le2`). The off-diagonal
entries are those of `gramUp`. With `gramUp2` in place of `gramUp`: `gram_tail_le2`, `gramTail2` and
`rows_gram_le2`, the same statements as in `CvSGramTailV1`. (Mirror, `L = 13/8`, `T = 19`, 721 atoms: scaled
`λ_min` +3.9e-11 at `NP = 1500`, against −1.2e-10 at `NP = 4000` with `gramUp`.) Not RH.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSGramTail2V1

open AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSGramTailV1

/-- `psiUp x = 1/x + 1/(2x²) + 1/(6x³)`, an upper bound for `ψ'(x) = Σ_{j ≥ 0} 1/(x + j)²`. -/
def psiUp (x : ℝ) : ℝ := 1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3)

/-- The telescoping step: `psiUp x − psiUp (x + 1) = 1/x² + 1/(6x³(x+1)³)`. -/
theorem psiUp_sub_eq {x : ℝ} (hx : 0 < x) :
    psiUp x - psiUp (x + 1) = 1 / x ^ 2 + 1 / (6 * x ^ 3 * (x + 1) ^ 3) := by
  have h1 : x + 1 ≠ 0 := by positivity
  simp only [psiUp]
  field_simp
  ring

theorem psiUp_step {x : ℝ} (hx : 0 < x) : 1 / x ^ 2 ≤ psiUp x - psiUp (x + 1) := by
  rw [psiUp_sub_eq hx]
  have : 0 ≤ 1 / (6 * x ^ 3 * (x + 1) ^ 3) := by positivity
  linarith

theorem psiUp_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ psiUp x := by
  simp only [psiUp]; positivity

/-- `Σ_{NP<k≤N} 1/(k − u)² ≤ psiUp (NP − u + 1)` for `u ≤ NP`. -/
theorem sum_inv_sub_sq_le2 {u : ℤ} {NP : ℕ} (hu : u ≤ NP) (N : ℕ) :
    ∑ k ∈ Finset.Ioc NP N, 1 / ((k : ℝ) - u) ^ 2 ≤ psiUp ((NP : ℝ) - u + 1) := by
  have hu' : (u : ℝ) ≤ NP := by exact_mod_cast hu
  rcases le_or_gt NP N with hN | hN
  · set g : ℕ → ℝ := fun k => psiUp ((k : ℝ) - u + 1)
    have h := sum_Ioc_telescope (f := fun k => 1 / ((k : ℝ) - u) ^ 2) (g := g) hN fun k hk => by
      have hk1 : (NP : ℝ) + 1 ≤ k := by
        have : NP + 1 ≤ k := hk
        exact_mod_cast this
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      simp only [g, hcast]
      have hc : (0 : ℝ) < k - u := by linarith
      rw [show (k : ℝ) - 1 - u + 1 = k - u by ring]
      exact psiUp_step hc
    have hgN : 0 ≤ g N := by
      simp only [g]
      have : (NP : ℝ) ≤ N := by exact_mod_cast hN
      exact psiUp_nonneg (by linarith)
    have hg : g NP = psiUp ((NP : ℝ) - u + 1) := rfl
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact psiUp_nonneg (by linarith)

/-- `gramUp` with the diagonal `psiUp (NP + 1 − n) + psiUp (NP + 1 + n)`. -/
def gramUp2 (NP : ℕ) (n n' : ℤ) : ℝ :=
  if n = n' then psiUp ((NP : ℝ) - n + 1) + psiUp ((NP : ℝ) + n + 1) else gramUp NP n n'

theorem gramUp2_off {NP : ℕ} {n n' : ℤ} (h : n ≠ n') : gramUp2 NP n n' = gramUp NP n n' := by
  rw [gramUp2, if_neg h]

theorem gramN_diag_le2 {NP : ℕ} {n : ℤ} (hn : |(n : ℝ)| < NP) (N : ℕ) :
    gramN NP N n n ≤ gramUp2 NP n n := by
  have h1 : n ≤ (NP : ℤ) := by
    have : (n : ℝ) < NP := lt_of_le_of_lt (le_abs_self _) hn
    exact_mod_cast this.le
  have h2 : -n ≤ (NP : ℤ) := by
    have : -(n : ℝ) < NP := lt_of_le_of_lt (neg_le_abs _) hn
    exact_mod_cast this.le
  rw [gramN, tail_sum_eq, Finset.sum_add_distrib, gramUp2, if_pos rfl]
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
  have := sum_inv_sub_sq_le2 h1 N
  have := sum_inv_sub_sq_le2 h2 N
  push_cast at this
  rw [show (NP : ℝ) + n + 1 = NP - -n + 1 by ring]
  linarith

/-- **The Gram tail with the sharp diagonal.** -/
theorem gram_tail_le2 {F : Finset ℤ} {R NP : ℕ} (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP)
    (v : ℤ → ℂ) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖∑ n ∈ F, v n * (wt n m : ℂ)‖ ^ 2 ≤ gform F v (gramUp2 NP) := by
  set E : ℕ → ℝ := fun N => ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
    ‖∑ n ∈ F, v n * (wt n m : ℂ)‖ ^ 2 with hE
  set C := (∑ n ∈ F, ‖v n‖) ^ 2
  have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
  have hmono : ∀ N', N ≤ N' → E N ≤ E N' := fun N' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      omega) fun _ _ _ => sq_nonneg _
  have hbound : ∀ N', NP ≤ N' → E N' ≤ gform F v (gramUp2 NP) + 2 / ((N' : ℝ) - R) * C :=
    fun N' hN' => by
      have hNR : (R : ℝ) < N' := lt_of_lt_of_le hR (by exact_mod_cast hN')
      simp only [hE]
      rw [tail_energy_eq]
      refine gform_le F v (by have : (0 : ℝ) < N' - R := by linarith
                              positivity)
        (fun n hn => gramN_diag_le2 (lt_of_le_of_lt (hF n hn) hR) N')
        (fun n hn n' hn' hne => by
          rw [gramUp2_off hne]
          exact gramN_off_le hRNP (hF n hn) (hF n' hn') hne hN')
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
    _ ≤ gform F v (gramUp2 NP) + 2 / (((max N NP + K : ℕ) : ℝ) - R) * C := hbound _ hN'
    _ ≤ gform F v (gramUp2 NP) + δ := by linarith

/-- `gramTail` with `gramUp2`: `(L/π)² ((1 + ε) ⟨aτ, G₂ aτ⟩ + (1 + 1/ε) T² ⟨a, G₂ a⟩)`. -/
def gramTail2 (M : ℕ) (L : ℝ) (F : Finset ℤ) (a : ℤ → ℂ) (T ε : ℝ) (NP : ℕ) : ℝ :=
  (L / Real.pi) ^ 2 * ((1 + ε) * gform F (fun n => a n * (tau M L n : ℂ)) (gramUp2 NP) +
    (1 + 1 / ε) * T ^ 2 * gform F a (gramUp2 NP))

/-- **The tail of the rows from the sharp Gram kernel**, with `|τ_m| ≤ T` only for `|m| > NP`. -/
theorem rows_gram_le2 (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} {R NP : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP) (a : ℤ → ℂ) {T : ℝ}
    (hT : ∀ m : ℤ, NP < m.natAbs → |tau M L m| ≤ T) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖crossRow M L F a m‖ ^ 2 ≤ gramTail2 M L F a T ε NP := by
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
      have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
      linarith
    rw [crossRow_eq_sub M hL a hmF, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hLπ]
    exact mul_le_mul_of_nonneg_left (norm_sub_mul_sq_le _ _ (hT m hm') hε) (sq_nonneg _)
  have hε' : 0 ≤ 1 + 1 / ε := by
    have := one_div_pos.mpr hε
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, gramTail2]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (gram_tail_le2 hF hRNP (fun n => a n * (tau M L n : ℂ)) N)
      (by linarith))
    (mul_le_mul_of_nonneg_left (gram_tail_le2 hF hRNP a N) (mul_nonneg hε' (sq_nonneg T)))

/-- `gramUp2` is below `gramUp` (the same kernel with a smaller diagonal). -/
theorem gramUp2_diag_le {NP : ℕ} {n : ℤ} (hn : |(n : ℝ)| < NP) : gramUp2 NP n n ≤ gramUp NP n n := by
  have h1 : (0 : ℝ) < NP - n + 1 / 2 := by
    have := le_abs_self (n : ℝ); linarith
  have h2 : (0 : ℝ) < NP + n + 1 / 2 := by
    have := neg_abs_le (n : ℝ); linarith
  have key : ∀ x : ℝ, 0 < x - 1 / 2 → psiUp x ≤ 1 / (x - 1 / 2) := fun x hx => by
    have hx0 : 0 < x := by linarith
    simp only [psiUp]
    rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) hx]
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, pow_pos hx0 5, pow_pos hx0 6]
  rw [gramUp2, gramUp, if_pos rfl, if_pos rfl]
  have k1 := key ((NP : ℝ) - n + 1) (by linarith)
  have k2 := key ((NP : ℝ) + n + 1) (by linarith)
  rw [show (NP : ℝ) - n + 1 - 1 / 2 = NP - n + 1 / 2 by ring] at k1
  rw [show (NP : ℝ) + n + 1 - 1 / 2 = NP + n + 1 / 2 by ring] at k2
  linarith

/-- The form of `gramUp2` is below that of `gramUp`. -/
theorem gform_gramUp2_le {F : Finset ℤ} {R NP : ℕ} (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP)
    (v : ℤ → ℂ) : gform F v (gramUp2 NP) ≤ gform F v (gramUp NP) := by
  have hR : (R : ℝ) < NP := by exact_mod_cast hRNP
  have h := gform_le F v (G₁ := gramUp2 NP) (G₂ := gramUp NP) le_rfl
    (fun n hn => gramUp2_diag_le (lt_of_le_of_lt (hF n hn) hR))
    (fun n _ n' _ hne => by rw [gramUp2_off hne, sub_self, abs_zero])
  simpa using h

/-- **Every `gramTail` budget is a `gramTail2` budget.** -/
theorem gramTail2_le (M : ℕ) (L : ℝ) {F : Finset ℤ} {R NP : ℕ} (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R)
    (hRNP : R < NP) (a : ℤ → ℂ) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    gramTail2 M L F a T ε NP ≤ gramTail M L F a T ε NP := by
  have hε' : 0 ≤ 1 + 1 / ε := by
    have := one_div_pos.mpr hε
    linarith
  rw [gramTail2, gramTail]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left (gform_gramUp2_le hF hRNP _) (by linarith)
  · exact mul_le_mul_of_nonneg_left (gform_gramUp2_le hF hRNP _) (mul_nonneg hε' (sq_nonneg T))

/-! ### The integer table of the diagonal -/

/-- `psiq x = ⌊2^128/x⌋ + ⌊2^127/x²⌋ + ⌊2^128/(6x³)⌋`, the table entry of `2^128 psiUp x`. -/
def psiq (x : ℤ) : ℤ := 2 ^ 128 / x + 2 ^ 127 / (x * x) + 2 ^ 128 / (6 * x ^ 3)

theorem ediv_real_err (a d : ℤ) (hd : 0 < d) : |((a / d : ℤ) : ℝ) - (a : ℝ) / d| ≤ 1 := by
  have h1 := Int.ediv_mul_le a hd.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have r1 : ((a / d : ℤ) : ℝ) * d ≤ a := by exact_mod_cast h1
  have r2 : (a : ℝ) < (((a / d : ℤ) : ℝ) + 1) * d := by exact_mod_cast h2
  have u1 : ((a / d : ℤ) : ℝ) ≤ (a : ℝ) / d := by rw [le_div_iff₀ hd']; exact r1
  have u2 : (a : ℝ) / d < ((a / d : ℤ) : ℝ) + 1 := by rw [div_lt_iff₀ hd']; exact r2
  rw [abs_le]
  constructor <;> linarith

/-- **`psiq` is `2^128 psiUp` within 3.** -/
theorem psiq_err {x : ℤ} (hx : 0 < x) : |(psiq x : ℝ) - 2 ^ 128 * psiUp (x : ℝ)| ≤ 3 := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have e1 := ediv_real_err (2 ^ 128) x hx
  have e2 := ediv_real_err (2 ^ 127) (x * x) (by positivity)
  have e3 := ediv_real_err (2 ^ 128) (6 * x ^ 3) (by positivity)
  have e : (psiq x : ℝ) - 2 ^ 128 * psiUp (x : ℝ) =
      ((((2 ^ 128 / x : ℤ) : ℝ) - ((2 ^ 128 : ℤ) : ℝ) / (x : ℝ)) +
        ((((2 ^ 127 / (x * x)) : ℤ) : ℝ) - ((2 ^ 127 : ℤ) : ℝ) / ((x * x : ℤ) : ℝ)) +
        ((((2 ^ 128 / (6 * x ^ 3)) : ℤ) : ℝ) - ((2 ^ 128 : ℤ) : ℝ) / ((6 * x ^ 3 : ℤ) : ℝ))) := by
    simp only [psiq, psiUp]
    push_cast
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := abs_add_le (((2 ^ 128 / x : ℤ) : ℝ) - ((2 ^ 128 : ℤ) : ℝ) / (x : ℝ))
    ((((2 ^ 127 / (x * x)) : ℤ) : ℝ) - ((2 ^ 127 : ℤ) : ℝ) / ((x * x : ℤ) : ℝ))
  linarith

/-! ### Symmetry and size of the kernel -/

theorem gramUp_symm (NP : ℕ) (n m : ℤ) : gramUp NP n m = gramUp NP m n := by
  simp only [gramUp]
  by_cases h : n = m
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hd : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hd' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm h)
    rw [div_eq_div_iff hd hd']
    ring

theorem gramUp2_symm (NP : ℕ) (n m : ℤ) : gramUp2 NP n m = gramUp2 NP m n := by
  by_cases h : n = m
  · subst h; rfl
  · rw [gramUp2_off h, gramUp2_off (Ne.symm h), gramUp_symm]

theorem psiUp_le_one {x : ℝ} (hx : 2 ≤ x) : psiUp x ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have h2 : 1 / (2 * x ^ 2) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : 1 / (6 * x ^ 3) ≤ 1 / 48 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  simp only [psiUp]; linarith

theorem gramUp2_diag (NP : ℕ) (n : ℤ) :
    gramUp2 NP n n = psiUp ((NP : ℝ) - n + 1) + psiUp ((NP : ℝ) + n + 1) := by
  rw [gramUp2, if_pos rfl]

/-- On `|n| ≤ NP − 1` the diagonal is in `[0, 2]`. -/
theorem gramUp2_diag_abs_le {NP : ℕ} {n : ℤ} (hn : |(n : ℝ)| + 1 ≤ NP) : |gramUp2 NP n n| ≤ 2 := by
  have h1 := le_abs_self (n : ℝ)
  have h2 := neg_abs_le (n : ℝ)
  have p1 := psiUp_le_one (x := (NP : ℝ) - n + 1) (by linarith)
  have p2 := psiUp_le_one (x := (NP : ℝ) + n + 1) (by linarith)
  have q1 := psiUp_nonneg (x := (NP : ℝ) - n + 1) (by linarith)
  have q2 := psiUp_nonneg (x := (NP : ℝ) + n + 1) (by linarith)
  rw [gramUp2_diag, abs_of_nonneg (by linarith)]
  linarith

end AEGIS.CvSGramTail2V1

#print axioms AEGIS.CvSGramTail2V1.psiUp_step
#print axioms AEGIS.CvSGramTail2V1.sum_inv_sub_sq_le2
#print axioms AEGIS.CvSGramTail2V1.gram_tail_le2
#print axioms AEGIS.CvSGramTail2V1.rows_gram_le2
#print axioms AEGIS.CvSGramTail2V1.gramUp2_diag_le
#print axioms AEGIS.CvSGramTail2V1.gramTail2_le
#print axioms AEGIS.CvSGramTail2V1.psiq_err
#print axioms AEGIS.CvSGramTail2V1.gramUp2_symm
#print axioms AEGIS.CvSGramTail2V1.gramUp2_diag_abs_le
