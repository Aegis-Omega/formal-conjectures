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
# Kronecker-packed dot products

`pack w l = Σ lᵢ 2^(w i)`. For lists `a`, `b` of length `n` with entries at most `A` and `B` and
`2 n A B < 2^w`, the product `pack w a * pack w b.reverse` has no carries, and its digit `n − 1` in base
`2^w` is the dot product `Σ aᵢ bᵢ` (`dot_digit`). The kernel evaluates `Nat.mul`, `Nat.div` and `Nat.mod`
with GMP, so a dot product of a long list costs one big multiplication instead of `n` list steps. This is
step 1 of the Arb ℓ = 9/5 port (`notes/arb_lean_port.md`: Gram and `LDLᵀ` residual checks). Not RH.
-/

open Polynomial Finset

namespace AEGIS.KroneckerDotV1

/-- `Σ lᵢ 2^(w i)`. -/
def pack (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 2 ^ w * pack w l

/-- `Σ lᵢ Xⁱ`. -/
noncomputable def toPoly : List ℕ → ℕ[X]
  | [] => 0
  | a :: l => C a + X * toPoly l

/-- `Σ aᵢ bᵢ`. -/
def dot (a b : List ℕ) : ℕ := (List.zipWith (· * ·) a b).sum

theorem eval_toPoly (w : ℕ) : ∀ l : List ℕ, (toPoly l).eval (2 ^ w) = pack w l
  | [] => by simp [toPoly, pack]
  | a :: l => by simp [toPoly, pack, eval_toPoly w l]

theorem coeff_toPoly : ∀ (l : List ℕ) (i : ℕ), (toPoly l).coeff i = l.getD i 0
  | [], i => by simp [toPoly]
  | a :: l, 0 => by simp [toPoly]
  | a :: l, i + 1 => by simp [toPoly, coeff_toPoly l i]

theorem natDegree_toPoly_le (l : List ℕ) : (toPoly l).natDegree ≤ l.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
    rw [coeff_toPoly]
    exact List.getD_eq_default _ _ (by omega)

theorem coeff_toPoly_le {l : List ℕ} {A : ℕ} (h : ∀ x ∈ l, x ≤ A) (i : ℕ) :
    (toPoly l).coeff i ≤ A := by
  rw [coeff_toPoly]
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- **Digits without carries.** If every coefficient is below `2^w`, digit `k` of `p(2^w)` is the
coefficient of `Xᵏ`. -/
theorem digit (w : ℕ) : ∀ (n : ℕ) (p : ℕ[X]), p.natDegree ≤ n → (∀ k, p.coeff k < 2 ^ w) →
    ∀ k, (p.eval (2 ^ w) / 2 ^ (w * k)) % 2 ^ w = p.coeff k := by
  intro n
  induction n with
  | zero =>
    intro p hd hb k
    have hp : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hd
    have h0 := hb 0
    rw [hp, eval_C, coeff_C]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Nat.mod_eq_of_lt h0]
    · have hle : 2 ^ w ≤ 2 ^ (w * k) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hk)
      rw [Nat.div_eq_of_lt (h0.trans_le hle), if_neg (by omega), Nat.zero_mod]
  | succ n ih =>
    intro p hd hb k
    have hp := X_mul_divX_add p
    have hdq : p.divX.natDegree ≤ n := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hbq : ∀ k, p.divX.coeff k < 2 ^ w := fun k => by rw [coeff_divX]; exact hb (k + 1)
    have he : p.eval (2 ^ w) = p.coeff 0 + 2 ^ w * p.divX.eval (2 ^ w) := by
      conv_lhs => rw [← hp]
      simp only [eval_add, eval_mul, eval_X, eval_C]
      ring
    rw [he]
    cases k with
    | zero =>
      rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hb 0)]
    | succ k =>
      rw [show w * (k + 1) = w + w * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (hb 0), zero_add,
        ih p.divX hdq hbq k, coeff_divX]

theorem coeff_mul_le {a b : List ℕ} {A B : ℕ} (hA : ∀ x ∈ a, x ≤ A) (hB : ∀ x ∈ b, x ≤ B) (k : ℕ) :
    (toPoly a * toPoly b).coeff k ≤ (k + 1) * (A * B) := by
  rw [coeff_mul]
  calc ∑ x ∈ antidiagonal k, (toPoly a).coeff x.1 * (toPoly b).coeff x.2
      ≤ ∑ _x ∈ antidiagonal k, A * B :=
        sum_le_sum fun x _ => Nat.mul_le_mul (coeff_toPoly_le hA _) (coeff_toPoly_le hB _)
    _ = (k + 1) * (A * B) := by simp [Finset.Nat.card_antidiagonal]

theorem dot_eq_sum : ∀ (a b : List ℕ), a.length = b.length →
    dot a b = ∑ k ∈ range a.length, a.getD k 0 * b.getD k 0
  | [], [], _ => by simp [dot]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    have ih := dot_eq_sum a b (by simpa using h)
    simp only [dot] at ih ⊢
    rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem getD_reverse_sub {b : List ℕ} {n k : ℕ} (hb : b.length = n) (hk : k < n) :
    b.reverse.getD (n - 1 - k) 0 = b.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega),
    List.getElem_reverse]
  congr 1
  omega

/-- **The packed dot product.** -/
theorem dot_digit (w n A B : ℕ) (a b : List ℕ) (hn : 0 < n) (ha : a.length = n) (hb : b.length = n)
    (hA : ∀ x ∈ a, x ≤ A) (hB : ∀ x ∈ b, x ≤ B) (hw : 2 * n * (A * B) < 2 ^ w) :
    (pack w a * pack w b.reverse / 2 ^ (w * (n - 1))) % 2 ^ w = dot a b := by
  have hB' : ∀ x ∈ b.reverse, x ≤ B := fun x hx => hB x (List.mem_reverse.mp hx)
  have hdeg : (toPoly a * toPoly b.reverse).natDegree ≤ 2 * n := by
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_toPoly_le a
    have h2 := natDegree_toPoly_le b.reverse
    rw [List.length_reverse] at h2
    omega
  have hbnd : ∀ k, (toPoly a * toPoly b.reverse).coeff k < 2 ^ w := by
    intro k
    by_cases h0 : (toPoly a * toPoly b.reverse).coeff k = 0
    · rw [h0]; positivity
    · have hk : k ≤ (toPoly a * toPoly b.reverse).natDegree := le_natDegree_of_ne_zero h0
      have h1 := natDegree_toPoly_le a
      have h2 := natDegree_toPoly_le b.reverse
      rw [List.length_reverse] at h2
      have hk' : k + 1 ≤ 2 * n := by
        have := (hk.trans natDegree_mul_le).trans (add_le_add h1 h2)
        omega
      exact (coeff_mul_le hA hB' k).trans_lt
        ((Nat.mul_le_mul_right _ hk').trans_lt hw)
  rw [← eval_toPoly, ← eval_toPoly, ← eval_mul, digit w (2 * n) _ hdeg hbnd (n - 1), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (toPoly a).coeff i * (toPoly b.reverse).coeff j), dot_eq_sum a b (by omega),
    ha, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_toPoly, coeff_toPoly, getD_reverse_sub hb (Finset.mem_range.mp hk)]

/-- A kernel instance: the digit is computed by GMP multiplication. -/
theorem example_dot : (pack 64 [3, 5, 7] * pack 64 [11, 13, 17].reverse / 2 ^ (64 * 2)) % 2 ^ 64 =
    dot [3, 5, 7] [11, 13, 17] :=
  dot_digit 64 3 17 17 _ _ (by norm_num) rfl rfl (by decide) (by decide) (by norm_num)

theorem example_value : (pack 64 [3, 5, 7] * pack 64 [11, 13, 17].reverse / 2 ^ (64 * 2)) % 2 ^ 64 = 217 := by
  decide +kernel

end AEGIS.KroneckerDotV1

#print axioms AEGIS.KroneckerDotV1.dot_digit
#print axioms AEGIS.KroneckerDotV1.example_value
