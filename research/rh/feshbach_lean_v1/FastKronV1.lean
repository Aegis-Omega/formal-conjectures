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

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
Generic strict-evaluation and Kronecker-packing lemmas for kernel replay of integer matrix checks.
-/

open Finset

namespace AEGIS.FastKronV1

/-! ## Strict evaluation (continuation style); every helper is the identity. -/

def fN {α : Sort _} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (Nat.succ m)

def fI {α : Sort _} (e : ℤ) (k : ℤ → α) : α :=
  match e with
  | .ofNat n => fN n fun n' => k (.ofNat n')
  | .negSucc n => fN n fun n' => k (.negSucc n')

def fL {α : Sort _} : List ℤ → (List ℤ → α) → α
  | [], k => k []
  | a :: l, k => fI a fun a' => fL l fun l' => k (a' :: l')

def fLL {α : Sort _} : List (List ℤ) → (List (List ℤ) → α) → α
  | [], k => k []
  | a :: l, k => fL a fun a' => fLL l fun l' => k (a' :: l')

theorem fN_eq {α : Sort _} (n : ℕ) (k : ℕ → α) : fN n k = k n := by cases n <;> rfl

theorem fI_eq {α : Sort _} (e : ℤ) (k : ℤ → α) : fI e k = k e := by
  cases e <;> simp only [fI, fN_eq]

theorem fL_eq {α : Sort _} (l : List ℤ) (k : List ℤ → α) : fL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp only [fL, fI_eq, ih]

theorem fLL_eq {α : Sort _} (l : List (List ℤ)) (k : List (List ℤ) → α) : fLL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp only [fLL, fL_eq, ih]

/-! ## Packing -/

/-- `Σ l_j β^j` (Horner). -/
def packZ (β : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + β * packZ β l

theorem packZ_eq (β : ℤ) : ∀ l : List ℤ, packZ β l = ∑ j ∈ range l.length, l.getD j 0 * β ^ j
  | [] => by simp [packZ]
  | a :: l => by
      rw [packZ, packZ_eq β l, List.length_cons, sum_range_succ', mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun j _ => by ring

/-- Strict Horner over the reversed list. -/
def packRevS (β : ℤ) : List ℤ → ℤ → ℤ
  | [], acc => acc
  | a :: l, acc => fI (acc * β + a) fun acc' => packRevS β l acc'

def packS (β : ℤ) (l : List ℤ) : ℤ := packRevS β l.reverse 0

theorem packRevS_append (β : ℤ) : ∀ (l₁ l₂ : List ℤ) (acc : ℤ),
    packRevS β (l₁ ++ l₂) acc = packRevS β l₂ (packRevS β l₁ acc)
  | [], _, _ => rfl
  | a :: l₁, l₂, acc => by
      simp only [List.cons_append, packRevS, fI_eq]
      exact packRevS_append β l₁ l₂ _

theorem packRevS_reverse (β : ℤ) : ∀ (l : List ℤ) (acc : ℤ),
    packRevS β l.reverse acc = acc * β ^ l.length + packZ β l
  | [], acc => by simp [packRevS, packZ]
  | a :: l, acc => by
      rw [List.reverse_cons, packRevS_append, packRevS_reverse β l acc]
      simp only [packRevS, fI_eq, packZ, List.length_cons]
      ring

theorem packS_eq (β : ℤ) (l : List ℤ) : packS β l = packZ β l := by
  rw [packS, packRevS_reverse]; ring

/-- Strict dot product. -/
def ldotS : List ℤ → List ℤ → ℤ → ℤ
  | a :: as, b :: bs, acc => fI (acc + a * b) fun acc' => ldotS as bs acc'
  | _, _, acc => acc

theorem ldotS_eq : ∀ (a b : List ℤ) (acc : ℤ), a.length = b.length →
    ldotS a b acc = acc + ∑ i ∈ range a.length, a.getD i 0 * b.getD i 0
  | [], [], acc, _ => by simp [ldotS]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: as, y :: bs, acc, h => by
      simp only [ldotS, fI_eq, List.length_cons]
      rw [ldotS_eq as bs _ (by simpa using h), sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-! ## Digits -/

/-- Base-`β` digits (`n` of them) of a natural number, low first. -/
def digs (β : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, s => (s % β) :: digs β n (s / β)

/-- `Σ_{j<n} β^j`. -/
def G (β : ℕ) (n : ℕ) : ℕ := (List.replicate n 1).foldr (fun a acc => a + β * acc) 0

/-- Unpack signed digits: `digs (S + off·G) - off`. -/
def unpackZ (β off n : ℕ) (S : ℤ) : List ℤ :=
  (digs β n (S + (off * G β n : ℕ)).toNat).map fun d : ℕ => (d : ℤ) - off

theorem digs_length (β : ℕ) : ∀ n s, (digs β n s).length = n
  | 0, _ => rfl
  | n + 1, s => by simp [digs, digs_length β n]

theorem unpackZ_length (β off n : ℕ) (S : ℤ) : (unpackZ β off n S).length = n := by
  simp [unpackZ, digs_length]

theorem G_eq (β : ℕ) : ∀ n, G β n = ∑ j ∈ range n, β ^ j
  | 0 => rfl
  | n + 1 => by
      have h : G β (n + 1) = 1 + β * G β n := rfl
      rw [h, G_eq β n, sum_range_succ', mul_sum]
      simp only [pow_zero, pow_succ]
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun j _ => by ring

theorem digs_getD {β : ℕ} (hβ : 0 < β) : ∀ (n : ℕ) (e : ℕ → ℕ), (∀ j < n, e j < β) →
    ∀ j < n, (digs β n (∑ i ∈ range n, e i * β ^ i)).getD j 0 = e j
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, e, he, j, hj => by
      have hs : ∑ i ∈ range (n + 1), e i * β ^ i =
          e 0 + β * ∑ i ∈ range n, e (i + 1) * β ^ i := by
        rw [sum_range_succ', mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [add_comm]
        congr 1
        exact sum_congr rfl fun i _ => by ring
      have h0 := he 0 (Nat.succ_pos n)
      rw [hs]
      simp only [digs]
      rcases j with _ | j
      · simp only [List.getD_cons_zero]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      · simp only [List.getD_cons_succ]
        rw [Nat.add_mul_div_left _ _ hβ, Nat.div_eq_of_lt h0, zero_add]
        exact digs_getD hβ n (fun i => e (i + 1)) (fun i hi => he (i + 1) (by omega)) j (by omega)

/-- Signed Kronecker extraction: if `S = Σ d_j β^j` with `-off ≤ d_j < β - off`, the unpacked
    digits are exactly `d_j`. -/
theorem unpackZ_getD {β off n : ℕ} (hβ : 0 < β) (d : ℕ → ℤ)
    (hd : ∀ j < n, -(off : ℤ) ≤ d j ∧ d j + off < β) :
    ∀ j < n, (unpackZ β off n (∑ i ∈ range n, d i * (β : ℤ) ^ i)).getD j 0 = d j := by
  intro j hj
  set e : ℕ → ℕ := fun i => (d i + off).toNat with he
  have hcast : ∀ i < n, ((e i : ℕ) : ℤ) = d i + off := fun i hi => by
    simp only [he]; rw [Int.toNat_of_nonneg (by linarith [(hd i hi).1])]
  have hsum : (∑ i ∈ range n, d i * (β : ℤ) ^ i) + ((off * G β n : ℕ) : ℤ) =
      ((∑ i ∈ range n, e i * β ^ i : ℕ) : ℤ) := by
    rw [G_eq]
    push_cast
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i hi => by rw [hcast i (mem_range.mp hi)]; ring
  have hlt : ∀ i < n, e i < β := fun i hi => by
    have := hcast i hi; have := (hd i hi).2; omega
  have hlen : j < (digs β n (∑ i ∈ range n, e i * β ^ i)).length := by
    rw [digs_length]; exact hj
  rw [unpackZ, hsum, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some]
  have hdig := digs_getD hβ n e hlt j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at hdig
  rw [hdig, hcast j hj]; ring

/-- `digs` reads the base-`β` digits of `s`. -/
theorem digs_getD_div (β : ℕ) : ∀ (n s j : ℕ), j < n → (digs β n s).getD j 0 = s / β ^ j % β
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by simp [digs]
  | n + 1, s, j + 1, hj => by
      simp only [digs, List.getD_cons_succ]
      rw [digs_getD_div β n (s / β) j (by omega), Nat.div_div_eq_div_mul, ← pow_succ']

/-- Digit `j` of `Σ_{i<m} e_i β^i` is `e_j` when every `e_i < β`. -/
theorem sum_div_pow_mod {β : ℕ} (hβ : 0 < β) : ∀ (m : ℕ) (e : ℕ → ℕ), (∀ i < m, e i < β) →
    ∀ j < m, (∑ i ∈ range m, e i * β ^ i) / β ^ j % β = e j
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, e, he, j, hj => by
      have hs : ∑ i ∈ range (m + 1), e i * β ^ i =
          e 0 + β * ∑ i ∈ range m, e (i + 1) * β ^ i := by
        rw [sum_range_succ', mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [add_comm]
        congr 1
        exact sum_congr rfl fun i _ => by ring
      have h0 := he 0 (Nat.succ_pos m)
      rw [hs]
      rcases j with _ | j
      · rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hβ,
          Nat.div_eq_of_lt h0, zero_add]
        exact sum_div_pow_mod hβ m (fun i => e (i + 1)) (fun i hi => he (i + 1) (by omega)) j
          (by omega)

/-- Signed digits `a, …, a+n-1` of a packed `m`-digit number. -/
def unpackR (β off m a n : ℕ) (S : ℤ) : List ℤ :=
  (digs β n ((S + (off * G β m : ℕ)).toNat / β ^ a)).map fun d : ℕ => (d : ℤ) - off

theorem unpackR_length (β off m a n : ℕ) (S : ℤ) : (unpackR β off m a n S).length = n := by
  simp [unpackR, digs_length]

theorem unpackR_getD {β off m a n : ℕ} (hβ : 0 < β) (han : a + n ≤ m) (d : ℕ → ℤ)
    (hd : ∀ j < m, -(off : ℤ) ≤ d j ∧ d j + off < β) :
    ∀ q < n, (unpackR β off m a n (∑ i ∈ range m, d i * (β : ℤ) ^ i)).getD q 0 = d (a + q) := by
  intro q hq
  set e : ℕ → ℕ := fun i => (d i + off).toNat with he
  have hcast : ∀ i < m, ((e i : ℕ) : ℤ) = d i + off := fun i hi => by
    simp only [he]; rw [Int.toNat_of_nonneg (by linarith [(hd i hi).1])]
  have hsum : (∑ i ∈ range m, d i * (β : ℤ) ^ i) + ((off * G β m : ℕ) : ℤ) =
      ((∑ i ∈ range m, e i * β ^ i : ℕ) : ℤ) := by
    rw [G_eq]
    push_cast
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i hi => by rw [hcast i (mem_range.mp hi)]; ring
  have hlt : ∀ i < m, e i < β := fun i hi => by
    have := hcast i hi; have := (hd i hi).2; omega
  have hlen : q < (digs β n ((∑ i ∈ range m, e i * β ^ i) / β ^ a)).length := by
    rw [digs_length]; exact hq
  rw [unpackR, hsum, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some]
  have hdig := digs_getD_div β n ((∑ i ∈ range m, e i * β ^ i) / β ^ a) q hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at hdig
  rw [hdig, Nat.div_div_eq_div_mul, ← pow_add, sum_div_pow_mod hβ m e hlt (a + q) (by omega),
    hcast (a + q) (by omega)]
  ring

/-! ## Transpose -/

/-- Prepend one row to the column accumulators (continuation style). -/
def consCols {α : Sort _} : List ℤ → List (List ℤ) → (List (List ℤ) → α) → α
  | a :: row, c :: acc, k => consCols row acc fun acc' => k ((a :: c) :: acc')
  | _, _, k => k []

def transGo {α : Sort _} : List (List ℤ) → List (List ℤ) → (List (List ℤ) → α) → α
  | [], acc, k => k acc
  | r :: rs, acc, k => consCols r acc fun acc' => transGo rs acc' k

/-- Transpose `rows` (each of length `m`) by folding from the last row. -/
def transC {α : Sort _} (m : ℕ) (rows : List (List ℤ)) (k : List (List ℤ) → α) : α :=
  transGo rows.reverse (List.replicate m []) k

theorem consCols_eq {α : Sort _} : ∀ (r : List ℤ) (acc : List (List ℤ)) (k : List (List ℤ) → α),
    consCols r acc k = k (List.zipWith List.cons r acc)
  | a :: row, c :: acc, k => by simp only [consCols, consCols_eq row acc, List.zipWith_cons_cons]
  | [], _, k => by simp [consCols]
  | _ :: _, [], k => by simp [consCols]

theorem transGo_eq {α : Sort _} : ∀ (rs acc : List (List ℤ)) (k : List (List ℤ) → α),
    transGo rs acc k = k (rs.foldl (fun acc r => List.zipWith List.cons r acc) acc)
  | [], acc, k => rfl
  | r :: rs, acc, k => by simp only [transGo, consCols_eq, transGo_eq rs, List.foldl_cons]

/-- The transposed list, as a plain function. -/
def transP (m : ℕ) (rows : List (List ℤ)) : List (List ℤ) :=
  rows.foldr (fun r acc => List.zipWith List.cons r acc) (List.replicate m [])

theorem transC_eq {α : Sort _} (m : ℕ) (rows : List (List ℤ)) (k : List (List ℤ) → α) :
    transC m rows k = k (transP m rows) := by
  rw [transC, transGo_eq, List.foldl_reverse]; rfl

theorem transP_length (m : ℕ) : ∀ rows : List (List ℤ), (∀ r ∈ rows, r.length = m) →
    (transP m rows).length = m
  | [], _ => by simp [transP]
  | r :: rows, h => by
      have ih := transP_length m rows fun r' hr' => h r' (List.mem_cons_of_mem r hr')
      simp only [transP, List.foldr_cons] at ih ⊢
      rw [List.length_zipWith, ih, h r List.mem_cons_self, min_self]

theorem transP_getD (m : ℕ) : ∀ rows : List (List ℤ), (∀ r ∈ rows, r.length = m) →
    ∀ c < m, (transP m rows).getD c [] = rows.map fun r => r.getD c 0
  | [], _, c, hc => by simp [transP, List.getD_eq_getElem?_getD, hc]
  | r :: rows, h, c, hc => by
      have hr : r.length = m := h r List.mem_cons_self
      have hrows : ∀ r' ∈ rows, r'.length = m := fun r' hr' => h r' (List.mem_cons_of_mem r hr')
      have ih := transP_getD m rows hrows c hc
      have hlen := transP_length m rows hrows
      simp only [transP, List.foldr_cons] at ih hlen ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
        List.getElem?_eq_getElem (by omega : c < r.length),
        List.getElem?_eq_getElem (by omega : c < (List.foldr (fun r acc =>
          List.zipWith List.cons r acc) (List.replicate m []) rows).length)]
      simp only [Option.getD_some, List.map_cons]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c < r.length),
        Option.getD_some]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at ih
      rw [ih]

end AEGIS.FastKronV1

#print axioms AEGIS.FastKronV1.packS_eq
#print axioms AEGIS.FastKronV1.ldotS_eq
#print axioms AEGIS.FastKronV1.unpackZ_getD
#print axioms AEGIS.FastKronV1.unpackR_getD
#print axioms AEGIS.FastKronV1.transC_eq
#print axioms AEGIS.FastKronV1.transP_getD
