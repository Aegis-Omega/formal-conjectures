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
import RHFixIntervalV1
import CvSResidualCertificateV1

/-!
# Packed fixed-point Gram certificates (kernel-checked positivity of an enclosed matrix)

A real symmetric `n × n` matrix `A` is known only through integer intervals: `I_ij` encloses
`A_ij` at scale `2^{-q}` (`RHFixIntervalV1.Iv.Mem`). A certificate is an integer matrix `L` with
entries in `[-B, B]` and integers `ε, η`. Writing `2^q A = L Lᵀ + ε·Id + E`, `check` (run by
`decide +kernel`) verifies that every row of `|E|` sums to at most `η`; the row-sum bound
`CvSResidualCertificateV1.residual_quadratic_le` then gives

  `(ε - η) Σ ‖c_i‖² ≤ 2^q Re Σ_{i,j} c_i conj(c_j) A_ij`   (`quad_lower_complex`).

`L Lᵀ` is computed by packed multiplication: a row is packed into one natural number `Σ u_k b^k`
(`pack`), and the digit at position `n - 1` of `pack u * pack (reverse v)` is `Σ u_k v_k` once
`n² M² < b` (`packDot_core`, `packDot_eq`), so one GMP multiplication replaces `n` kernel
multiplications. Signed entries are shifted by `B` (`offRow`, `gramEntry_eq`).

Unlike `RHExactLDLTV1` (exact rational `A = L D Lᵀ`), `A` is only enclosed, so its entries may be
transcendental once enclosures for them are proved. Example: the Hilbert matrix `H_8`
(`hilbert8_posDef`); `tools/packed_gram_cert.py` is the untrusted certificate generator.
No `native_decide`. Not RH.
-/

open Finset

namespace AEGIS.CvSPackedGramV1

/-- Little-endian base-`b` packing `Σ l_i b^i`. -/
def pack (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + b * pack b l

theorem pack_eq (b : ℕ) : ∀ l : List ℕ, pack b l = ∑ i ∈ range l.length, l.getD i 0 * b ^ i
  | [] => by simp [pack]
  | a :: l => by
    rw [pack, pack_eq b l, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    exact congrArg (· + a) (sum_congr rfl fun i _ => by ring)

/-- **Kronecker extraction.** If every product `x_i y_j` is at most `Q` and `n² Q < b`, the digit
of `(Σ x_i b^i)(Σ y_j b^{n-1-j})` at position `n - 1` is the dot product `Σ x_i y_i`. -/
theorem packDot_core {b n Q : ℕ} (x y : ℕ → ℕ) (hn : 0 < n)
    (hQ : ∀ i < n, ∀ j < n, x i * y j ≤ Q) (hb : n * n * Q < b) :
    (∑ i ∈ range n, x i * b ^ i) * (∑ j ∈ range n, y j * b ^ (n - 1 - j)) / b ^ (n - 1) % b =
      ∑ i ∈ range n, x i * y i := by
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hb
  set lo := ∑ i ∈ range n, ∑ j ∈ range n,
    if i < j then x i * y j * b ^ (i + (n - 1 - j)) else 0 with hlo_def
  set hi := ∑ i ∈ range n, ∑ j ∈ range n,
    if j < i then x i * y j * b ^ (i - 1 - j) else 0 with hhi_def
  set d := ∑ i ∈ range n, x i * y i with hd_def
  have hsplit : (∑ i ∈ range n, x i * b ^ i) * (∑ j ∈ range n, y j * b ^ (n - 1 - j)) =
      lo + b ^ (n - 1) * (d + b * hi) := by
    rw [sum_mul_sum, mul_add, mul_sum, mul_sum, mul_sum, hlo_def, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have e : b ^ (n - 1) * (x i * y i) =
        ∑ j ∈ range n, if i = j then b ^ (n - 1) * (x i * y j) else 0 := by
      rw [sum_ite_eq, if_pos (mem_range.mpr hi)]
    rw [e, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [h, if_true, h.ne, if_false, not_lt.mpr h.le, mul_zero, add_zero]
      rw [pow_add]; ring
    · simp only [lt_irrefl, if_false, if_true, mul_zero, zero_add, add_zero]
      rw [show b ^ (n - 1) = b ^ i * b ^ (n - 1 - i) by rw [← pow_add]; congr 1; omega]; ring
    · simp only [not_lt.mpr h.le, if_false, h.ne', h, if_true, zero_add]
      rw [show b ^ (n - 1) * (b * (x i * y j * b ^ (i - 1 - j))) =
        x i * y j * b ^ (n - 1 + 1 + (i - 1 - j)) by rw [pow_add, pow_succ]; ring]
      rw [show n - 1 + 1 + (i - 1 - j) = i + (n - 1 - j) by omega, pow_add]; ring
  have hlo : lo < b ^ (n - 1) := by
    have h1 : lo * b ≤ n * n * Q * b ^ (n - 1) := by
      calc lo * b = ∑ i ∈ range n, ∑ j ∈ range n,
            (if i < j then x i * y j * b ^ (i + (n - 1 - j) + 1) else 0) := by
            rw [hlo_def, sum_mul]
            refine sum_congr rfl fun i _ => ?_
            rw [sum_mul]
            refine sum_congr rfl fun j _ => ?_
            split_ifs <;> simp [pow_succ, mul_assoc]
        _ ≤ ∑ i ∈ range n, ∑ j ∈ range n, Q * b ^ (n - 1) := by
            refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
            rw [mem_range] at hi hj
            split_ifs with h
            · exact Nat.mul_le_mul (hQ i hi j hj) (Nat.pow_le_pow_right hb0 (by omega))
            · exact Nat.zero_le _
        _ = n * n * Q * b ^ (n - 1) := by simp only [sum_const, card_range, smul_eq_mul]; ring
    have h2 : n * n * Q * b ^ (n - 1) < b * b ^ (n - 1) :=
      Nat.mul_lt_mul_of_pos_right hb (pow_pos hb0 _)
    by_contra hc
    have := Nat.mul_le_mul_right b (not_lt.mp hc)
    linarith [mul_comm (b ^ (n - 1)) b]
  have hd : d < b := by
    have : d ≤ n * Q := by
      calc d ≤ ∑ i ∈ range n, Q := sum_le_sum fun i hi => hQ i (mem_range.mp hi) i (mem_range.mp hi)
        _ = n * Q := by simp
    have h3 : n * Q ≤ n * n * Q := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hn
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos hb0 _), Nat.div_eq_of_lt hlo, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]


theorem getD_le {l : List ℕ} {M : ℕ} (h : ∀ a ∈ l, a ≤ M) (k : ℕ) : l.getD k 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simp
  | some a =>
    obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hk
    exact h _ (List.getElem_mem hk')

theorem getD_mem {α : Type*} {l : List α} {d : α} {i : ℕ} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem pack_reverse (b : ℕ) (l : List ℕ) :
    pack b l.reverse = ∑ j ∈ range l.length, l.getD j 0 * b ^ (l.length - 1 - j) := by
  rw [pack_eq, List.length_reverse, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega),
    show l.length - 1 - (l.length - 1 - j) = j by omega, ← List.getD_eq_getElem?_getD]

/-- **Packed dot product.** One big multiplication, one division and one remainder compute
`Σ u_k v_k` when the entries are at most `M` and `n² M² < b`. -/
theorem packDot_eq {b M : ℕ} (u v : List ℕ) (hn : 0 < u.length) (hlen : v.length = u.length)
    (hu : ∀ a ∈ u, a ≤ M) (hv : ∀ a ∈ v, a ≤ M) (hb : u.length * u.length * (M * M) < b) :
    pack b u * pack b v.reverse / b ^ (u.length - 1) % b =
      ∑ k ∈ range u.length, u.getD k 0 * v.getD k 0 := by
  rw [pack_eq, pack_reverse, hlen]
  exact packDot_core _ _ hn (fun i _ j _ => Nat.mul_le_mul (getD_le hu i) (getD_le hv j)) hb

/-! ## Signed rows -/

/-- Shift a row of integers in `[-B, B]` to naturals. -/
def offRow (B : ℕ) (r : List ℤ) : List ℕ := r.map fun x : ℤ => (x + (B : ℤ)).toNat

theorem offRow_le {B : ℕ} {r : List ℤ} (hr : ∀ x ∈ r, -(B : ℤ) ≤ x ∧ x ≤ B) :
    ∀ a ∈ offRow B r, a ≤ 2 * B := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have := hr x hx
  omega

theorem offRow_getD {B : ℕ} {r : List ℤ} (hr : ∀ x ∈ r, -(B : ℤ) ≤ x ∧ x ≤ B) {k : ℕ}
    (hk : k < r.length) : (((offRow B r).getD k 0 : ℕ) : ℤ) = r.getD k 0 + B := by
  have hk' : k < (offRow B r).length := by simpa [offRow] using hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [offRow, List.getElem_map]
  have := hr _ (List.getElem_mem hk)
  omega

theorem sum_eq_range (r : List ℤ) : r.sum = ∑ k ∈ range r.length, r.getD k 0 := by
  induction r with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- A Gram entry from the packed shifted rows: `Σ (x_k + B)(y_k + B) - B(Σx + Σy) - nB²`. -/
def gramEntry (b B n : ℕ) (P : ℕ) (s : ℤ) (R : ℕ) (t : ℤ) : ℤ :=
  ((P * R / b ^ (n - 1) % b : ℕ) : ℤ) - B * (s + t) - n * B ^ 2

theorem gramEntry_eq {b B : ℕ} {r r' : List ℤ} (hn : 0 < r.length) (hlen : r'.length = r.length)
    (hr : ∀ x ∈ r, -(B : ℤ) ≤ x ∧ x ≤ B) (hr' : ∀ x ∈ r', -(B : ℤ) ≤ x ∧ x ≤ B)
    (hb : r.length * r.length * (2 * B * (2 * B)) < b) :
    gramEntry b B r.length (pack b (offRow B r)) r.sum (pack b (offRow B r').reverse) r'.sum =
      ∑ k ∈ range r.length, r.getD k 0 * r'.getD k 0 := by
  have hlu : (offRow B r).length = r.length := List.length_map _
  have hlv : (offRow B r').length = r.length := (List.length_map _).trans hlen
  have key := packDot_eq (offRow B r) (offRow B r') (by omega) (by omega) (offRow_le hr)
    (offRow_le hr') (by rwa [hlu])
  rw [hlu] at key
  unfold gramEntry
  rw [key, sum_eq_range r, sum_eq_range r', hlen]
  push_cast
  have e : ∀ k ∈ range r.length,
      (((offRow B r).getD k 0 : ℕ) : ℤ) * (((offRow B r').getD k 0 : ℕ) : ℤ) =
        r.getD k 0 * r'.getD k 0 + B * r.getD k 0 + B * r'.getD k 0 + B ^ 2 := by
    intro k hk
    rw [mem_range] at hk
    rw [offRow_getD hr hk, offRow_getD hr' (by omega)]
    ring
  rw [sum_congr rfl e]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  ring

/-! ## The kernel check -/

open AEGIS.RHFixIntervalV1

/-- Upper bound for `|a - g - ε δ_ij|` when `a ∈ [lo, hi]`. -/
def errAt (eps : ℤ) (i j : ℕ) (g : ℤ) (I : Iv) : ℤ :=
  max (I.hi - (g + if i = j then eps else 0)) ((g + if i = j then eps else 0) - I.lo)

/-- `Σ_j errAt` along row `i`; a column is `(pack of its reversed shifted row, its row sum)`. -/
def rowErr (b B n : ℕ) (eps : ℤ) (i P : ℕ) (s : ℤ) : ℕ → List (ℕ × ℤ) → List Iv → ℤ
  | j, c :: cs, I :: Is =>
    errAt eps i j (gramEntry b B n P s c.1 c.2) I + rowErr b B n eps i P s (j + 1) cs Is
  | _, _, _ => 0

theorem rowErr_eq (b B n : ℕ) (eps : ℤ) (i P : ℕ) (s : ℤ) :
    ∀ (cs : List (ℕ × ℤ)) (Is : List Iv) (j : ℕ), Is.length = cs.length →
      rowErr b B n eps i P s j cs Is = ∑ k ∈ range cs.length,
        errAt eps i (j + k) (gramEntry b B n P s (cs.getD k (0, 0)).1 (cs.getD k (0, 0)).2)
          (Is.getD k ⟨0, 0⟩)
  | [], _, _, _ => by simp [rowErr]
  | _ :: _, [], _, h => by simp at h
  | c :: cs, I :: Is, j, h => by
    rw [rowErr, rowErr_eq b B n eps i P s cs Is (j + 1) (by simpa using h), List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg (· + _) (sum_congr rfl fun k _ => by rw [show j + 1 + k = j + (k + 1) by ring])

/-- Every row `i` has `rowErr ≤ η`. -/
def rowsOk (b B n : ℕ) (eps eta : ℤ) (cols : List (ℕ × ℤ)) :
    ℕ → List (List ℤ) → List (List Iv) → Bool
  | i, r :: rs, Ir :: Irs =>
    decide (rowErr b B n eps i (pack b (offRow B r)) r.sum 0 cols Ir ≤ eta) &&
      rowsOk b B n eps eta cols (i + 1) rs Irs
  | _, _, _ => true

theorem rowsOk_spec (b B n : ℕ) (eps eta : ℤ) (cols : List (ℕ × ℤ)) :
    ∀ (rs : List (List ℤ)) (Irs : List (List Iv)) (i0 : ℕ),
      rowsOk b B n eps eta cols i0 rs Irs = true → Irs.length = rs.length →
      ∀ k < rs.length, rowErr b B n eps (i0 + k) (pack b (offRow B (rs.getD k [])))
        (rs.getD k []).sum 0 cols (Irs.getD k []) ≤ eta
  | [], _, _, _, _, k, hk => by simp at hk
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | r :: rs, Ir :: Irs, i0, hok, h, k, hk => by
    simp only [rowsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    cases k with
    | zero => simpa using hok.1
    | succ k =>
      have := rowsOk_spec b B n eps eta cols rs Irs (i0 + 1) hok.2 (by simpa using h) k
        (by simpa using hk)
      simpa [show i0 + 1 + k = i0 + (k + 1) by ring] using this

/-- Row `r` has length `n` and entries in `[-B, B]`. -/
def rowBounded (B n : ℕ) (r : List ℤ) : Bool :=
  decide (r.length = n) && r.all fun x => decide (-(B : ℤ) ≤ x) && decide (x ≤ B)

/-- **The certificate check**, evaluated by the kernel (`decide +kernel`): `L` is an `n × n`
integer matrix with entries in `[-B, B]`, `I` an `n × n` matrix of intervals, and for every row
`i`, `Σ_j max(hi_ij - c_ij, c_ij - lo_ij) ≤ η` where `c = L Lᵀ + ε·Id`, with `L Lᵀ` computed by
packed multiplication in base `b`. -/
def check (b B n : ℕ) (eps eta : ℤ) (L : List (List ℤ)) (I : List (List Iv)) : Bool :=
  decide (0 < n) && decide (n * n * (2 * B * (2 * B)) < b) && decide (L.length = n) &&
    decide (I.length = n) && L.all (rowBounded B n) && I.all (fun r => decide (r.length = n)) &&
    rowsOk b B n eps eta (L.map fun r => (pack b (offRow B r).reverse, r.sum)) 0 L I

/-- Entry `L_{ik}`. -/
def Lm (L : List (List ℤ)) (i k : ℕ) : ℤ := (L.getD i []).getD k 0

/-- Entry `I_{ij}`. -/
def Im (I : List (List Iv)) (i j : ℕ) : Iv := (I.getD i []).getD j ⟨0, 0⟩

/-- `(L Lᵀ)_{ij}`. -/
def gram (n : ℕ) (L : List (List ℤ)) (i j : ℕ) : ℤ := ∑ k ∈ range n, Lm L i k * Lm L j k

theorem check_spec {b B n : ℕ} {eps eta : ℤ} {L : List (List ℤ)} {I : List (List Iv)}
    (hc : check b B n eps eta L I = true) :
    ∀ i < n, ∑ j ∈ range n, errAt eps i j (gram n L i j) (Im I i j) ≤ eta := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hn, hb⟩, hL⟩, hI⟩, hLr⟩, hIr⟩, hok⟩ := hc
  intro i hi
  have hrow : ∀ k < n, (L.getD k []).length = n ∧
      ∀ x ∈ L.getD k [], -(B : ℤ) ≤ x ∧ x ≤ B := by
    intro k hk
    have := hLr _ (getD_mem (l := L) (i := k) (d := []) (by omega))
    simp only [rowBounded, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact ⟨this.1, this.2⟩
  have h := rowsOk_spec b B n eps eta _ L I 0 hok (by omega) i (by omega)
  have hIi : (I.getD i []).length = n := hIr _ (getD_mem (by omega : i < I.length))
  rw [zero_add, rowErr_eq _ _ _ _ _ _ _ _ _ 0 (by rw [List.length_map, hL, hIi]),
    List.length_map, hL] at h
  refine le_trans (le_of_eq (sum_congr rfl fun j hj => ?_)) h
  rw [mem_range] at hj
  have hcol : (L.map fun r => (pack b (offRow B r).reverse, r.sum)).getD j (0, 0) =
      (pack b (offRow B (L.getD j [])).reverse, (L.getD j []).sum) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hcol, zero_add]
  have hi' := hrow i hi
  have hj' := hrow j hj
  have := gramEntry_eq (b := b) (B := B) (r := L.getD i []) (r' := L.getD j []) (by omega)
    (by omega) hi'.2 hj'.2 (by rwa [hi'.1])
  rw [hi'.1] at this
  rw [this]
  rfl

/-! ## Soundness: the quadratic form -/

/-- **Soundness of the packed Gram certificate.** If the kernel accepts `check` and the intervals
`I_ij` enclose `A_ij` at scale `2^{-q}`, then `2^q xᵀ A x ≥ (ε - η) ‖x‖²`. -/
theorem quad_lower {n : ℕ} (q b B : ℕ) (eps eta : ℤ) (L : List (List ℤ)) (I : List (List Iv))
    (hc : check b B n eps eta L I = true) (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (hI : ∀ i j : Fin n, (Im I i j).Mem q (A i j)) (x : Fin n → ℝ) :
    ((eps - eta : ℤ) : ℝ) * ∑ i, x i ^ 2 ≤ 2 ^ q * ∑ i, ∑ j, A i j * x i * x j := by
  have hrow := check_spec hc
  set G : Fin n → Fin n → ℝ := fun i j => (gram n L i j : ℝ) with hG_def
  set D : Fin n → Fin n → ℝ := fun i j => if (i : ℕ) = j then (eps : ℝ) else 0 with hD_def
  set E : Fin n → Fin n → ℝ := fun i j => A i j * 2 ^ q - G i j - D i j with hE_def
  have hsplit : 2 ^ q * ∑ i, ∑ j, A i j * x i * x j = ∑ i, ∑ j, G i j * x i * x j +
      ∑ i, ∑ j, D i j * x i * x j + ∑ i, ∑ j, E i j * x i * x j := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by simp only [hE_def]; ring
  have hG : 0 ≤ ∑ i, ∑ j, G i j * x i * x j := by
    have e : ∑ i, ∑ j, G i j * x i * x j =
        ∑ k ∈ range n, (∑ i : Fin n, (Lm L i k : ℝ) * x i) ^ 2 := by
      have hsq : ∀ k ∈ range n, (∑ i : Fin n, (Lm L i k : ℝ) * x i) ^ 2 =
          ∑ i : Fin n, ∑ j : Fin n, (Lm L i k : ℝ) * Lm L j k * x i * x j := by
        intro k _
        rw [sq, sum_mul_sum]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
      rw [sum_congr rfl hsq]
      simp only [hG_def, gram, Int.cast_sum, Int.cast_mul, sum_mul]
      conv_rhs => rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      conv_rhs => rw [sum_comm]
    rw [e]
    exact sum_nonneg fun k _ => sq_nonneg _
  have hD : ∑ i, ∑ j, D i j * x i * x j = (eps : ℝ) * ∑ i, x i ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [hD_def, Fin.val_inj, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
    ring
  have hgram : ∀ i j, gram n L i j = gram n L j i := fun i j =>
    sum_congr rfl fun k _ => mul_comm _ _
  have hEsym : ∀ i j, E i j = E j i := by
    intro i j
    simp only [hE_def, hG_def, hD_def]
    rw [hA i j, hgram i j]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  have hEabs : ∀ i j, |E i j| ≤ (errAt eps i j (gram n L i j) (Im I i j) : ℝ) := by
    intro i j
    obtain ⟨h1, h2⟩ := hI i j
    have hp : (0 : ℝ) < 2 ^ q := by positivity
    rw [div_le_iff₀ hp] at h1
    rw [le_div_iff₀ hp] at h2
    have key : ∀ c lo hi : ℤ, (lo : ℝ) ≤ A i j * 2 ^ q → A i j * 2 ^ q ≤ hi →
        |A i j * 2 ^ q - c| ≤ ((max (hi - c) (c - lo) : ℤ) : ℝ) := by
      intro c lo hi l1 l2
      rw [Int.cast_max, abs_le]
      push_cast
      constructor
      · linarith [le_max_right ((hi : ℝ) - c) (c - lo)]
      · linarith [le_max_left ((hi : ℝ) - c) (c - lo)]
    have hEc : E i j = A i j * 2 ^ q -
        ((gram n L i j + if (i : ℕ) = j then eps else 0 : ℤ) : ℝ) := by
      simp only [hE_def, hG_def, hD_def]
      push_cast
      ring
    rw [hEc]
    exact key _ _ _ h1 h2
  have hErow : ∀ i, ∑ j, |E i j| ≤ eta := by
    intro i
    refine (sum_le_sum fun j _ => hEabs i j).trans ?_
    have := hrow i i.isLt
    rw [← Fin.sum_univ_eq_sum_range (fun j => errAt eps i j (gram n L i j) (Im I i j)) n] at this
    exact_mod_cast this
  have hE := AEGIS.CvSResidualCertificateV1.residual_quadratic_le (fun i j => -E i j)
    (fun i j => |E i j|) (eta : ℝ) (fun i j => by simp only [abs_neg, le_refl])
    (fun i j => by simp only [hEsym i j]) hErow x
  have hE' : -(∑ i, ∑ j, E i j * x i * x j) ≤ (eta : ℝ) * ∑ i, x i ^ 2 := by
    refine le_trans (le_of_eq ?_) hE
    simp only [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [hsplit, hD]
  push_cast
  linarith

/-- **Complex form.** `2^q Re Σ c_i conj(c_j) A_ij ≥ (ε - η) Σ ‖c_i‖²`. -/
theorem quad_lower_complex {n : ℕ} (q b B : ℕ) (eps eta : ℤ) (L : List (List ℤ))
    (I : List (List Iv)) (hc : check b B n eps eta L I = true) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = A j i) (hI : ∀ i j : Fin n, (Im I i j).Mem q (A i j)) (c : Fin n → ℂ) :
    ((eps - eta : ℤ) : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤
      2 ^ q * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (A i j : ℂ)).re := by
  have h1 := quad_lower q b B eps eta L I hc A hA hI (fun i => (c i).re)
  have h2 := quad_lower q b B eps eta L I hc A hA hI (fun i => (c i).im)
  have hre : (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (A i j : ℂ)).re =
      ∑ i, ∑ j, A i j * (c i).re * (c j).re + ∑ i, ∑ j, A i j * (c i).im * (c j).im := by
    simp only [Complex.re_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hn : ∑ i, ‖c i‖ ^ 2 = ∑ i, (c i).re ^ 2 + ∑ i, (c i).im ^ 2 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hre, hn, mul_add, mul_add]
  linarith

/-! ## Example: the Hilbert matrix -/

/-- The Hilbert matrix `1 / (i + j + 1)`. -/
noncomputable def hilbert (n : ℕ) (i j : Fin n) : ℝ := 1 / ((i : ℝ) + j + 1)

/-- Enclosures `⌊2^q / (i+j+1)⌋ ≤ 2^q / (i+j+1) ≤ ⌊2^q / (i+j+1)⌋ + 1`. -/
def hilbIv (q n : ℕ) : List (List Iv) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    ⟨((2 ^ q / (i + j + 1) : ℕ) : ℤ), ((2 ^ q / (i + j + 1) + 1 : ℕ) : ℤ)⟩

theorem hilbIv_mem (q n : ℕ) (i j : Fin n) : (Im (hilbIv q n) i j).Mem q (hilbert n i j) := by
  have hI : Im (hilbIv q n) i j =
      ⟨((2 ^ q / (i + j + 1) : ℕ) : ℤ), ((2 ^ q / (i + j + 1) + 1 : ℕ) : ℤ)⟩ := by
    simp only [Im, hilbIv, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range i.isLt, List.getElem?_range j.isLt, Option.map_some, Option.getD_some]
  rw [hI]
  set m := (i : ℕ) + j + 1 with hm
  have hm0 : 0 < m := by omega
  have h1 : 2 ^ q / m * m ≤ 2 ^ q := Nat.div_mul_le_self _ _
  have h2 : 2 ^ q < m * (2 ^ q / m + 1) := Nat.lt_mul_div_succ _ hm0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hh : hilbert n i j = 1 / (m : ℝ) := by simp [hilbert, hm]
  rw [hh]
  constructor
  · simp only [Int.cast_natCast]
    rw [div_le_div_iff₀ hp hmR, one_mul]
    exact_mod_cast h1
  · simp only [Int.cast_natCast]
    rw [div_le_div_iff₀ hmR hp, one_mul]
    rw [mul_comm] at h2
    push_cast at h2 ⊢
    exact_mod_cast h2.le

theorem hilbert_symm (n : ℕ) (i j : Fin n) : hilbert n i j = hilbert n j i := by
  simp only [hilbert, add_comm (i : ℝ)]

/-- Untrusted certificate for `H_8` from `tools/packed_gram_cert.py 8 100`. -/
def hilbL8 : List (List ℤ) := [
  [1125899906811337, 0, 0, 0, 0, 0, 0, 0],
  [562949953436956, 325019307012605, 0, 0, 0, 0, 0, 0],
  [375299968957970, 325019307247431, 83919623400847, 0, 0, 0, 0, 0],
  [281474976718478, 292517376528107, 125879436871257, 21277502266854, 0, 0, 0, 0],
  [225179981374782, 260015445805171, 143862213763039, 42555018111624, 5361383877467, 0, 0, 0],
  [187649984478985, 232156648041621, 149856472772273, 59104195174199, 13403565475309,
   1346772210609, 0, 0],
  [160842843839130, 208940983238233, 149856472833905, 70925036268234, 21933150956655,
   4041150874442, 335321522698, 0],
  [140737488359239, 189594595901862, 146859343417570, 78984700877721, 29853486955194,
   7616517124193, 1180316574425, 60286152592]]

/-- The kernel accepts the `H_8` certificate (`q = 100`, `b = 2^109`). -/
theorem hilb8_check : check (2 ^ 109) 1125899906811337 8 70452151894954616958 2026600422517800
    hilbL8 (hilbIv 100 8) = true := by
  decide +kernel

/-- **`H_8` is positive definite**, with margin:
`Re Σ c_i conj(c_j) / (i+j+1) ≥ μ Σ ‖c_i‖²`, `μ = (ε - η) / 2^100 ≈ 5.6·10⁻¹¹`
(`λ_min(H_8) ≈ 1.1·10⁻¹⁰`). -/
theorem hilbert8_posDef (c : Fin 8 → ℂ) :
    ((70452151894954616958 - 2026600422517800 : ℤ) : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤
      2 ^ 100 * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (hilbert 8 i j : ℂ)).re :=
  quad_lower_complex 100 _ _ _ _ _ _ hilb8_check _ (hilbert_symm 8) (hilbIv_mem 100 8) c

end AEGIS.CvSPackedGramV1

#print axioms AEGIS.CvSPackedGramV1.pack_eq
#print axioms AEGIS.CvSPackedGramV1.packDot_core
#print axioms AEGIS.CvSPackedGramV1.packDot_eq
#print axioms AEGIS.CvSPackedGramV1.gramEntry_eq
#print axioms AEGIS.CvSPackedGramV1.rowErr_eq
#print axioms AEGIS.CvSPackedGramV1.rowsOk_spec
#print axioms AEGIS.CvSPackedGramV1.check_spec
#print axioms AEGIS.CvSPackedGramV1.quad_lower
#print axioms AEGIS.CvSPackedGramV1.quad_lower_complex
#print axioms AEGIS.CvSPackedGramV1.hilbIv_mem
#print axioms AEGIS.CvSPackedGramV1.hilb8_check
#print axioms AEGIS.CvSPackedGramV1.hilbert8_posDef
