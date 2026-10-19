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
import CvSTauL12DataV1
import CvSRowTailV1

/-!
# `τ_k` at `L = 6/5`, `k = 1, …, 70` (CvS step 7e)

`τ_k = ∫ h₊ S_k + π Σ_{j<M} ppw_j sin(2πk ℓ_j/L)` (`CvSRowTailV1.tau`). At `L = 6/5` the nodes
`ℓ_j = min(log(j+1), L)` of the prime powers `j + 1 ≥ 4` sit at the window end, where the sine
vanishes, so for every cutoff `M ≥ 3` only `p = 2, 3` remain (`primeSum_eq`):

  `τ_k = ∫ h₊ S_k + π (√2 log 2 · sin(5πk log 2/3) + (2/√3) log 3 · sin(5πk log 3/3))`.

* `log2_bounds`, `log3_bounds`: `Real.abs_log_sub_add_sum_range_le` at `x = 1/2, 1/3`, to `2^-64`.
* `s2_bounds`, `s3_bounds`: `exp(−log p/2)` from `a² ≤ 1/p ≤ b²` (`exp_half_bounds`).
* `sinQ_bounds`: alternating partial sums of `Real.hasSum_sin` at rational `|x| ≤ 2`.
* `sinPi_bounds`: `sin(πu)` for `u` in a rational interval, via the nearest integer
  (`Real.sin_add_int_mul_pi`) and `Real.abs_sin_sub_sin_le`.
* `prime_bounds`: the prime part to about `4·10⁻¹⁶`.
* `tau_mem`: with `CvSTauL12V1.source_integral_mem`, a box of width at most `2·10⁻⁷` for
  `τ_k`, `k = 1, …, 70` (data from `tools/gen_tau_prime.py`, untrusted; one `decide +kernel`).
* `tau_neg`, `tau_zero`: `τ_{−k} = −τ_k` for every `M`, `L`.

These are the inputs of the off-diagonal entries `cvsEntry = L/(2π²)·(τ_n − τ_m)/(n − m)`
(`CvSRowTailV1.cvsEntry_off`) of the `L = 1.2` low block. Not RH.
-/

open Finset

namespace AEGIS.CvSTauPrimeL12V1

open AEGIS.CvSTauL12V1 AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchLorentzV1
open AEGIS.RHKreinZetaBridgeV3

/-! ### Logarithms -/

/-- `Σ_{i<n} x^(i+1)/(i+1)`, the partial sums of `−log(1 − x)`. -/
def logSum (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, x ^ (i + 1) / (i + 1)

theorem logSum_cast (x : ℚ) (n : ℕ) :
    (logSum x n : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
  simp [logSum]

def l2Lo : ℚ := 12786308645202655659 / 18446744073709551616
def l2Hi : ℚ := 12786308645202655660 / 18446744073709551616
def l3Lo : ℚ := 20265819725292939637 / 18446744073709551616
def l3Hi : ℚ := 20265819725292939639 / 18446744073709551616

theorem log2_bounds : (l2Lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ l2Hi := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 / 2 : ℚ) : ℝ)) (by norm_num) 70
  rw [← logSum_cast, show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv,
    show |((1 / 2 : ℚ) : ℝ)| ^ (70 + 1) / (1 - |((1 / 2 : ℚ) : ℝ)|) = (((1 / 2) ^ 70 : ℚ) : ℝ) by
      norm_num] at h
  have h1 : l2Lo ≤ logSum (1 / 2) 70 - (1 / 2) ^ 70 := by decide +kernel
  have h2 : logSum (1 / 2) 70 + (1 / 2) ^ 70 ≤ l2Hi := by decide +kernel
  have h1' : (l2Lo : ℝ) ≤ (logSum (1 / 2) 70 : ℝ) - (((1 / 2) ^ 70 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (logSum (1 / 2) 70 : ℝ) + (((1 / 2) ^ 70 : ℚ) : ℝ) ≤ l2Hi := by exact_mod_cast h2
  have := abs_le.mp h
  constructor <;> linarith

theorem log3_bounds : (l3Lo : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ l3Hi := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 / 3 : ℚ) : ℝ)) (by norm_num) 48
  rw [← logSum_cast, show (1 : ℝ) - ((1 / 3 : ℚ) : ℝ) = 2 / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    show |((1 / 3 : ℚ) : ℝ)| ^ (48 + 1) / (1 - |((1 / 3 : ℚ) : ℝ)|) =
      (((1 / 3) ^ 48 / 2 : ℚ) : ℝ) by norm_num] at h
  have h1 : l3Lo ≤ l2Lo + logSum (1 / 3) 48 - (1 / 3) ^ 48 / 2 := by decide +kernel
  have h2 : l2Hi + logSum (1 / 3) 48 + (1 / 3) ^ 48 / 2 ≤ l3Hi := by decide +kernel
  have h1' : (l3Lo : ℝ) ≤ l2Lo + (logSum (1 / 3) 48 : ℝ) - (((1 / 3) ^ 48 / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (l2Hi : ℝ) + (logSum (1 / 3) 48 : ℝ) + (((1 / 3) ^ 48 / 2 : ℚ) : ℝ) ≤ l3Hi := by
    exact_mod_cast h2
  have := abs_le.mp h
  have := log2_bounds
  constructor <;> linarith

/-! ### `p^{-1/2}` -/

theorem exp_half_bounds {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hal : a ^ 2 ≤ p⁻¹) (hbh : p⁻¹ ≤ b ^ 2) :
    a ≤ Real.exp (-Real.log p / 2) ∧ Real.exp (-Real.log p / 2) ≤ b := by
  have he : Real.exp (-Real.log p / 2) ^ 2 = p⁻¹ := by
    rw [sq, ← Real.exp_add, show -Real.log p / 2 + -Real.log p / 2 = -Real.log p by ring,
      Real.exp_neg, Real.exp_log hp]
  have h0 := (Real.exp_pos (-Real.log p / 2)).le
  constructor
  · exact (pow_le_pow_iff_left₀ ha h0 two_ne_zero).mp (he ▸ hal)
  · exact (pow_le_pow_iff_left₀ h0 hb two_ne_zero).mp (he ▸ hbh)

def s2Lo : ℚ := 13043817825332782212 / 18446744073709551616
def s2Hi : ℚ := 13043817825332782213 / 18446744073709551616
def s3Lo : ℚ := 10650232656628343401 / 18446744073709551616
def s3Hi : ℚ := 10650232656628343402 / 18446744073709551616

theorem s2_bounds : (s2Lo : ℝ) ≤ Real.exp (-Real.log 2 / 2) ∧
    Real.exp (-Real.log 2 / 2) ≤ s2Hi := by
  have h1 : s2Lo ^ 2 ≤ 2⁻¹ := by decide +kernel
  have h2 : 2⁻¹ ≤ s2Hi ^ 2 := by decide +kernel
  have h1' : ((s2Lo ^ 2 : ℚ) : ℝ) ≤ ((2⁻¹ : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((2⁻¹ : ℚ) : ℝ) ≤ ((s2Hi ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  exact exp_half_bounds (by norm_num) (by simp [s2Lo]; norm_num) (by simp [s2Hi]; norm_num)
    h1' h2'

theorem s3_bounds : (s3Lo : ℝ) ≤ Real.exp (-Real.log 3 / 2) ∧
    Real.exp (-Real.log 3 / 2) ≤ s3Hi := by
  have h1 : s3Lo ^ 2 ≤ 3⁻¹ := by decide +kernel
  have h2 : 3⁻¹ ≤ s3Hi ^ 2 := by decide +kernel
  have h1' : ((s3Lo ^ 2 : ℚ) : ℝ) ≤ ((3⁻¹ : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((3⁻¹ : ℚ) : ℝ) ≤ ((s3Hi ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  exact exp_half_bounds (by norm_num) (by simp [s3Lo]; norm_num) (by simp [s3Hi]; norm_num)
    h1' h2'

/-! ### The sine series -/

/-- `x^(2n+1)/(2n+1)!`. -/
noncomputable def sinTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * n + 1).factorial

theorem sin_hasSum (x : ℝ) : HasSum (fun n : ℕ => (-1) ^ n * sinTerm x n) (Real.sin x) := by
  simpa [sinTerm, mul_div_assoc] using Real.hasSum_sin x

theorem sinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2) : Antitone (sinTerm x) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hf : (((2 * (n + 1) + 1).factorial : ℕ) : ℝ) =
      ((2 * n + 3) * (2 * n + 2) : ℝ) * ((2 * n + 1).factorial : ℕ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  have hF : (0 : ℝ) < ((2 * n + 1).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
  have hq : x ^ 2 / ((2 * n + 3) * (2 * n + 2)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hsplit : sinTerm x (n + 1) = sinTerm x n * (x ^ 2 / ((2 * n + 3) * (2 * n + 2))) := by
    simp only [sinTerm]
    rw [hf, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]
    field_simp
  rw [hsplit]
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg hx0 _) hF.le) hq

theorem sin_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2) (k : ℕ) :
    Real.sin x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * sinTerm x i :=
  (sinTerm_antitone hx0 hx).tendsto_le_alternating_series (sin_hasSum x).tendsto_sum_nat k

theorem partial_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * sinTerm x i ≤ Real.sin x :=
  (sinTerm_antitone hx0 hx).alternating_series_le_tendsto (sin_hasSum x).tendsto_sum_nat k

/-- Rational partial sums of the sine series. -/
def sinPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1).factorial)

theorem sinPartial_cast (x : ℚ) (n : ℕ) :
    (sinPartial x n : ℝ) = ∑ i ∈ range n, (-1) ^ i * sinTerm x i := by
  simp [sinPartial, sinTerm]

def sinLoQ (x : ℚ) : ℚ := if 0 ≤ x then sinPartial x 14 else -sinPartial (-x) 15
def sinHiQ (x : ℚ) : ℚ := if 0 ≤ x then sinPartial x 15 else -sinPartial (-x) 14

theorem sinQ_bounds {x : ℚ} (h : |x| ≤ 2) :
    (sinLoQ x : ℝ) ≤ Real.sin x ∧ Real.sin x ≤ sinHiQ x := by
  have h' := abs_le.mp h
  by_cases hx : 0 ≤ x
  · have hr0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
    have hr2 : (x : ℝ) ≤ 2 := by exact_mod_cast h'.2
    simp only [sinLoQ, sinHiQ, if_pos hx, sinPartial_cast]
    exact ⟨partial_le_sin hr0 hr2 7, sin_le_partial hr0 hr2 7⟩
  · have hr0 : (0 : ℝ) ≤ ((-x : ℚ) : ℝ) := by push_cast; exact_mod_cast (by linarith : 0 ≤ -x)
    have hr2 : ((-x : ℚ) : ℝ) ≤ 2 := by push_cast; exact_mod_cast (by linarith : -x ≤ 2)
    have hs : Real.sin x = -Real.sin ((-x : ℚ) : ℝ) := by push_cast; rw [Real.sin_neg, neg_neg]
    simp only [sinLoQ, sinHiQ, if_neg hx]
    rw [Rat.cast_neg, Rat.cast_neg, sinPartial_cast, sinPartial_cast, hs]
    have a := partial_le_sin hr0 hr2 7
    have b := sin_le_partial hr0 hr2 7
    constructor <;> linarith

/-! ### `sin(πu)` for `u` in a rational interval -/

theorem mul_lo {w s wl wh sl : ℝ} (h0 : 0 ≤ wl) (h1 : wl ≤ w) (h2 : w ≤ wh) (h3 : sl ≤ s) :
    min (wl * sl) (wh * sl) ≤ w * s := by
  have hw : 0 ≤ w := h0.trans h1
  have : w * sl ≤ w * s := mul_le_mul_of_nonneg_left h3 hw
  rcases le_total 0 sl with h | h
  · exact min_le_of_left_le (by nlinarith)
  · exact min_le_of_right_le (by nlinarith)

theorem mul_hi {w s wl wh sh : ℝ} (h0 : 0 ≤ wl) (h1 : wl ≤ w) (h2 : w ≤ wh) (h3 : s ≤ sh) :
    w * s ≤ max (wl * sh) (wh * sh) := by
  have hw : 0 ≤ w := h0.trans h1
  have : w * s ≤ w * sh := mul_le_mul_of_nonneg_left h3 hw
  rcases le_total 0 sh with h | h
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem piLo_nonneg : (0 : ℝ) ≤ piLo := by norm_num [piLo]

/-- The integer nearest to `u` (from the lower end). -/
def mid (ul : ℚ) : ℤ := ⌊ul + 1 / 2⌋

/-- A rational lower end for `θ = π(u − mid)`, rounded down to `2^-64`. -/
def thLo (ul : ℚ) : ℚ := rdn (min (piLo * (ul - mid ul)) (piHi * (ul - mid ul)))

def thHi (ul uh : ℚ) : ℚ := max (piLo * (uh - mid ul)) (piHi * (uh - mid ul))

def baseLo (ul uh : ℚ) : ℚ := sinLoQ (thLo ul) - (thHi ul uh - thLo ul)
def baseHi (ul uh : ℚ) : ℚ := sinHiQ (thLo ul) + (thHi ul uh - thLo ul)

def sinPiLo (ul uh : ℚ) : ℚ := if mid ul % 2 = 0 then baseLo ul uh else -baseHi ul uh
def sinPiHi (ul uh : ℚ) : ℚ := if mid ul % 2 = 0 then baseHi ul uh else -baseLo ul uh

/-- **`sin(πu)` from a rational interval for `u`.** Reduce by the nearest integer `m`
(`sin(θ + mπ) = (−1)^m sin θ`), evaluate the alternating sine series at a rational point and
pay the distance (`|sin x − sin y| ≤ |x − y|`). -/
theorem sinPi_bounds {u : ℝ} {ul uh : ℚ} (hl : (ul : ℝ) ≤ u) (hh : u ≤ uh)
    (hok : |thLo ul| ≤ 2) :
    (sinPiLo ul uh : ℝ) ≤ Real.sin (Real.pi * u) ∧ Real.sin (Real.pi * u) ≤ sinPiHi ul uh := by
  have hπ := pi_bounds
  have h1 : (thLo ul : ℝ) ≤ Real.pi * (u - mid ul) := by
    have a := rdn_le (min (piLo * (ul - mid ul)) (piHi * (ul - mid ul)))
    have b : ((min (piLo * (ul - mid ul)) (piHi * (ul - mid ul)) : ℚ) : ℝ) ≤
        Real.pi * (u - mid ul) := by
      push_cast
      exact mul_lo piLo_nonneg hπ.1.le hπ.2.le (by linarith)
    simp only [thLo]
    linarith
  have h2 : Real.pi * (u - mid ul) ≤ thHi ul uh := by
    have b : Real.pi * (u - mid ul) ≤
        ((max (piLo * (uh - mid ul)) (piHi * (uh - mid ul)) : ℚ) : ℝ) := by
      push_cast
      exact mul_hi piLo_nonneg hπ.1.le hπ.2.le (by linarith)
    simpa only [thHi] using b
  have hs := sinQ_bounds hok
  have hlip := abs_le.mp (Real.abs_sin_sub_sin_le (Real.pi * (u - mid ul)) (thLo ul))
  have hb : (baseLo ul uh : ℝ) ≤ Real.sin (Real.pi * (u - mid ul)) ∧
      Real.sin (Real.pi * (u - mid ul)) ≤ baseHi ul uh := by
    simp only [baseLo, baseHi]
    push_cast
    have e : |Real.pi * (u - mid ul) - thLo ul| = Real.pi * (u - mid ul) - thLo ul :=
      abs_of_nonneg (by linarith)
    rw [e] at hlip
    constructor <;> linarith [hs.1, hs.2, hlip.1, hlip.2]
  have hsin : Real.sin (Real.pi * u) = (-1) ^ (mid ul) * Real.sin (Real.pi * (u - mid ul)) := by
    rw [← Real.sin_add_int_mul_pi]
    congr 1
    ring
  by_cases hm2 : mid ul % 2 = 0
  · have he : Even (mid ul) := Int.even_iff.mpr hm2
    simp only [sinPiLo, sinPiHi, if_pos hm2]
    rw [hsin, he.neg_one_zpow, one_mul]
    exact hb
  · have ho : Odd (mid ul) := Int.odd_iff.mpr (by omega)
    simp only [sinPiLo, sinPiHi, if_neg hm2]
    rw [hsin, ho.neg_one_zpow]
    push_cast
    constructor <;> linarith [hb.1, hb.2]

/-! ### The prime part of `τ_k` at `L = 6/5` -/

theorem ppw_one : ppw 1 = Real.log 2 * (2 * Real.exp (-Real.log 2 / 2)) := by
  simp only [ppw]
  rw [show (1 + 1 : ℕ) = 2 from rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  ring

theorem ppw_two : ppw 2 = Real.log 3 * (2 * Real.exp (-Real.log 3 / 2)) := by
  simp only [ppw]
  rw [show (2 + 1 : ℕ) = 3 from rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  push_cast
  ring

theorem node_zero : node (6 / 5) 0 = 0 := by
  simp only [node]
  norm_num

theorem node_one : node (6 / 5) 1 = Real.log 2 := by
  simp only [node]
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

theorem node_two : node (6 / 5) 2 = Real.log 3 := by
  simp only [node]
  rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l3Hi : ℝ) ≤ 6 / 5 := by norm_num [l3Hi]
  exact min_eq_left (by linarith [log3_bounds.2])

/-- Prime powers `j + 1 ≥ 4` have `log(j+1) > 6/5`, so their node is the window end. -/
theorem node_big {j : ℕ} (hj : 3 ≤ j) : node (6 / 5) j = 6 / 5 := by
  simp only [node]
  apply min_eq_right
  have h4 : (4 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ j + 1)
  have hl : Real.log 4 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h4
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlo : (6 / 5 : ℝ) ≤ 2 * l2Lo := by norm_num [l2Lo]
  have := log2_bounds.1
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

/-- **At `L = 6/5` only `p = 2, 3` contribute to the prime sum** (for any cutoff `M ≥ 3`). -/
theorem primeSum_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    ∑ j ∈ range M, ppw j * Real.sin (2 * Real.pi * k * node (6 / 5) j / (6 / 5)) =
      ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3)) := by
  have hz : ∀ j ∈ range M, j ∉ range 3 →
      ppw j * Real.sin (2 * Real.pi * k * node (6 / 5) j / (6 / 5)) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [node_big hj, show 2 * Real.pi * k * (6 / 5) / (6 / 5) = ((2 * k : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.sin_int_mul_pi, mul_zero]
  rw [← sum_subset (range_mono hM) hz]
  simp only [sum_range_succ, sum_range_zero, node_zero, node_one, node_two]
  rw [show 2 * Real.pi * k * Real.log 2 / (6 / 5) = Real.pi * (5 * k * Real.log 2 / 3) by ring,
    show 2 * Real.pi * k * Real.log 3 / (6 / 5) = Real.pi * (5 * k * Real.log 3 / 3) by ring]
  simp

def w2Lo : ℚ := l2Lo * (2 * s2Lo)
def w2Hi : ℚ := l2Hi * (2 * s2Hi)
def w3Lo : ℚ := l3Lo * (2 * s3Lo)
def w3Hi : ℚ := l3Hi * (2 * s3Hi)

theorem w2_bounds : (w2Lo : ℝ) ≤ ppw 1 ∧ ppw 1 ≤ w2Hi := by
  rw [ppw_one]
  have a := log2_bounds
  have b := s2_bounds
  have h0 : (0 : ℝ) ≤ l2Lo := by norm_num [l2Lo]
  have h1 : (0 : ℝ) ≤ s2Lo := by norm_num [s2Lo]
  simp only [w2Lo, w2Hi]
  push_cast
  constructor
  · exact mul_le_mul a.1 (by linarith) (by linarith) (by linarith)
  · exact mul_le_mul a.2 (by linarith) (by linarith [Real.exp_pos (-Real.log 2 / 2)])
      (by linarith)

theorem w3_bounds : (w3Lo : ℝ) ≤ ppw 2 ∧ ppw 2 ≤ w3Hi := by
  rw [ppw_two]
  have a := log3_bounds
  have b := s3_bounds
  have h0 : (0 : ℝ) ≤ l3Lo := by norm_num [l3Lo]
  have h1 : (0 : ℝ) ≤ s3Lo := by norm_num [s3Lo]
  simp only [w3Lo, w3Hi]
  push_cast
  constructor
  · exact mul_le_mul a.1 (by linarith) (by linarith) (by linarith)
  · exact mul_le_mul a.2 (by linarith) (by linarith [Real.exp_pos (-Real.log 3 / 2)])
      (by linarith)

def s2l (k : ℕ) : ℚ := sinPiLo (5 * k * l2Lo / 3) (5 * k * l2Hi / 3)
def s2h (k : ℕ) : ℚ := sinPiHi (5 * k * l2Lo / 3) (5 * k * l2Hi / 3)
def s3l (k : ℕ) : ℚ := sinPiLo (5 * k * l3Lo / 3) (5 * k * l3Hi / 3)
def s3h (k : ℕ) : ℚ := sinPiHi (5 * k * l3Lo / 3) (5 * k * l3Hi / 3)

def sumLo (k : ℕ) : ℚ := min (w2Lo * s2l k) (w2Hi * s2l k) + min (w3Lo * s3l k) (w3Hi * s3l k)
def sumHi (k : ℕ) : ℚ := max (w2Lo * s2h k) (w2Hi * s2h k) + max (w3Lo * s3h k) (w3Hi * s3h k)

/-- Rational bounds for `π Σ_j ppw_j sin(2πk ℓ_j/L)` at `L = 6/5`. -/
def primeLo (k : ℕ) : ℚ := min (piLo * sumLo k) (piHi * sumLo k)
def primeHi (k : ℕ) : ℚ := max (piLo * sumHi k) (piHi * sumHi k)

theorem prime_bounds (k : ℕ) (h2 : |thLo (5 * k * l2Lo / 3)| ≤ 2)
    (h3 : |thLo (5 * k * l3Lo / 3)| ≤ 2) :
    (primeLo k : ℝ) ≤ Real.pi * (ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3))) ∧
      Real.pi * (ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3))) ≤ primeHi k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have l2 := log2_bounds
  have l3 := log3_bounds
  have hs2 : (s2l k : ℝ) ≤ Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) ∧
      Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) ≤ s2h k :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have hs3 : (s3l k : ℝ) ≤ Real.sin (Real.pi * (5 * k * Real.log 3 / 3)) ∧
      Real.sin (Real.pi * (5 * k * Real.log 3 / 3)) ≤ s3h k :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  have hw2 := w2_bounds
  have hw3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have hπ := pi_bounds
  have hlo : (sumLo k : ℝ) ≤ ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
      ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3)) := by
    simp only [sumLo]
    push_cast
    exact add_le_add (mul_lo z2 hw2.1 hw2.2 hs2.1) (mul_lo z3 hw3.1 hw3.2 hs3.1)
  have hhi : ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
      ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3)) ≤ sumHi k := by
    simp only [sumHi]
    push_cast
    exact add_le_add (mul_hi z2 hw2.1 hw2.2 hs2.2) (mul_hi z3 hw3.1 hw3.2 hs3.2)
  constructor
  · simp only [primeLo]
    push_cast
    exact mul_lo piLo_nonneg hπ.1.le hπ.2.le hlo
  · simp only [primeHi]
    push_cast
    exact mul_hi piLo_nonneg hπ.1.le hπ.2.le hhi

/-! ### `τ_k` at `L = 6/5` -/

theorem sourceS_neg (L r : ℝ) (n : ℤ) : sourceS L r (-n) = -sourceS L r n := by
  simp only [sourceS]
  rw [← intervalIntegral.integral_neg]
  congr 1
  funext y
  push_cast
  rw [show 2 * Real.pi * -(n : ℝ) * (1 - y / L) = -(2 * Real.pi * n * (1 - y / L)) by ring,
    Real.sin_neg, neg_mul]

/-- `τ` is odd in `k`, so the boxes for `k ≥ 1` also give `k ≤ −1`, and `τ_0 = 0`. -/
theorem tau_neg (M : ℕ) (L : ℝ) (k : ℤ) : tau M L (-k) = -tau M L k := by
  simp only [tau, sourceS_neg, mul_neg, MeasureTheory.integral_neg]
  rw [neg_add, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [show 2 * Real.pi * -(k : ℝ) * node L j / L = -(2 * Real.pi * k * node L j / L) by ring,
    Real.sin_neg, mul_neg]

theorem tau_zero (M : ℕ) (L : ℝ) : tau M L 0 = 0 := by
  have h := tau_neg M L 0
  rw [neg_zero] at h
  linarith

theorem tau_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    tau M (6 / 5) k = (∫ r, hplus r * sourceS (6 / 5) r k) +
      Real.pi * (ppw 1 * Real.sin (Real.pi * (5 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (5 * k * Real.log 3 / 3))) := by
  rw [tau, primeSum_eq hM]

/-- The full check: source box from `CvSTauL12DataV1` plus the prime part, inside `[lo, hi]`. -/
def tauFullCheck (k : ℕ) (lo hi : ℚ) : Bool :=
  decide (|thLo (5 * k * l2Lo / 3)| ≤ 2) && decide (|thLo (5 * k * l3Lo / 3)| ≤ 2) &&
    decide (lo ≤ tauLo.getD (k - 1) 0 + primeLo k) &&
    decide (tauHi.getD (k - 1) 0 + primeHi k ≤ hi)

theorem tauFullCheck_sound {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70)
    {lo hi : ℚ} (h : tauFullCheck k lo hi = true) :
    (lo : ℝ) ≤ tau M (6 / 5) k ∧ tau M (6 / 5) k ≤ hi := by
  simp only [tauFullCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, h3⟩, hl⟩, hh⟩ := h
  have hs := source_integral_mem hk1 hk
  have hp := prime_bounds k h2 h3
  have hl' : (lo : ℝ) ≤ ((tauLo.getD (k - 1) 0 : ℚ) : ℝ) + (primeLo k : ℝ) := by
    exact_mod_cast hl
  have hh' : ((tauHi.getD (k - 1) 0 : ℚ) : ℝ) + (primeHi k : ℝ) ≤ hi := by exact_mod_cast hh
  rw [tau_eq hM]
  push_cast at hs hp ⊢
  constructor <;> linarith [hs.1, hs.2, hp.1, hp.2]

/-- Boxes for `τ_k`, `k = 1, …, 70` (untrusted, from `tools/gen_tau_prime.py`). -/
def tauFLo : List ℚ := [
  301818217931592 / 281474976710656,
  1068367435544121 / 281474976710656,
  -633816419165404 / 281474976710656,
  1209477933805230 / 281474976710656,
  279558959437947 / 281474976710656,
  1603221960798082 / 281474976710656,
  2214772671759733 / 281474976710656,
  1779269846213191 / 281474976710656,
  3317151544717779 / 281474976710656,
  1450207586842889 / 281474976710656,
  2548449820910573 / 281474976710656,
  919583621641596 / 281474976710656,
  680322800106539 / 281474976710656,
  806352320509551 / 281474976710656,
  -478322561393118 / 281474976710656,
  1347415340480716 / 281474976710656,
  159799925814019 / 281474976710656,
  2050416673746102 / 281474976710656,
  1935465555453732 / 281474976710656,
  2144978651667028 / 281474976710656,
  3124241170834561 / 281474976710656,
  1417028593163837 / 281474976710656,
  2620867342487736 / 281474976710656,
  531852959407775 / 281474976710656,
  973318232372088 / 281474976710656,
  423751578706263 / 281474976710656,
  -206526345582307 / 281474976710656,
  1315075646533220 / 281474976710656,
  172817783941397 / 281474976710656,
  2390676312689833 / 281474976710656,
  1667520362625025 / 281474976710656,
  2547274326316741 / 281474976710656,
  2802000087710952 / 281474976710656,
  1525329939210922 / 281474976710656,
  2532074764385012 / 281474976710656,
  262324733687916 / 281474976710656,
  1211253699443586 / 281474976710656,
  28671643047769 / 281474976710656,
  161062003208634 / 281474976710656,
  1146908972757906 / 281474976710656,
  344992104397100 / 281474976710656,
  2588285212116174 / 281474976710656,
  1480284248854466 / 281474976710656,
  2924229532590557 / 281474976710656,
  2410698849129347 / 281474976710656,
  1747913458279908 / 281474976710656,
  2285300735282483 / 281474976710656,
  146286760395434 / 281474976710656,
  1340546105577202 / 281474976710656,
  -309622456328665 / 281474976710656,
  563186417804995 / 281474976710656,
  887091390312602 / 281474976710656,
  662757584152711 / 281474976710656,
  2624912608265457 / 281474976710656,
  1421032000557570 / 281474976710656,
  3212192717197619 / 281474976710656,
  2017858280481929 / 281474976710656,
  2032494309504270 / 281474976710656,
  1909634236465980 / 281474976710656,
  189254263371981 / 281474976710656,
  1326716920524097 / 281474976710656,
  -532297645289914 / 281474976710656,
  932431242190036 / 281474976710656,
  596449881763137 / 281474976710656,
  1085352828680445 / 281474976710656,
  2510339768208833 / 281474976710656,
  1511846856587869 / 281474976710656,
  3361664051347484 / 281474976710656,
  1689309730797879 / 281474976710656,
  2314000484312282 / 281474976710656
]

/-- Upper ends. -/
def tauFHi : List ℚ := [
  301818273138220 / 281474976710656,
  1068367491136327 / 281474976710656,
  -633816363874355 / 281474976710656,
  1209477989106999 / 281474976710656,
  279559015118940 / 281474976710656,
  1603222016608632 / 281474976710656,
  2214772727274171 / 281474976710656,
  1779269901831251 / 281474976710656,
  3317151600400911 / 281474976710656,
  1450207642654574 / 281474976710656,
  2548449876481587 / 281474976710656,
  919583677169379 / 281474976710656,
  680322855810637 / 281474976710656,
  806352376166664 / 281474976710656,
  -478322505518203 / 281474976710656,
  1347415396402218 / 281474976710656,
  159799981637423 / 281474976710656,
  2050416729349371 / 281474976710656,
  1935465611145965 / 281474976710656,
  2144978707344041 / 281474976710656,
  3124241226806599 / 281474976710656,
  1417028648943028 / 281474976710656,
  2620867398393792 / 281474976710656,
  531853015367779 / 281474976710656,
  973318288320662 / 281474976710656,
  423751634584831 / 281474976710656,
  -206526289826184 / 281474976710656,
  1315075702484305 / 281474976710656,
  172817839675180 / 281474976710656,
  2390676368523945 / 281474976710656,
  1667520418516492 / 281474976710656,
  2547274382226004 / 281474976710656,
  2802000143601611 / 281474976710656,
  1525329995049498 / 281474976710656,
  2532074820140727 / 281474976710656,
  262324789667868 / 281474976710656,
  1211253755282288 / 281474976710656,
  28671699050933 / 281474976710656,
  161062059020478 / 281474976710656,
  1146909028681787 / 281474976710656,
  344992160408289 / 281474976710656,
  2588285267871996 / 281474976710656,
  1480284304654484 / 281474976710656,
  2924229588414151 / 281474976710656,
  2410698904957087 / 281474976710656,
  1747913514093486 / 281474976710656,
  2285300791064655 / 281474976710656,
  146286816435215 / 281474976710656,
  1340546161551495 / 281474976710656,
  -309622400434288 / 281474976710656,
  563186473605886 / 281474976710656,
  887091446304150 / 281474976710656,
  662757640023299 / 281474976710656,
  2624912664297286 / 281474976710656,
  1421032055864393 / 281474976710656,
  3212192770407098 / 281474976710656,
  2017858331968630 / 281474976710656,
  2032494359105233 / 281474976710656,
  1909634284515104 / 281474976710656,
  189254309719436 / 281474976710656,
  1326716965468767 / 281474976710656,
  -532297601886041 / 281474976710656,
  932431284321683 / 281474976710656,
  596449922495203 / 281474976710656,
  1085352868255130 / 281474976710656,
  2510339806508409 / 281474976710656,
  1511846893831494 / 281474976710656,
  3361664087426140 / 281474976710656,
  1689309765910499 / 281474976710656,
  2314000518357744 / 281474976710656
]

def tauFullAll : Bool :=
  (List.range 70).all fun i => tauFullCheck (i + 1) (tauFLo.getD i 0) (tauFHi.getD i 0)

set_option maxRecDepth 100000 in
theorem tauFullAll_true : tauFullAll = true := by decide +kernel

/-- **`τ_k` at `L = 6/5` for `k = 1, …, 70` and every prime cutoff `M ≥ 3`**, each box of width
at most `2·10⁻⁷`. -/
theorem tau_mem {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70) :
    ((tauFLo.getD (k - 1) 0 : ℚ) : ℝ) ≤ tau M (6 / 5) k ∧
      tau M (6 / 5) k ≤ ((tauFHi.getD (k - 1) 0 : ℚ) : ℝ) := by
  have h := tauFullAll_true
  simp only [tauFullAll, List.all_eq_true, List.mem_range] at h
  have := h (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at this
  exact tauFullCheck_sound hM hk1 hk this

end AEGIS.CvSTauPrimeL12V1

#print axioms AEGIS.CvSTauPrimeL12V1.log2_bounds
#print axioms AEGIS.CvSTauPrimeL12V1.log3_bounds
#print axioms AEGIS.CvSTauPrimeL12V1.sinQ_bounds
#print axioms AEGIS.CvSTauPrimeL12V1.sinPi_bounds
#print axioms AEGIS.CvSTauPrimeL12V1.primeSum_eq
#print axioms AEGIS.CvSTauPrimeL12V1.prime_bounds
#print axioms AEGIS.CvSTauPrimeL12V1.tauFullCheck_sound
#print axioms AEGIS.CvSTauPrimeL12V1.tauFullAll_true
#print axioms AEGIS.CvSTauPrimeL12V1.tau_mem
#print axioms AEGIS.CvSTauPrimeL12V1.tau_neg
#print axioms AEGIS.CvSTauPrimeL12V1.tau_zero
