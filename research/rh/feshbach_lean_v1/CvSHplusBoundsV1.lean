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

import CvSDiagL12V1
import CvSRingBridgeV1

/-!
# `h₊` on half-lines and the three-prime Krein symbol (CvS step K2)

Rational bounds for `h₊(r) = Re ψ(1/4 + ir/2) − log π` on `r² ∈ [ql, qh]` already exist:
`CvSDiagL12V1.hplus_bounds` (40 terms plus the `CvSDiagTelV1.hplus_tel` tail). This file adds:

* `hplus_le_of_sq_le`: `h₊` increases in `r²`, since every series term `a_k(r)` does;
* `hplus_ge_of_sq`: so the lower bound `hpLo q q` holds on the whole half-line `q ≤ t²`;
* `scertM_three_ge`: `ScertM 3 t ≥ h₊(t) − w₂⁺ − w₃⁺`.

Not RH.
-/

open Finset

namespace AEGIS.CvSHplusBoundsV1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSTauPrimeL12V1 AEGIS.CvSDiagL12V1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem archTerm_le_of_sq_le (k : ℕ) {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) :
    archTerm k a ≤ archTerm k b := by
  unfold archTerm
  have hc := archWidth_pos k
  have : 2 * archWidth k / (archWidth k ^ 2 + b ^ 2) ≤
      2 * archWidth k / (archWidth k ^ 2 + a ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

theorem hplus_le_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) : hplus a ≤ hplus b := by
  rw [hplus_eq_tsum, hplus_eq_tsum]
  have := Summable.tsum_le_tsum (fun k => archTerm_le_of_sq_le k h) (archTerm_summable a)
    (archTerm_summable b)
  linarith

/-- **`h₊ ≥ hpLo q q` on the half-line `q ≤ t²`.** -/
theorem hplus_ge_of_sq {q : ℚ} (hq : 0 ≤ q) (hl : logOk (aK ^ 2 + q) = true) {t : ℝ}
    (ht : (q : ℝ) ≤ t ^ 2) : (hpLo q q : ℝ) ≤ hplus t := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have e : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt hq'
  have h := (hplus_bounds (r := Real.sqrt (q : ℝ)) hq e.ge e.le hl hl).1
  exact h.trans (hplus_le_of_sq_le (by rw [e]; exact ht))

theorem ppw_zero : ppw 0 = 0 := by
  simp [ppw]

theorem ppw_nonneg (n : ℕ) : 0 ≤ ppw n := by
  unfold ppw
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- `ScertM 3 t ≥ h₊(t) − w₂⁺ − w₃⁺`. -/
theorem scertM_three_ge (t : ℝ) : hplus t - w2Hi - w3Hi ≤ ScertM 3 t := by
  unfold ScertM
  rw [AEGIS.CvSRingBridgeV1.psi_sub_log_eq_hplus]
  simp only [sum_range_succ, sum_range_zero, ppw_zero, zero_mul, zero_add]
  have h1 := w2_bounds.2
  have h2 := w3_bounds.2
  have c1 := Real.cos_le_one (t * Real.log ((1 + 1 : ℕ) : ℝ))
  have c2 := Real.cos_le_one (t * Real.log ((2 + 1 : ℕ) : ℝ))
  have p1 := ppw_nonneg 1
  have p2 := ppw_nonneg 2
  nlinarith

end AEGIS.CvSHplusBoundsV1

#print axioms AEGIS.CvSHplusBoundsV1.hplus_le_of_sq_le
#print axioms AEGIS.CvSHplusBoundsV1.hplus_ge_of_sq
#print axioms AEGIS.CvSHplusBoundsV1.scertM_three_ge
