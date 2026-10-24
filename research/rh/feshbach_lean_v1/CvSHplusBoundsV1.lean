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

import CvSTauPrimeL12V1
import CvSRingBridgeV1
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Rational lower bounds for `h₊(r) = Re ψ(1/4 + ir/2) − log π` (CvS step K2)

* `hplus_le_of_sq_le`: `h₊` increases in `r²`, since every series term `a_k(r)` does.
* `tsum_archTerm_ge`: with `Φ_r(k) = −(3/4)/(k + 1/8) + r²/(2c_k² + r²)`,
  `Φ_r(k) − Φ_r(k+1) ≤ a_k(r)`, so `Σ_{k<N} a_k(r) + Φ_r(N) ≤ Σ' a_k(r)`.
* `gamma_le`: `γ < H₅₁₂ − 9 log 2`; `logPi_le`: `log π ≤ log 3 + π/3 − 1`.
* `hplusCheck_sound`: a passing `Bool` check, run by `decide +kernel`, gives `lo ≤ h₊(p)`.
* `scertM_three_ge`: `ScertM 3 t ≥ h₊(t) − w₂ − w₃`.

No `native_decide`. Not RH.
-/

open Finset Filter Topology

namespace AEGIS.CvSHplusBoundsV1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-! ### Monotonicity in `|r|` -/

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

/-! ### The telescoping tail -/

/-- `Φ_r(k) = −(3/4)/(k + 1/8) + r²/(2c_k² + r²)`. -/
noncomputable def tailPhi (r : ℝ) (k : ℕ) : ℝ :=
  -(3 / 4) / ((k : ℝ) + 1 / 8) + r ^ 2 / (2 * archWidth k ^ 2 + r ^ 2)

theorem tele_le (r : ℝ) (k : ℕ) : tailPhi r k - tailPhi r (k + 1) ≤ archTerm k r := by
  have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw : archWidth k = 2 * (k : ℝ) + 1 / 2 := rfl
  have hw1 : archWidth (k + 1) = 2 * (k : ℝ) + 5 / 2 := by
    simp only [archWidth]; push_cast; ring
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  unfold tailPhi archTerm
  rw [hw, hw1, hk1]
  set x : ℝ := (k : ℝ)
  set R : ℝ := r ^ 2 with hR
  have hR0 : 0 ≤ R := sq_nonneg r
  have h1 : -(3 / 4) / (x + 1 / 8) - -(3 / 4) / (x + 1 + 1 / 8) ≤
      1 / (x + 1) - 2 / (2 * x + 1 / 2) := by
    have e : 1 / (x + 1) - 2 / (2 * x + 1 / 2) -
        (-(3 / 4) / (x + 1 / 8) - -(3 / 4) / (x + 1 + 1 / 8)) =
        (21 / 256) / ((x + 1) * (x + 1 / 4) * (x + 1 / 8) * (x + 9 / 8)) := by
      field_simp
      ring
    have : 0 ≤ (21 / 256) / ((x + 1) * (x + 1 / 4) * (x + 1 / 8) * (x + 9 / 8)) := by
      positivity
    linarith
  have h2 : R / (2 * (2 * x + 1 / 2) ^ 2 + R) - R / (2 * (2 * x + 5 / 2) ^ 2 + R) ≤
      2 / (2 * x + 1 / 2) - 2 * (2 * x + 1 / 2) / ((2 * x + 1 / 2) ^ 2 + R) := by
    set c : ℝ := 2 * x + 1 / 2 with hc
    have hc0 : 0 < c := by positivity
    have e5 : 2 * x + 5 / 2 = c + 2 := by rw [hc]; ring
    rw [e5]
    have e : 2 / c - 2 * c / (c ^ 2 + R) -
        (R / (2 * c ^ 2 + R) - R / (2 * (c + 2) ^ 2 + R)) =
        R * (24 * c ^ 3 + 32 * c ^ 2 + 8 * c * R + 16 * R + 2 * R ^ 2) /
          (c * (c ^ 2 + R) * (2 * c ^ 2 + R) * (2 * (c + 2) ^ 2 + R)) := by
      field_simp
      ring
    have : 0 ≤ R * (24 * c ^ 3 + 32 * c ^ 2 + 8 * c * R + 16 * R + 2 * R ^ 2) /
        (c * (c ^ 2 + R) * (2 * c ^ 2 + R) * (2 * (c + 2) ^ 2 + R)) := by positivity
    linarith
  have e2 : 2 * (2 * x + 1 / 2) / ((2 * x + 1 / 2) ^ 2 + R) =
      2 / (2 * x + 1 / 2) - (2 / (2 * x + 1 / 2) -
        2 * (2 * x + 1 / 2) / ((2 * x + 1 / 2) ^ 2 + R)) := by ring
  rw [e2]
  linarith

theorem tailPhi_tendsto (r : ℝ) : Tendsto (tailPhi r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => -(3 / 4 : ℝ) / ((k : ℝ) + 1 / 8)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hg : Tendsto (fun k : ℕ => 2 * archWidth k ^ 2 + r ^ 2) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [archWidth]
    nlinarith [sq_nonneg r]
  have h2 : Tendsto (fun k : ℕ => r ^ 2 / (2 * archWidth k ^ 2 + r ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  show Tendsto (fun k : ℕ => tailPhi r k) atTop (𝓝 0)
  simp only [tailPhi]
  simpa using h1.add h2

/-- **Tail bound**: `Σ_{k<N} a_k(r) + Φ_r(N) ≤ Σ' a_k(r)`. -/
theorem tsum_archTerm_ge (r : ℝ) (N : ℕ) :
    (∑ k ∈ range N, archTerm k r) + tailPhi r N ≤ ∑' k, archTerm k r := by
  have hs := (archTerm_summable r).hasSum.tendsto_sum_nat
  have hle : ∀ n, N ≤ n →
      (∑ k ∈ range N, archTerm k r) + tailPhi r N - tailPhi r n ≤
        ∑ k ∈ range n, archTerm k r := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n _ ih =>
      rw [sum_range_succ]
      have := tele_le r n
      linarith
  have hl : Tendsto (fun n => (∑ k ∈ range N, archTerm k r) + tailPhi r N - tailPhi r n)
      atTop (𝓝 ((∑ k ∈ range N, archTerm k r) + tailPhi r N - 0)) :=
    tendsto_const_nhds.sub (tailPhi_tendsto r)
  rw [sub_zero] at hl
  exact le_of_tendsto_of_tendsto hl hs (eventually_atTop.mpr ⟨N, hle⟩)

/-! ### `γ` and `log π` -/

/-- Upward-rounded harmonic numbers. -/
def hUp : ℕ → ℚ
  | 0 => 0
  | n + 1 => rup (hUp n + 1 / (n + 1))

theorem harmonic_le_hUp (n : ℕ) : (harmonic n : ℝ) ≤ hUp n := by
  induction n with
  | zero => simp [hUp]
  | succ n ih =>
    rw [harmonic_succ, hUp]
    refine le_trans ?_ (le_rup _)
    push_cast
    have e : (1 : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ := one_div _
    linarith

/-- `γ < H₅₁₂ − 9 log 2 ≤ gamUp`. -/
def gamUp : ℚ := 5782 / 10000

theorem gamUp_check : hUp 512 - 9 * l2Lo ≤ gamUp := by decide +kernel

theorem gamma_le : Real.eulerMascheroniConstant ≤ gamUp := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 512
  rw [Real.eulerMascheroniSeq', if_neg (by norm_num)] at h
  have hl : Real.log ((512 : ℕ) : ℝ) = 9 * Real.log 2 := by
    rw [show ((512 : ℕ) : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hl] at h
  have h2 := log2_bounds.1
  have h3 := harmonic_le_hUp 512
  have h4 : ((hUp 512 - 9 * l2Lo : ℚ) : ℝ) ≤ gamUp := by exact_mod_cast gamUp_check
  push_cast at h4
  linarith

def logPiUp : ℚ := l3Hi + piHi / 3 - 1

theorem logPi_le : Real.log Real.pi ≤ logPiUp := by
  have hpi := pi_bounds
  have h3 : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  have h4 := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
  have h5 := log3_bounds.2
  simp only [logPiUp]
  push_cast
  linarith [hpi.2]

/-! ### Kernel-checked partial sums -/

def archQ (k : ℕ) (r : ℚ) : ℚ := 1 / (k + 1) - 2 * cw k / (cw k ^ 2 + r ^ 2)

theorem archQ_cast (k : ℕ) (r : ℚ) : (archQ k r : ℝ) = archTerm k r := by
  simp only [archQ, archTerm]
  push_cast
  rw [cw_cast]

/-- Downward-rounded partial sums of the series. -/
def archLo (r : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => rdn (archLo r n + archQ n r)

theorem archLo_le (r : ℚ) (n : ℕ) : (archLo r n : ℝ) ≤ ∑ k ∈ range n, archTerm k r := by
  induction n with
  | zero => simp [archLo]
  | succ n ih =>
    rw [archLo, sum_range_succ]
    refine le_trans (rdn_le _) ?_
    push_cast
    rw [archQ_cast]
    linarith

def tailQ (r : ℚ) (N : ℕ) : ℚ := -(3 / 4) / ((N : ℚ) + 1 / 8) + r ^ 2 / (2 * cw N ^ 2 + r ^ 2)

theorem tailQ_cast (r : ℚ) (N : ℕ) : (tailQ r N : ℝ) = tailPhi r N := by
  simp only [tailQ, tailPhi]
  push_cast
  rw [cw_cast]

/-- The rational lower bound `h₊(p) ≥ Σ_{k<N} a_k(p) + Φ_p(N) − γ⁺ − (log π)⁺`. -/
def hplusLo (p : ℚ) (N : ℕ) : ℚ := archLo p N + tailQ p N - gamUp - logPiUp

theorem hplusLo_le (p : ℚ) (N : ℕ) : (hplusLo p N : ℝ) ≤ hplus p := by
  rw [hplus_eq_tsum]
  have h1 := archLo_le p N
  have h2 := tsum_archTerm_ge (p : ℝ) N
  have h3 := gamma_le
  have h4 := logPi_le
  simp only [hplusLo]
  push_cast
  rw [tailQ_cast]
  linarith

def hplusCheck (p : ℚ) (N : ℕ) (lo : ℚ) : Bool := decide (lo ≤ hplusLo p N)

/-- **A passing check bounds `h₊` on `|t| ≥ p`.** -/
theorem hplusCheck_sound {p : ℚ} {N : ℕ} {lo : ℚ} (h : hplusCheck p N lo = true) (hp : 0 ≤ p)
    {t : ℝ} (ht : (p : ℝ) ≤ |t|) : (lo : ℝ) ≤ hplus t := by
  simp only [hplusCheck, decide_eq_true_eq] at h
  have h1 : (lo : ℝ) ≤ hplusLo p N := by exact_mod_cast h
  have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : ((p : ℝ)) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ hp' ht 2
  exact h1.trans ((hplusLo_le p N).trans (hplus_le_of_sq_le h2))

/-! ### The Krein symbol with three prime powers -/

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

/-! ### Sanity checks -/

example : hplusCheck 0 40 (-5381 / 1000) = true := by decide +kernel
example : hplusCheck 266 540 (31459 / 10000) = true := by decide +kernel

end AEGIS.CvSHplusBoundsV1

#print axioms AEGIS.CvSHplusBoundsV1.hplus_le_of_sq_le
#print axioms AEGIS.CvSHplusBoundsV1.tele_le
#print axioms AEGIS.CvSHplusBoundsV1.tsum_archTerm_ge
#print axioms AEGIS.CvSHplusBoundsV1.gamma_le
#print axioms AEGIS.CvSHplusBoundsV1.logPi_le
#print axioms AEGIS.CvSHplusBoundsV1.hplusLo_le
#print axioms AEGIS.CvSHplusBoundsV1.hplusCheck_sound
#print axioms AEGIS.CvSHplusBoundsV1.scertM_three_ge
