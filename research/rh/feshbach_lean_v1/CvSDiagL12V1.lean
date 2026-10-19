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
import CvSDiagTelV1
import CvSTauPrimeL12V1
import CvSQuadV1

/-!
# The diagonal entries `cvsEntry M (6/5) n n`, `n = 0, …, 70` (CvS step 7g)

`cvsEntry_diag_eq`: for every prime cutoff `M ≥ 3`, with `ω = 2πn/L`, `L = 6/5`,

  `cvsEntry M L n n = L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`

(`CvSQuadV1.hplus_cosB_diag`, `blockFn_diag`; the prime powers `≥ 4` sit at the window end).

* `log_bounds`: `log x` for a positive rational from `log x = e log 2 − log(1 − y)`, `y = 1 − 2^e/x`
  (64 terms of `Real.abs_log_sub_add_sum_range_le`); `lpi_bounds` for `log π`.
* `hplus_bounds`: `h₊(ω)` from `ω² ∈ [ql, qh]` via `CvSDiagTelV1.hplus_tel` at `K = 40`.
* `D_bounds`: the archimedean diagonal series via `CvSDiagTelV1.diagSeries_tel` at `K = 40`.
* `Pd_bounds`: the prime part, `cos(πu) = sin(π(u + 1/2))` and `CvSTauPrimeL12V1.sinPi_bounds`.
* `diag_mem`: one `decide +kernel` over `n = 0, …, 70`; every box has width at most `2·10⁻⁸`
  (data from `tools/gen_diag.py`, untrusted); `cvsEntry_diag_neg` gives `n ≤ −1`.

With `CvSTauPrimeL12V1.tau_mem` (off-diagonal entries) this encloses the whole `L = 1.2` low block.
Not RH.
-/

open Finset

namespace AEGIS.CvSDiagL12V1

open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSDiagTelV1
open AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1

/-! ### Logarithms of positive rationals -/

/-- `⌊log₂ x⌋` for `1 ≤ x < 2^64` by structural recursion (kernel-friendly). -/
def lg2 : ℕ → ℚ → ℕ
  | 0, _ => 0
  | f + 1, x => if 2 ≤ x then lg2 f (x / 2) + 1 else 0

/-- `y = 1 − 2^e/x`, so that `log x = e log 2 − log(1 − y)`. -/
def yOf (x : ℚ) : ℚ := 1 - 2 ^ lg2 64 x / x

def logLoQ (x : ℚ) : ℚ :=
  lg2 64 x * l2Lo + logSum (rdn (yOf x)) 64 - rdn (yOf x) ^ 65 / (1 - rdn (yOf x))

def logHiQ (x : ℚ) : ℚ :=
  lg2 64 x * l2Hi + logSum (rup (yOf x)) 64 + rup (yOf x) ^ 65 / (1 - rup (yOf x))

def logOk (x : ℚ) : Bool :=
  decide (0 < x) && decide (0 ≤ rdn (yOf x)) && decide (rup (yOf x) < 1)

theorem log_bounds {x : ℚ} (h : logOk x = true) :
    (logLoQ x : ℝ) ≤ Real.log x ∧ Real.log x ≤ logHiQ x := by
  simp only [logOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hyl⟩, hyh⟩ := h
  simp only [logLoQ, logHiQ]
  push_cast [logSum_cast]
  have hyle := rdn_le (yOf x)
  have hyge := le_rup (yOf x)
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hy : ((yOf x : ℚ) : ℝ) = 1 - 2 ^ lg2 64 x / (x : ℝ) := by simp [yOf]
  have hy1 : ((yOf x : ℚ) : ℝ) < 1 := by
    rw [hy]; have : (0 : ℝ) < 2 ^ lg2 64 x / x := by positivity
    linarith
  have hlogx : Real.log x = (lg2 64 x : ℝ) * Real.log 2 - Real.log (1 - (yOf x : ℝ)) := by
    rw [hy, show (1 : ℝ) - (1 - 2 ^ lg2 64 x / (x : ℝ)) = 2 ^ lg2 64 x / x by ring,
      Real.log_div (by positivity) hxr.ne', Real.log_pow]
    ring
  have hyl0 : (0 : ℝ) ≤ (rdn (yOf x) : ℝ) := by exact_mod_cast hyl
  have hyl1 : (rdn (yOf x) : ℝ) < 1 := lt_of_le_of_lt hyle hy1
  have hyh1 : (rup (yOf x) : ℝ) < 1 := by exact_mod_cast hyh
  have hyh0 : (0 : ℝ) ≤ (rup (yOf x) : ℝ) := le_trans hyl0 (le_trans hyle hyge)
  have hL := Real.abs_log_sub_add_sum_range_le (x := (rdn (yOf x) : ℝ))
    (by rw [abs_of_nonneg hyl0]; exact hyl1) 64
  have hU := Real.abs_log_sub_add_sum_range_le (x := (rup (yOf x) : ℝ))
    (by rw [abs_of_nonneg hyh0]; exact hyh1) 64
  rw [abs_of_nonneg hyl0] at hL
  rw [abs_of_nonneg hyh0] at hU
  have hL' := abs_le.mp hL
  have hU' := abs_le.mp hU
  have mono1 : Real.log (1 - (yOf x : ℝ)) ≤ Real.log (1 - (rdn (yOf x) : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have mono2 : Real.log (1 - (rup (yOf x) : ℝ)) ≤ Real.log (1 - (yOf x : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have l2 := log2_bounds
  have he : (0 : ℝ) ≤ (lg2 64 x : ℝ) := Nat.cast_nonneg _
  have m1 : (lg2 64 x : ℝ) * l2Lo ≤ (lg2 64 x : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left l2.1 he
  have m2 : (lg2 64 x : ℝ) * Real.log 2 ≤ (lg2 64 x : ℝ) * l2Hi := mul_le_mul_of_nonneg_left l2.2 he
  rw [hlogx]
  constructor <;> linarith

/-! ### Interval division -/

def idivLo (nl _nh dl dh : ℚ) : ℚ := if 0 ≤ nl then nl / dh else nl / dl
def idivHi (_nl nh dl dh : ℚ) : ℚ := if 0 ≤ nh then nh / dl else nh / dh

theorem idiv_bounds {n d : ℝ} {nl nh dl dh : ℚ} (h1 : (nl : ℝ) ≤ n) (h2 : n ≤ nh)
    (h3 : (dl : ℝ) ≤ d) (h4 : d ≤ dh) (h5 : 0 < dl) :
    (idivLo nl nh dl dh : ℝ) ≤ n / d ∧ n / d ≤ idivHi nl nh dl dh := by
  have hdl : (0 : ℝ) < dl := by exact_mod_cast h5
  have hd : 0 < d := lt_of_lt_of_le hdl h3
  have hdh : (0 : ℝ) < dh := lt_of_lt_of_le hd h4
  constructor
  · simp only [idivLo]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ nl := by exact_mod_cast h
      push_cast
      rw [div_le_div_iff₀ hdh hd]; nlinarith
    · have h' : (nl : ℝ) < 0 := by exact_mod_cast (not_le.mp h)
      push_cast
      rw [div_le_div_iff₀ hdl hd]; nlinarith
  · simp only [idivHi]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ nh := by exact_mod_cast h
      push_cast
      rw [div_le_div_iff₀ hd hdl]; nlinarith
    · have h' : (nh : ℝ) < 0 := by exact_mod_cast (not_le.mp h)
      push_cast
      rw [div_le_div_iff₀ hd hdh]; nlinarith

/-! ### `h₊(r)` for `r²` in a rational interval (`K = 40`) -/

/-- `c_40 − 1 = 159/2`. -/
def aK : ℚ := 159 / 2

theorem aK_cast : (aK : ℝ) = archWidth 40 - 1 := by simp [aK, archWidth]; norm_num

def SLo (q : ℚ) : ℚ := ∑ k ∈ range 40, rdn (2 * cw k / (cw k ^ 2 + q))
def SHi (q : ℚ) : ℚ := ∑ k ∈ range 40, rup (2 * cw k / (cw k ^ 2 + q))

theorem S_bounds {r : ℝ} {ql qh : ℚ} (h0 : 0 ≤ ql) (h1 : (ql : ℝ) ≤ r ^ 2) (h2 : r ^ 2 ≤ qh) :
    (SLo qh : ℝ) ≤ ∑ k ∈ range 40, 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) ∧
      ∑ k ∈ range 40, 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) ≤ ((SHi ql : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) ≤ ql := by exact_mod_cast h0
  have hcast : ∀ (k : ℕ) (q : ℚ), (((2 * cw k / (cw k ^ 2 + q)) : ℚ) : ℝ) =
      2 * archWidth k / (archWidth k ^ 2 + (q : ℝ)) := fun k q => by push_cast [cw_cast]; ring
  simp only [SLo, SHi]
  push_cast
  constructor
  · refine sum_le_sum fun k _ => ?_
    have hc := archWidth_pos k
    have t := rdn_le (2 * cw k / (cw k ^ 2 + qh))
    rw [hcast] at t
    have u : 2 * archWidth k / (archWidth k ^ 2 + (qh : ℝ)) ≤
        2 * archWidth k / (archWidth k ^ 2 + r ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    exact t.trans u
  · refine sum_le_sum fun k _ => ?_
    have hc := archWidth_pos k
    have t := le_rup (2 * cw k / (cw k ^ 2 + ql))
    rw [hcast] at t
    have u : 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) ≤
        2 * archWidth k / (archWidth k ^ 2 + (ql : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    exact u.trans t

/-- `log π` bounds (precomputed, checked once by `lpi_check`). -/
def lpiLo : ℚ := 21116539237790634171 / 18446744073709551616
def lpiHi : ℚ := 21116539237790634177 / 18446744073709551616

theorem lpi_check : logOk piLo = true ∧ logOk piHi = true ∧ lpiLo ≤ logLoQ piLo ∧
    logHiQ piHi ≤ lpiHi := by decide +kernel

theorem lpi_bounds : (lpiLo : ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ lpiHi := by
  obtain ⟨h1, h2, h3, h4⟩ := lpi_check
  have a := log_bounds h1
  have b := log_bounds h2
  have hp := pi_bounds
  have hp0 : (0 : ℝ) < piLo := by norm_num [piLo]
  have m1 : Real.log piLo ≤ Real.log Real.pi := Real.log_le_log hp0 hp.1.le
  have m2 : Real.log Real.pi ≤ Real.log piHi := Real.log_le_log Real.pi_pos hp.2.le
  have h3' : (lpiLo : ℝ) ≤ logLoQ piLo := by exact_mod_cast h3
  have h4' : (logHiQ piHi : ℝ) ≤ lpiHi := by exact_mod_cast h4
  constructor <;> linarith [a.1, b.2]

def hpLo (ql qh : ℚ) : ℚ :=
  -SHi ql + logLoQ (aK ^ 2 + ql) / 2 - l2Hi +
    idivLo (aK ^ 2 - qh) (aK ^ 2 - ql) ((aK ^ 2 + ql) ^ 2) ((aK ^ 2 + qh) ^ 2) / 6 -
    1 / (4 * aK ^ 4) - lpiHi

def hpHi (ql qh : ℚ) : ℚ :=
  -SLo qh + logHiQ (aK ^ 2 + qh) / 2 - l2Lo +
    idivHi (aK ^ 2 - qh) (aK ^ 2 - ql) ((aK ^ 2 + ql) ^ 2) ((aK ^ 2 + qh) ^ 2) / 6 +
    1 / (4 * aK ^ 4) - lpiLo

/-- **`h₊(r)` from `r² ∈ [ql, qh]`** (via `CvSDiagTelV1.hplus_tel` at `K = 40`). -/
theorem hplus_bounds {r : ℝ} {ql qh : ℚ} (h0 : 0 ≤ ql) (h1 : (ql : ℝ) ≤ r ^ 2) (h2 : r ^ 2 ≤ qh)
    (hl : logOk (aK ^ 2 + ql) = true) (hh : logOk (aK ^ 2 + qh) = true) :
    (hpLo ql qh : ℝ) ≤ hplus r ∧ hplus r ≤ hpHi ql qh := by
  have T := abs_le.mp (hplus_tel r (K := 40) (by norm_num))
  rw [← aK_cast] at T
  have S := S_bounds h0 h1 h2
  have L1 := log_bounds hl
  have L2 := log_bounds hh
  push_cast at L1 L2
  have h0' : (0 : ℝ) ≤ ql := by exact_mod_cast h0
  have ha : (0 : ℝ) < aK := by norm_num [aK]
  have g1 : Real.log ((aK : ℝ) ^ 2 + ql) ≤ Real.log ((aK : ℝ) ^ 2 + r ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have g2 : Real.log ((aK : ℝ) ^ 2 + r ^ 2) ≤ Real.log ((aK : ℝ) ^ 2 + qh) :=
    Real.log_le_log (by positivity) (by linarith)
  have C := idiv_bounds (n := (aK : ℝ) ^ 2 - r ^ 2) (d := ((aK : ℝ) ^ 2 + r ^ 2) ^ 2)
    (nl := aK ^ 2 - qh) (nh := aK ^ 2 - ql) (dl := (aK ^ 2 + ql) ^ 2) (dh := (aK ^ 2 + qh) ^ 2)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith) 2)
    (by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith) 2)
    (pow_pos (by have : (0 : ℚ) < aK ^ 2 := by norm_num [aK]
                 linarith) 2)
  have P := lpi_bounds
  have l2 := log2_bounds
  simp only [hpLo, hpHi]
  push_cast
  constructor <;> linarith [T.1, T.2, S.1, S.2, L1.1, L2.2, C.1, C.2]

/-! ### The archimedean diagonal series for `r² ∈ [ql, qh]` -/

/-- Outward-rounded `e^{−c_k·6/5}`, `k < 40` (checked once by `E_check`). -/
def EloL : List ℚ := [
  10123787795700325150 / 18446744073709551616,
  918409308362266468 / 18446744073709551616,
  83316212736569733 / 18446744073709551616,
  7558276295286888 / 18446744073709551616,
  685671355904309 / 18446744073709551616,
  62202702036815 / 18446744073709551616,
  5642901817851 / 18446744073709551616,
  511912503528 / 18446744073709551616,
  46439654583 / 18446744073709551616,
  4212910415 / 18446744073709551616,
  382186610 / 18446744073709551616,
  34671187 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616,
  0 / 18446744073709551616
]

def EhiL : List ℚ := [
  10123787795700325151 / 18446744073709551616,
  918409308362266469 / 18446744073709551616,
  83316212736569734 / 18446744073709551616,
  7558276295286889 / 18446744073709551616,
  685671355904310 / 18446744073709551616,
  62202702036816 / 18446744073709551616,
  5642901817852 / 18446744073709551616,
  511912503529 / 18446744073709551616,
  46439654584 / 18446744073709551616,
  4212910416 / 18446744073709551616,
  382186611 / 18446744073709551616,
  34671188 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616,
  3145300 / 18446744073709551616
]

/-- An upper bound for `e^{−c_40·6/5}`. -/
def ehK : ℚ := 3145300 / 18446744073709551616

theorem E_check : ((List.range 40).all fun k => decide (EloL.getD k 0 ≤ Elo k) &&
    decide (Ehi k ≤ EhiL.getD k 1) && decide (EhiL.getD k 1 ≤ 1)) = true ∧ Ehi 40 ≤ ehK := by
  decide +kernel

theorem EL_bounds {k : ℕ} (hk : k < 40) :
    ((EloL.getD k 0 : ℚ) : ℝ) ≤ Real.exp (-archWidth k * (6 / 5)) ∧
      Real.exp (-archWidth k * (6 / 5)) ≤ ((EhiL.getD k 1 : ℚ) : ℝ) ∧
      ((EhiL.getD k 1 : ℚ) : ℝ) ≤ 1 := by
  have h := E_check.1
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk
  have e := E_bounds k
  refine ⟨le_trans (by exact_mod_cast h1) e.1, le_trans e.2.1 (by exact_mod_cast h2),
    by exact_mod_cast h3⟩

def fLo (k : ℕ) (ql qh : ℚ) : ℚ :=
  idivLo (cw k ^ 2 - qh) (cw k ^ 2 - ql) ((cw k ^ 2 + ql) ^ 2) ((cw k ^ 2 + qh) ^ 2)
def fHi (k : ℕ) (ql qh : ℚ) : ℚ :=
  idivHi (cw k ^ 2 - qh) (cw k ^ 2 - ql) ((cw k ^ 2 + ql) ^ 2) ((cw k ^ 2 + qh) ^ 2)

def DhLo (ql qh : ℚ) : ℚ := ∑ k ∈ range 40,
  rdn (min ((1 - EhiL.getD k 1) * fLo k ql qh) ((1 - EloL.getD k 0) * fLo k ql qh))
def DhHi (ql qh : ℚ) : ℚ := ∑ k ∈ range 40,
  rup (max ((1 - EhiL.getD k 1) * fHi k ql qh) ((1 - EloL.getD k 0) * fHi k ql qh))

def gDLo (ql qh : ℚ) : ℚ := aK / (aK ^ 2 + qh) / 2 -
  idivHi (aK ^ 3 - 3 * aK * qh) (aK ^ 3 - 3 * aK * ql) ((aK ^ 2 + ql) ^ 3) ((aK ^ 2 + qh) ^ 3) / 6
def gDHi (ql qh : ℚ) : ℚ := aK / (aK ^ 2 + ql) / 2 -
  idivLo (aK ^ 3 - 3 * aK * qh) (aK ^ 3 - 3 * aK * ql) ((aK ^ 2 + ql) ^ 3) ((aK ^ 2 + qh) ^ 3) / 6

def hDHi : ℚ := 1 / (4 * aK ^ 5) + ehK / (2 * aK)

def DLo (ql qh : ℚ) : ℚ := DhLo ql qh + gDLo ql qh - hDHi
def DHi (ql qh : ℚ) : ℚ := DhHi ql qh + gDHi ql qh + hDHi

/-- The archimedean diagonal series `D(r) = Σ_k (1 − e^{−c_k L})(c_k² − r²)/(c_k² + r²)²`. -/
noncomputable def Dser (r : ℝ) : ℝ :=
  ∑' k, (1 - Real.exp (-archWidth k * (6 / 5))) * (archWidth k ^ 2 - r ^ 2) /
    (archWidth k ^ 2 + r ^ 2) ^ 2

theorem D_bounds {r : ℝ} {ql qh : ℚ} (h0 : 0 ≤ ql) (h1 : (ql : ℝ) ≤ r ^ 2) (h2 : r ^ 2 ≤ qh) :
    (DLo ql qh : ℝ) ≤ Dser r ∧ Dser r ≤ DHi ql qh := by
  have T := abs_le.mp (diagSeries_tel r (L := 6 / 5) (by norm_num) (K := 40) (by norm_num))
  simp only [gD, hD] at T
  rw [← aK_cast] at T
  have h0' : (0 : ℝ) ≤ ql := by exact_mod_cast h0
  have ha : (0 : ℝ) < aK := by norm_num [aK]
  -- the head
  have hcast : ∀ k : ℕ, ((cw k : ℚ) : ℝ) = archWidth k := cw_cast
  have H : (DhLo ql qh : ℝ) ≤ ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (6 / 5))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
      ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (6 / 5))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ≤ ((DhHi ql qh : ℚ) : ℝ) := by
    simp only [DhLo, DhHi]
    push_cast
    have hterm : ∀ k ∈ range 40, ((min ((1 - EhiL.getD k 1) * fLo k ql qh)
          ((1 - EloL.getD k 0) * fLo k ql qh) : ℚ) : ℝ) ≤
          (1 - Real.exp (-archWidth k * (6 / 5))) * (archWidth k ^ 2 - r ^ 2) /
            (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
        (1 - Real.exp (-archWidth k * (6 / 5))) * (archWidth k ^ 2 - r ^ 2) /
            (archWidth k ^ 2 + r ^ 2) ^ 2 ≤
          ((max ((1 - EhiL.getD k 1) * fHi k ql qh) ((1 - EloL.getD k 0) * fHi k ql qh) : ℚ) : ℝ) := by
      intro k hk
      have hk40 : k < 40 := mem_range.mp hk
      have E := EL_bounds hk40
      have hc := archWidth_pos k
      have F := idiv_bounds (n := archWidth k ^ 2 - r ^ 2) (d := (archWidth k ^ 2 + r ^ 2) ^ 2)
        (nl := cw k ^ 2 - qh) (nh := cw k ^ 2 - ql) (dl := (cw k ^ 2 + ql) ^ 2)
        (dh := (cw k ^ 2 + qh) ^ 2)
        (by push_cast [hcast]; linarith) (by push_cast [hcast]; linarith)
        (by push_cast [hcast]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2)
        (by push_cast [hcast]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2)
        (by have : (0 : ℚ) < cw k := by simp [cw]; positivity
            positivity)
      have e1 : (0 : ℝ) ≤ 1 - ((EhiL.getD k 1 : ℚ) : ℝ) := by linarith [E.2.2]
      rw [mul_div_assoc]
      push_cast
      constructor
      · exact mul_lo e1 (by linarith [E.2.1]) (by linarith [E.1]) (by simpa [fLo] using F.1)
      · exact mul_hi e1 (by linarith [E.2.1]) (by linarith [E.1]) (by simpa [fHi] using F.2)
    constructor
    · refine sum_le_sum fun k hk => ?_
      have u := (hterm k hk).1
      exact (rdn_le _).trans u
    · refine sum_le_sum fun k hk => ?_
      have u := (hterm k hk).2
      exact u.trans (le_rup _)
  -- the telescoped tail profile gD
  have G1 : (aK : ℝ) / ((aK : ℝ) ^ 2 + qh) / 2 ≤ (aK : ℝ) / ((aK : ℝ) ^ 2 + r ^ 2) / 2 := by
    gcongr
  have G2 : (aK : ℝ) / ((aK : ℝ) ^ 2 + r ^ 2) / 2 ≤ (aK : ℝ) / ((aK : ℝ) ^ 2 + ql) / 2 := by
    gcongr
  have C := idiv_bounds (n := (aK : ℝ) ^ 3 - 3 * aK * r ^ 2) (d := ((aK : ℝ) ^ 2 + r ^ 2) ^ 3)
    (nl := aK ^ 3 - 3 * aK * qh) (nh := aK ^ 3 - 3 * aK * ql) (dl := (aK ^ 2 + ql) ^ 3)
    (dh := (aK ^ 2 + qh) ^ 3)
    (by push_cast; nlinarith) (by push_cast; nlinarith)
    (by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith) 3)
    (by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith) 3)
    (pow_pos (by have : (0 : ℚ) < aK ^ 2 := by norm_num [aK]
                 linarith) 3)
  -- the tail budget
  have hE : Real.exp (-archWidth 40 * (6 / 5)) ≤ ehK := by
    have e := (E_bounds 40).2.1
    exact e.trans (by exact_mod_cast E_check.2)
  have hT : 1 / (4 * (aK : ℝ) ^ 5) + Real.exp (-archWidth 40 * (6 / 5)) / (2 * aK) ≤ hDHi := by
    simp only [hDHi]; push_cast
    have : Real.exp (-archWidth 40 * (6 / 5)) / (2 * aK) ≤ (ehK : ℝ) / (2 * aK) := by gcongr
    linarith
  simp only [DLo, DHi, gDLo, gDHi, Dser]
  push_cast
  constructor <;> linarith [T.1, T.2, H.1, H.2, C.1, C.2]

/-! ### The diagonal entry `cvsEntry M (6/5) n n` -/

open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSQuadV1 AEGIS.CvSArchDiagV1 AEGIS.CvSRowTailV1
open AEGIS.RHKreinZetaBridgeV3

theorem ppw_zero : ppw 0 = 0 := by simp [ppw]

/-- **The diagonal entry at `L = 6/5`**: `L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`
with `ω = 2πn/L`, for every prime cutoff `M ≥ 3`. -/
theorem cvsEntry_diag_eq {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (6 / 5) n n = 6 / 5 * hplus (2 * Real.pi * n / (6 / 5)) +
      2 * Dser (2 * Real.pi * n / (6 / 5)) -
      6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5)) * Real.cos (2 * Real.pi * n / (6 / 5) * Real.log 2) +
        ppw 2 * (1 - Real.log 3 / (6 / 5)) * Real.cos (2 * Real.pi * n / (6 / 5) * Real.log 3)) := by
  have hL : (0 : ℝ) < 6 / 5 := by norm_num
  rw [cvsEntry, hplus_cosB_diag hL n]
  simp only [blockFn_diag hL n]
  have hz : ∀ j ∈ range M, j ∉ range 3 → ppw j * (Real.pi * (6 / 5 * diagProfile (6 / 5) n
      (min |Real.log ((j + 1 : ℕ) : ℝ)| (6 / 5)))) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    have h := node_big hj
    simp only [node] at h
    rw [h, diagProfile]
    simp
  rw [← sum_subset (range_mono hM) hz]
  have h1 : min |Real.log ((1 + 1 : ℕ) : ℝ)| (6 / 5 : ℝ) = Real.log 2 := node_one
  have h2 : min |Real.log ((2 + 1 : ℕ) : ℝ)| (6 / 5 : ℝ) = Real.log 3 := node_two
  simp only [sum_range_succ, sum_range_zero, ppw_zero, zero_mul, zero_add, h1, h2]
  simp only [diagProfile, Dser]
  field_simp
  ring

/-! ### The prime part of the diagonal -/

def cf2Lo : ℚ := 6 / 5 * w2Lo * (1 - 5 * l2Hi / 6)
def cf2Hi : ℚ := 6 / 5 * w2Hi * (1 - 5 * l2Lo / 6)
def cf3Lo : ℚ := 6 / 5 * w3Lo * (1 - 5 * l3Hi / 6)
def cf3Hi : ℚ := 6 / 5 * w3Hi * (1 - 5 * l3Lo / 6)

theorem cf_bounds :
    ((cf2Lo : ℝ) ≤ 6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5))) ∧
      6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5))) ≤ cf2Hi) ∧
    ((cf3Lo : ℝ) ≤ 6 / 5 * (ppw 2 * (1 - Real.log 3 / (6 / 5))) ∧
      6 / 5 * (ppw 2 * (1 - Real.log 3 / (6 / 5))) ≤ cf3Hi) ∧
    (0 : ℝ) ≤ cf2Lo ∧ (0 : ℝ) ≤ cf3Lo := by
  have a := log2_bounds
  have b := log3_bounds
  have w2 := w2_bounds
  have w3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have p2 : (0 : ℝ) ≤ 1 - 5 * (l2Hi : ℝ) / 6 := by norm_num [l2Hi]
  have p3 : (0 : ℝ) ≤ 1 - 5 * (l3Hi : ℝ) / 6 := by norm_num [l3Hi]
  simp only [cf2Lo, cf2Hi, cf3Lo, cf3Hi]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by positivity, by positivity⟩
  · have := mul_le_mul w2.1 (show 1 - 5 * (l2Hi : ℝ) / 6 ≤ 1 - Real.log 2 / (6 / 5) by linarith [a.2])
      p2 (by linarith)
    nlinarith
  · have := mul_le_mul w2.2 (show 1 - Real.log 2 / (6 / 5) ≤ 1 - 5 * (l2Lo : ℝ) / 6 by linarith [a.1])
      (by linarith [a.2]) (by linarith)
    nlinarith
  · have := mul_le_mul w3.1 (show 1 - 5 * (l3Hi : ℝ) / 6 ≤ 1 - Real.log 3 / (6 / 5) by linarith [b.2])
      p3 (by linarith)
    nlinarith
  · have := mul_le_mul w3.2 (show 1 - Real.log 3 / (6 / 5) ≤ 1 - 5 * (l3Lo : ℝ) / 6 by linarith [b.1])
      (by linarith [b.2]) (by linarith)
    nlinarith

theorem cos_eq_sin (n : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * (n : ℤ) / (6 / 5) * x) = Real.sin (Real.pi * (5 * n * x / 3 + 1 / 2)) := by
  rw [← Real.sin_add_pi_div_two]
  congr 1
  push_cast
  ring

def co2l (n : ℕ) : ℚ := sinPiLo (5 * n * l2Lo / 3 + 1 / 2) (5 * n * l2Hi / 3 + 1 / 2)
def co2h (n : ℕ) : ℚ := sinPiHi (5 * n * l2Lo / 3 + 1 / 2) (5 * n * l2Hi / 3 + 1 / 2)
def co3l (n : ℕ) : ℚ := sinPiLo (5 * n * l3Lo / 3 + 1 / 2) (5 * n * l3Hi / 3 + 1 / 2)
def co3h (n : ℕ) : ℚ := sinPiHi (5 * n * l3Lo / 3 + 1 / 2) (5 * n * l3Hi / 3 + 1 / 2)

def PdLo (n : ℕ) : ℚ := min (cf2Lo * co2l n) (cf2Hi * co2l n) + min (cf3Lo * co3l n) (cf3Hi * co3l n)
def PdHi (n : ℕ) : ℚ := max (cf2Lo * co2h n) (cf2Hi * co2h n) + max (cf3Lo * co3h n) (cf3Hi * co3h n)

theorem Pd_bounds (n : ℕ) (h2 : |thLo (5 * n * l2Lo / 3 + 1 / 2)| ≤ 2)
    (h3 : |thLo (5 * n * l3Lo / 3 + 1 / 2)| ≤ 2) :
    (PdLo n : ℝ) ≤ 6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (6 / 5) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (6 / 5)) * Real.cos (2 * Real.pi * (n : ℤ) / (6 / 5) * Real.log 3)) ∧
    6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (6 / 5) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (6 / 5)) * Real.cos (2 * Real.pi * (n : ℤ) / (6 / 5) * Real.log 3)) ≤
      PdHi n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have l2 := log2_bounds
  have l3 := log3_bounds
  have s2 : (co2l n : ℝ) ≤ Real.sin (Real.pi * (5 * n * Real.log 2 / 3 + 1 / 2)) ∧
      Real.sin (Real.pi * (5 * n * Real.log 2 / 3 + 1 / 2)) ≤ co2h n :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have s3 : (co3l n : ℝ) ≤ Real.sin (Real.pi * (5 * n * Real.log 3 / 3 + 1 / 2)) ∧
      Real.sin (Real.pi * (5 * n * Real.log 3 / 3 + 1 / 2)) ≤ co3h n :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  obtain ⟨c2, c3, z2, z3⟩ := cf_bounds
  rw [cos_eq_sin, cos_eq_sin]
  have e : 6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5)) * Real.sin (Real.pi * (5 * n * Real.log 2 / 3 + 1 / 2)) +
      ppw 2 * (1 - Real.log 3 / (6 / 5)) * Real.sin (Real.pi * (5 * n * Real.log 3 / 3 + 1 / 2))) =
      6 / 5 * (ppw 1 * (1 - Real.log 2 / (6 / 5))) * Real.sin (Real.pi * (5 * n * Real.log 2 / 3 + 1 / 2)) +
      6 / 5 * (ppw 2 * (1 - Real.log 3 / (6 / 5))) * Real.sin (Real.pi * (5 * n * Real.log 3 / 3 + 1 / 2)) := by
    ring
  rw [e]
  simp only [PdLo, PdHi]
  push_cast
  constructor
  · exact add_le_add (mul_lo z2 c2.1 c2.2 s2.1) (mul_lo z3 c3.1 c3.2 s3.1)
  · exact add_le_add (mul_hi z2 c2.1 c2.2 s2.2) (mul_hi z3 c3.1 c3.2 s3.2)

/-! ### The kernel check -/

def ql (n : ℕ) : ℚ := (5 * piLo * n / 3) ^ 2
def qh (n : ℕ) : ℚ := (5 * piHi * n / 3) ^ 2

theorem q_bounds (n : ℕ) : (ql n : ℝ) ≤ (2 * Real.pi * (n : ℤ) / (6 / 5)) ^ 2 ∧
    (2 * Real.pi * (n : ℤ) / (6 / 5)) ^ 2 ≤ qh n := by
  have hp := pi_bounds
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp0 : (0 : ℝ) ≤ piLo := piLo_nonneg
  have e : 2 * Real.pi * ((n : ℤ) : ℝ) / (6 / 5) = 5 * Real.pi * n / 3 := by push_cast; ring
  rw [e]
  simp only [ql, qh]
  push_cast
  constructor
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.1.le) 2
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.2.le) 2

def entryLo (n : ℕ) : ℚ := 6 / 5 * hpLo (ql n) (qh n) + 2 * DLo (ql n) (qh n) - PdHi n
def entryHi (n : ℕ) : ℚ := 6 / 5 * hpHi (ql n) (qh n) + 2 * DHi (ql n) (qh n) - PdLo n

def diagCheck (n : ℕ) (lo hi : ℚ) : Bool :=
  logOk (aK ^ 2 + ql n) && logOk (aK ^ 2 + qh n) &&
    decide (|thLo (5 * n * l2Lo / 3 + 1 / 2)| ≤ 2) && decide (|thLo (5 * n * l3Lo / 3 + 1 / 2)| ≤ 2) &&
    decide (lo ≤ entryLo n) && decide (entryHi n ≤ hi)

theorem diagCheck_sound {M : ℕ} (hM : 3 ≤ M) {n : ℕ} {lo hi : ℚ} (h : diagCheck n lo hi = true) :
    (lo : ℝ) ≤ cvsEntry M (6 / 5) n n ∧ cvsEntry M (6 / 5) n n ≤ hi := by
  simp only [diagCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hl, hh⟩, h2⟩, h3⟩, hlo⟩, hhi⟩ := h
  have q := q_bounds n
  have hq0 : (0 : ℚ) ≤ ql n := by simp only [ql]; positivity
  have H := hplus_bounds hq0 q.1 q.2 hl hh
  have Dd := D_bounds hq0 q.1 q.2
  have P := Pd_bounds n h2 h3
  have hlo' : (lo : ℝ) ≤ entryLo n := by exact_mod_cast hlo
  have hhi' : (entryHi n : ℝ) ≤ hi := by exact_mod_cast hhi
  simp only [entryLo, entryHi] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [cvsEntry_diag_eq hM]
  constructor <;> linarith [H.1, H.2, Dd.1, Dd.2, P.1, P.2]

/-- Boxes for `cvsEntry M (6/5) n n`, `n = 0, …, 70` (untrusted, from `tools/gen_diag.py`). -/
def diagLo : List ℚ := [
  -810735438783605 / 281474976710656,
  36433761805421 / 281474976710656,
  78076019628908 / 281474976710656,
  326042620023061 / 281474976710656,
  477969672983592 / 281474976710656,
  407601953001972 / 281474976710656,
  716595718933601 / 281474976710656,
  491523654885294 / 281474976710656,
  758498540633428 / 281474976710656,
  633909993834225 / 281474976710656,
  672957963835204 / 281474976710656,
  800626184189016 / 281474976710656,
  614640688967367 / 281474976710656,
  914936354361254 / 281474976710656,
  695422439092467 / 281474976710656,
  928771313104051 / 281474976710656,
  889496933463676 / 281474976710656,
  869543563196690 / 281474976710656,
  1062293595413714 / 281474976710656,
  823437272501258 / 281474976710656,
  1095996159575408 / 281474976710656,
  865592821821871 / 281474976710656,
  996366087788827 / 281474976710656,
  994361758617692 / 281474976710656,
  885105359535908 / 281474976710656,
  1128312716228729 / 281474976710656,
  888085413289868 / 281474976710656,
  1173982869316751 / 281474976710656,
  1023293773045328 / 281474976710656,
  1109312922982274 / 281474976710656,
  1188947022760073 / 281474976710656,
  1008533090160989 / 281474976710656,
  1258572343014731 / 281474976710656,
  981318594846403 / 281474976710656,
  1194007521599595 / 281474976710656,
  1075446720325662 / 281474976710656,
  1075333175306912 / 281474976710656,
  1229695148164955 / 281474976710656,
  1025308028695416 / 281474976710656,
  1323784988467390 / 281474976710656,
  1100187131580813 / 281474976710656,
  1285566095330703 / 281474976710656,
  1244337368329697 / 281474976710656,
  1159835285843888 / 281474976710656,
  1344488475617563 / 281474976710656,
  1072854068915514 / 281474976710656,
  1330534648584163 / 281474976710656,
  1119850096740738 / 281474976710656,
  1233079721555096 / 281474976710656,
  1276021850776322 / 281474976710656,
  1151380699921732 / 281474976710656,
  1414763121629291 / 281474976710656,
  1165209226236933 / 281474976710656,
  1420802606080254 / 281474976710656,
  1269076548380124 / 281474976710656,
  1296945216072686 / 281474976710656,
  1382237344581896 / 281474976710656,
  1165068334714020 / 281474976710656,
  1420409874501446 / 281474976710656,
  1156986455061714 / 281474976710656,
  1365433761671249 / 281474976710656,
  1293211829321668 / 281474976710656,
  1276193947961150 / 281474976710656,
  1461728020053230 / 281474976710656,
  1236397472815307 / 281474976710656,
  1518737003779037 / 281474976710656,
  1285611821742430 / 281474976710656,
  1420495257956415 / 281474976710656,
  1389481068363643 / 281474976710656,
  1264791248313079 / 281474976710656,
  1470204229723789 / 281474976710656
]

/-- Upper ends. -/
def diagHi : List ℚ := [
  -810735434467088 / 281474976710656,
  36433766121938 / 281474976710656,
  78076023945425 / 281474976710656,
  326042624339578 / 281474976710656,
  477969677300109 / 281474976710656,
  407601957318488 / 281474976710656,
  716595723250117 / 281474976710656,
  491523659201810 / 281474976710656,
  758498544949944 / 281474976710656,
  633909998150741 / 281474976710656,
  672957968151720 / 281474976710656,
  800626188505532 / 281474976710656,
  614640693283883 / 281474976710656,
  914936358677769 / 281474976710656,
  695422443408982 / 281474976710656,
  928771317420566 / 281474976710656,
  889496937780192 / 281474976710656,
  869543567513206 / 281474976710656,
  1062293599730230 / 281474976710656,
  823437276817773 / 281474976710656,
  1095996163891924 / 281474976710656,
  865592826138387 / 281474976710656,
  996366092105343 / 281474976710656,
  994361762934208 / 281474976710656,
  885105363852424 / 281474976710656,
  1128312720545245 / 281474976710656,
  888085417606384 / 281474976710656,
  1173982873633267 / 281474976710656,
  1023293777361843 / 281474976710656,
  1109312927298790 / 281474976710656,
  1188947027076589 / 281474976710656,
  1008533094477505 / 281474976710656,
  1258572347331247 / 281474976710656,
  981318599162919 / 281474976710656,
  1194007525916111 / 281474976710656,
  1075446724642178 / 281474976710656,
  1075333179623428 / 281474976710656,
  1229695152481471 / 281474976710656,
  1025308033011931 / 281474976710656,
  1323784992783906 / 281474976710656,
  1100187135897328 / 281474976710656,
  1285566099647218 / 281474976710656,
  1244337372646213 / 281474976710656,
  1159835290160403 / 281474976710656,
  1344488479934079 / 281474976710656,
  1072854073232030 / 281474976710656,
  1330534652900679 / 281474976710656,
  1119850101057254 / 281474976710656,
  1233079725871612 / 281474976710656,
  1276021855092838 / 281474976710656,
  1151380704238248 / 281474976710656,
  1414763125945807 / 281474976710656,
  1165209230553449 / 281474976710656,
  1420802610396770 / 281474976710656,
  1269076552696640 / 281474976710656,
  1296945220389202 / 281474976710656,
  1382237348898412 / 281474976710656,
  1165068339030535 / 281474976710656,
  1420409878817962 / 281474976710656,
  1156986459378230 / 281474976710656,
  1365433765987765 / 281474976710656,
  1293211833638184 / 281474976710656,
  1276193952277666 / 281474976710656,
  1461728024369746 / 281474976710656,
  1236397477131823 / 281474976710656,
  1518737008095553 / 281474976710656,
  1285611826058946 / 281474976710656,
  1420495262272931 / 281474976710656,
  1389481072680159 / 281474976710656,
  1264791252629594 / 281474976710656,
  1470204234040305 / 281474976710656
]

def diagAll : Bool :=
  (List.range 71).all fun n => diagCheck n (diagLo.getD n 0) (diagHi.getD n 0)

set_option maxRecDepth 100000 in
theorem diagAll_true : diagAll = true := by decide +kernel

/-- **The diagonal of the `L = 6/5` low block**: `cvsEntry M (6/5) n n` for `n = 0, …, 70` and
every prime cutoff `M ≥ 3`, each box of width at most `2·10⁻⁸`. -/
theorem diag_mem {M : ℕ} (hM : 3 ≤ M) {n : ℕ} (hn : n ≤ 70) :
    ((diagLo.getD n 0 : ℚ) : ℝ) ≤ cvsEntry M (6 / 5) n n ∧
      cvsEntry M (6 / 5) n n ≤ ((diagHi.getD n 0 : ℚ) : ℝ) := by
  have h := diagAll_true
  simp only [diagAll, List.all_eq_true, List.mem_range] at h
  exact diagCheck_sound hM (h n (by omega))

theorem hplus_neg (r : ℝ) : hplus (-r) = hplus r := by
  simp only [hplus_eq_tsum, archTerm, neg_sq]

theorem Dser_neg (r : ℝ) : Dser (-r) = Dser r := by
  simp only [Dser, neg_sq]

/-- The diagonal is even in `n`. -/
theorem cvsEntry_diag_neg {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (6 / 5) (-n) (-n) = cvsEntry M (6 / 5) n n := by
  rw [cvsEntry_diag_eq hM, cvsEntry_diag_eq hM]
  have e : 2 * Real.pi * ((-n : ℤ) : ℝ) / (6 / 5) = -(2 * Real.pi * (n : ℝ) / (6 / 5)) := by
    push_cast; ring
  rw [e, hplus_neg, Dser_neg]
  have c2 : Real.cos (-(2 * Real.pi * (n : ℝ) / (6 / 5)) * Real.log 2) =
      Real.cos (2 * Real.pi * (n : ℝ) / (6 / 5) * Real.log 2) := by rw [neg_mul, Real.cos_neg]
  have c3 : Real.cos (-(2 * Real.pi * (n : ℝ) / (6 / 5)) * Real.log 3) =
      Real.cos (2 * Real.pi * (n : ℝ) / (6 / 5) * Real.log 3) := by rw [neg_mul, Real.cos_neg]
  rw [c2, c3]

end AEGIS.CvSDiagL12V1

#print axioms AEGIS.CvSDiagL12V1.log_bounds
#print axioms AEGIS.CvSDiagL12V1.idiv_bounds
#print axioms AEGIS.CvSDiagL12V1.lpi_bounds
#print axioms AEGIS.CvSDiagL12V1.hplus_bounds
#print axioms AEGIS.CvSDiagL12V1.D_bounds
#print axioms AEGIS.CvSDiagL12V1.cvsEntry_diag_eq
#print axioms AEGIS.CvSDiagL12V1.Pd_bounds
#print axioms AEGIS.CvSDiagL12V1.diagCheck_sound
#print axioms AEGIS.CvSDiagL12V1.diagAll_true
#print axioms AEGIS.CvSDiagL12V1.diag_mem
#print axioms AEGIS.CvSDiagL12V1.cvsEntry_diag_neg
