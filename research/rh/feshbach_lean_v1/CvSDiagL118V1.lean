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
import CvSTauL118V1
import CvSTauPrimeL118V1
import CvSDiagL12V1

/-!
# The diagonal entries `cvsEntry M (11/8) n n`, `n = 0, …, 70`

The diagonal of `CvSDiagL12V1` with the window moved to `L = 11/8`. For every prime cutoff `M ≥ 3`,
with `ω = 2πn/L`,

  `cvsEntry M L n n = L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`

(`cvsEntry_diag_eq`; the prime powers `≥ 4` sit at the window end, `CvSTauPrimeL118V1.node_big`).
The logarithms, the interval division, `h₊` (`hplus_bounds`) and the window-free parts of the
telescoped tail are those of `CvSDiagL12V1`; here `e^{−c_k L} = (e^{−11/16})^{4k+1}`
(`CvSTauL118V1.E_bounds`) and `ω = 16πn/11`. `diag_mem`: one `decide +kernel` over `n = 0, …, 70`,
every box of width at most `2·10⁻⁸` (data from `tools/gen_diag118.py`, untrusted);
`cvsEntry_diag_neg` gives `n ≤ −1`. Not RH.
-/

open Finset

namespace AEGIS.CvSDiagL118V1

open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSDiagTelV1
open AEGIS.CvSTauL118V1 (Elo Ehi E_bounds)
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds cw cw_cast rdn rup rdn_le le_rup)
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds s2Lo s3Lo thLo sinPiLo
  sinPiHi sinPi_bounds mul_lo mul_hi piLo_nonneg w2Lo w2Hi w3Lo w3Hi w2_bounds w3_bounds)
open AEGIS.CvSTauPrimeL118V1 (node_one node_two node_big)
open AEGIS.CvSDiagL12V1 (logOk aK aK_cast idivLo idivHi idiv_bounds hpLo hpHi hplus_bounds fLo fHi
  gDLo gDHi ppw_zero)

/-! ### The archimedean diagonal series for `r² ∈ [ql, qh]` -/

/-- Outward-rounded `e^{−c_k·11/8}`, `k < 40` (checked once by `E_check`). -/
def EloL : List ℚ := [
  9275605431009477473 / 18446744073709551616,
  592969616601756849 / 18446744073709551616,
  37907279349911714 / 18446744073709551616,
  2423331293005048 / 18446744073709551616,
  154918386557097 / 18446744073709551616,
  9903601114189 / 18446744073709551616,
  633116037474 / 18446744073709551616,
  40473754171 / 18446744073709551616,
  2587400539 / 18446744073709551616,
  165406982 / 18446744073709551616,
  10574114 / 18446744073709551616,
  675980 / 18446744073709551616,
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
  9275605431009477474 / 18446744073709551616,
  592969616601756850 / 18446744073709551616,
  37907279349911715 / 18446744073709551616,
  2423331293005049 / 18446744073709551616,
  154918386557098 / 18446744073709551616,
  9903601114190 / 18446744073709551616,
  633116037475 / 18446744073709551616,
  40473754172 / 18446744073709551616,
  2587400540 / 18446744073709551616,
  165406983 / 18446744073709551616,
  10574115 / 18446744073709551616,
  675981 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616,
  43214 / 18446744073709551616
]

/-- An upper bound for `e^{−c_40·11/8}`. -/
def ehK : ℚ := 43214 / 18446744073709551616

theorem E_check : ((List.range 40).all fun k => decide (EloL.getD k 0 ≤ Elo k) &&
    decide (Ehi k ≤ EhiL.getD k 1) && decide (EhiL.getD k 1 ≤ 1)) = true ∧ Ehi 40 ≤ ehK := by
  decide +kernel

theorem EL_bounds {k : ℕ} (hk : k < 40) :
    ((EloL.getD k 0 : ℚ) : ℝ) ≤ Real.exp (-archWidth k * (11 / 8)) ∧
      Real.exp (-archWidth k * (11 / 8)) ≤ ((EhiL.getD k 1 : ℚ) : ℝ) ∧
      ((EhiL.getD k 1 : ℚ) : ℝ) ≤ 1 := by
  have h := E_check.1
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk
  have e := E_bounds k
  refine ⟨le_trans (by exact_mod_cast h1) e.1, le_trans e.2.1 (by exact_mod_cast h2),
    by exact_mod_cast h3⟩

def DhLo (ql qh : ℚ) : ℚ := ∑ k ∈ range 40,
  rdn (min ((1 - EhiL.getD k 1) * fLo k ql qh) ((1 - EloL.getD k 0) * fLo k ql qh))
def DhHi (ql qh : ℚ) : ℚ := ∑ k ∈ range 40,
  rup (max ((1 - EhiL.getD k 1) * fHi k ql qh) ((1 - EloL.getD k 0) * fHi k ql qh))

def hDHi : ℚ := 1 / (4 * aK ^ 5) + ehK / (2 * aK)

def DLo (ql qh : ℚ) : ℚ := DhLo ql qh + gDLo ql qh - hDHi
def DHi (ql qh : ℚ) : ℚ := DhHi ql qh + gDHi ql qh + hDHi

/-- The archimedean diagonal series `D(r) = Σ_k (1 − e^{−c_k L})(c_k² − r²)/(c_k² + r²)²`. -/
noncomputable def Dser (r : ℝ) : ℝ :=
  ∑' k, (1 - Real.exp (-archWidth k * (11 / 8))) * (archWidth k ^ 2 - r ^ 2) /
    (archWidth k ^ 2 + r ^ 2) ^ 2

theorem D_bounds {r : ℝ} {ql qh : ℚ} (h0 : 0 ≤ ql) (h1 : (ql : ℝ) ≤ r ^ 2) (h2 : r ^ 2 ≤ qh) :
    (DLo ql qh : ℝ) ≤ Dser r ∧ Dser r ≤ DHi ql qh := by
  have T := abs_le.mp (diagSeries_tel r (L := 11 / 8) (by norm_num) (K := 40) (by norm_num))
  simp only [gD, hD] at T
  rw [← aK_cast] at T
  have h0' : (0 : ℝ) ≤ ql := by exact_mod_cast h0
  have ha : (0 : ℝ) < aK := by norm_num [aK]
  -- the head
  have hcast : ∀ k : ℕ, ((cw k : ℚ) : ℝ) = archWidth k := cw_cast
  have H : (DhLo ql qh : ℝ) ≤ ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (11 / 8))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
      ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (11 / 8))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ≤ ((DhHi ql qh : ℚ) : ℝ) := by
    simp only [DhLo, DhHi]
    push_cast
    have hterm : ∀ k ∈ range 40, ((min ((1 - EhiL.getD k 1) * fLo k ql qh)
          ((1 - EloL.getD k 0) * fLo k ql qh) : ℚ) : ℝ) ≤
          (1 - Real.exp (-archWidth k * (11 / 8))) * (archWidth k ^ 2 - r ^ 2) /
            (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
        (1 - Real.exp (-archWidth k * (11 / 8))) * (archWidth k ^ 2 - r ^ 2) /
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
  have hE : Real.exp (-archWidth 40 * (11 / 8)) ≤ ehK := by
    have e := (E_bounds 40).2.1
    exact e.trans (by exact_mod_cast E_check.2)
  have hT : 1 / (4 * (aK : ℝ) ^ 5) + Real.exp (-archWidth 40 * (11 / 8)) / (2 * aK) ≤ hDHi := by
    simp only [hDHi]; push_cast
    have : Real.exp (-archWidth 40 * (11 / 8)) / (2 * aK) ≤ (ehK : ℝ) / (2 * aK) := by gcongr
    linarith
  simp only [DLo, DHi, gDLo, gDHi, Dser]
  push_cast
  constructor <;> linarith [T.1, T.2, H.1, H.2, C.1, C.2]

/-! ### The diagonal entry `cvsEntry M (11/8) n n` -/

open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSQuadV1 AEGIS.CvSArchDiagV1 AEGIS.CvSRowTailV1
open AEGIS.RHKreinZetaBridgeV3

/-- **The diagonal entry at `L = 11/8`**: `L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`
with `ω = 2πn/L`, for every prime cutoff `M ≥ 3`. -/
theorem cvsEntry_diag_eq {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (11 / 8) n n = 11 / 8 * hplus (2 * Real.pi * n / (11 / 8)) +
      2 * Dser (2 * Real.pi * n / (11 / 8)) -
      11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8)) * Real.cos (2 * Real.pi * n / (11 / 8) * Real.log 2) +
        ppw 2 * (1 - Real.log 3 / (11 / 8)) * Real.cos (2 * Real.pi * n / (11 / 8) * Real.log 3)) := by
  have hL : (0 : ℝ) < 11 / 8 := by norm_num
  rw [cvsEntry, hplus_cosB_diag hL n]
  simp only [blockFn_diag hL n]
  have hz : ∀ j ∈ range M, j ∉ range 3 → ppw j * (Real.pi * (11 / 8 * diagProfile (11 / 8) n
      (min |Real.log ((j + 1 : ℕ) : ℝ)| (11 / 8)))) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    have h := node_big hj
    simp only [node] at h
    rw [h, diagProfile]
    simp
  rw [← sum_subset (range_mono hM) hz]
  have h1 : min |Real.log ((1 + 1 : ℕ) : ℝ)| (11 / 8 : ℝ) = Real.log 2 := node_one
  have h2 : min |Real.log ((2 + 1 : ℕ) : ℝ)| (11 / 8 : ℝ) = Real.log 3 := node_two
  simp only [sum_range_succ, sum_range_zero, ppw_zero, zero_mul, zero_add, h1, h2]
  simp only [diagProfile, Dser]
  field_simp
  ring

/-! ### The prime part of the diagonal -/

def cf2Lo : ℚ := 11 / 8 * w2Lo * (1 - 8 * l2Hi / 11)
def cf2Hi : ℚ := 11 / 8 * w2Hi * (1 - 8 * l2Lo / 11)
def cf3Lo : ℚ := 11 / 8 * w3Lo * (1 - 8 * l3Hi / 11)
def cf3Hi : ℚ := 11 / 8 * w3Hi * (1 - 8 * l3Lo / 11)

theorem cf_bounds :
    ((cf2Lo : ℝ) ≤ 11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8))) ∧
      11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8))) ≤ cf2Hi) ∧
    ((cf3Lo : ℝ) ≤ 11 / 8 * (ppw 2 * (1 - Real.log 3 / (11 / 8))) ∧
      11 / 8 * (ppw 2 * (1 - Real.log 3 / (11 / 8))) ≤ cf3Hi) ∧
    (0 : ℝ) ≤ cf2Lo ∧ (0 : ℝ) ≤ cf3Lo := by
  have a := log2_bounds
  have b := log3_bounds
  have w2 := w2_bounds
  have w3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have p2 : (0 : ℝ) ≤ 1 - 8 * (l2Hi : ℝ) / 11 := by norm_num [l2Hi]
  have p3 : (0 : ℝ) ≤ 1 - 8 * (l3Hi : ℝ) / 11 := by norm_num [l3Hi]
  simp only [cf2Lo, cf2Hi, cf3Lo, cf3Hi]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by positivity, by positivity⟩
  · have := mul_le_mul w2.1 (show 1 - 8 * (l2Hi : ℝ) / 11 ≤ 1 - Real.log 2 / (11 / 8) by linarith [a.2])
      p2 (by linarith)
    nlinarith
  · have := mul_le_mul w2.2 (show 1 - Real.log 2 / (11 / 8) ≤ 1 - 8 * (l2Lo : ℝ) / 11 by linarith [a.1])
      (by linarith [a.2]) (by linarith)
    nlinarith
  · have := mul_le_mul w3.1 (show 1 - 8 * (l3Hi : ℝ) / 11 ≤ 1 - Real.log 3 / (11 / 8) by linarith [b.2])
      p3 (by linarith)
    nlinarith
  · have := mul_le_mul w3.2 (show 1 - Real.log 3 / (11 / 8) ≤ 1 - 8 * (l3Lo : ℝ) / 11 by linarith [b.1])
      (by linarith [b.2]) (by linarith)
    nlinarith

theorem cos_eq_sin (n : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * (n : ℤ) / (11 / 8) * x) = Real.sin (Real.pi * (16 * n * x / 11 + 1 / 2)) := by
  rw [← Real.sin_add_pi_div_two]
  congr 1
  push_cast
  ring

def co2l (n : ℕ) : ℚ := sinPiLo (16 * n * l2Lo / 11 + 1 / 2) (16 * n * l2Hi / 11 + 1 / 2)
def co2h (n : ℕ) : ℚ := sinPiHi (16 * n * l2Lo / 11 + 1 / 2) (16 * n * l2Hi / 11 + 1 / 2)
def co3l (n : ℕ) : ℚ := sinPiLo (16 * n * l3Lo / 11 + 1 / 2) (16 * n * l3Hi / 11 + 1 / 2)
def co3h (n : ℕ) : ℚ := sinPiHi (16 * n * l3Lo / 11 + 1 / 2) (16 * n * l3Hi / 11 + 1 / 2)

def PdLo (n : ℕ) : ℚ := min (cf2Lo * co2l n) (cf2Hi * co2l n) + min (cf3Lo * co3l n) (cf3Hi * co3l n)
def PdHi (n : ℕ) : ℚ := max (cf2Lo * co2h n) (cf2Hi * co2h n) + max (cf3Lo * co3h n) (cf3Hi * co3h n)

theorem Pd_bounds (n : ℕ) (h2 : |thLo (16 * n * l2Lo / 11 + 1 / 2)| ≤ 2)
    (h3 : |thLo (16 * n * l3Lo / 11 + 1 / 2)| ≤ 2) :
    (PdLo n : ℝ) ≤ 11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (11 / 8) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (11 / 8)) * Real.cos (2 * Real.pi * (n : ℤ) / (11 / 8) * Real.log 3)) ∧
    11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (11 / 8) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (11 / 8)) * Real.cos (2 * Real.pi * (n : ℤ) / (11 / 8) * Real.log 3)) ≤
      PdHi n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have l2 := log2_bounds
  have l3 := log3_bounds
  have s2 : (co2l n : ℝ) ≤ Real.sin (Real.pi * (16 * n * Real.log 2 / 11 + 1 / 2)) ∧
      Real.sin (Real.pi * (16 * n * Real.log 2 / 11 + 1 / 2)) ≤ co2h n :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have s3 : (co3l n : ℝ) ≤ Real.sin (Real.pi * (16 * n * Real.log 3 / 11 + 1 / 2)) ∧
      Real.sin (Real.pi * (16 * n * Real.log 3 / 11 + 1 / 2)) ≤ co3h n :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  obtain ⟨c2, c3, z2, z3⟩ := cf_bounds
  rw [cos_eq_sin, cos_eq_sin]
  have e : 11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8)) * Real.sin (Real.pi * (16 * n * Real.log 2 / 11 + 1 / 2)) +
      ppw 2 * (1 - Real.log 3 / (11 / 8)) * Real.sin (Real.pi * (16 * n * Real.log 3 / 11 + 1 / 2))) =
      11 / 8 * (ppw 1 * (1 - Real.log 2 / (11 / 8))) * Real.sin (Real.pi * (16 * n * Real.log 2 / 11 + 1 / 2)) +
      11 / 8 * (ppw 2 * (1 - Real.log 3 / (11 / 8))) * Real.sin (Real.pi * (16 * n * Real.log 3 / 11 + 1 / 2)) := by
    ring
  rw [e]
  simp only [PdLo, PdHi]
  push_cast
  constructor
  · exact add_le_add (mul_lo z2 c2.1 c2.2 s2.1) (mul_lo z3 c3.1 c3.2 s3.1)
  · exact add_le_add (mul_hi z2 c2.1 c2.2 s2.2) (mul_hi z3 c3.1 c3.2 s3.2)

/-! ### The kernel check -/

def ql (n : ℕ) : ℚ := (16 * piLo * n / 11) ^ 2
def qh (n : ℕ) : ℚ := (16 * piHi * n / 11) ^ 2

theorem q_bounds (n : ℕ) : (ql n : ℝ) ≤ (2 * Real.pi * (n : ℤ) / (11 / 8)) ^ 2 ∧
    (2 * Real.pi * (n : ℤ) / (11 / 8)) ^ 2 ≤ qh n := by
  have hp := pi_bounds
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp0 : (0 : ℝ) ≤ piLo := piLo_nonneg
  have e : 2 * Real.pi * ((n : ℤ) : ℝ) / (11 / 8) = 16 * Real.pi * n / 11 := by push_cast; ring
  rw [e]
  simp only [ql, qh]
  push_cast
  constructor
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.1.le) 2
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.2.le) 2

def entryLo (n : ℕ) : ℚ := 11 / 8 * hpLo (ql n) (qh n) + 2 * DLo (ql n) (qh n) - PdHi n
def entryHi (n : ℕ) : ℚ := 11 / 8 * hpHi (ql n) (qh n) + 2 * DHi (ql n) (qh n) - PdLo n

def diagCheck (n : ℕ) (lo hi : ℚ) : Bool :=
  logOk (aK ^ 2 + ql n) && logOk (aK ^ 2 + qh n) &&
    decide (|thLo (16 * n * l2Lo / 11 + 1 / 2)| ≤ 2) && decide (|thLo (16 * n * l3Lo / 11 + 1 / 2)| ≤ 2) &&
    decide (lo ≤ entryLo n) && decide (entryHi n ≤ hi)

theorem diagCheck_sound {M : ℕ} (hM : 3 ≤ M) {n : ℕ} {lo hi : ℚ} (h : diagCheck n lo hi = true) :
    (lo : ℝ) ≤ cvsEntry M (11 / 8) n n ∧ cvsEntry M (11 / 8) n n ≤ hi := by
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

/-- Boxes for `cvsEntry M (11/8) n n`, `n = 0, …, 70` (untrusted, from `tools/gen_diag118.py`). -/
def diagLo : List ℚ := [
  -1080932730301589 / 281474976710656,
  40565966620458 / 281474976710656,
  39348107168222 / 281474976710656,
  568993500744042 / 281474976710656,
  193711745702691 / 281474976710656,
  587854753667421 / 281474976710656,
  357613544800786 / 281474976710656,
  897424556552747 / 281474976710656,
  574316994982731 / 281474976710656,
  874506318528259 / 281474976710656,
  487586498333830 / 281474976710656,
  961585640502145 / 281474976710656,
  743359944616202 / 281474976710656,
  1121940242159092 / 281474976710656,
  683484976927300 / 281474976710656,
  1000844647571486 / 281474976710656,
  756687094532508 / 281474976710656,
  1229247055616135 / 281474976710656,
  899939156854535 / 281474976710656,
  1140763917225693 / 281474976710656,
  774671806419366 / 281474976710656,
  1198496546553658 / 281474976710656,
  1001593639448321 / 281474976710656,
  1316810389597803 / 281474976710656,
  909190876075494 / 281474976710656,
  1175427822799934 / 281474976710656,
  975701173954236 / 281474976710656,
  1385186230964931 / 281474976710656,
  1093631103839878 / 281474976710656,
  1270717499179361 / 281474976710656,
  961688078343743 / 281474976710656,
  1325309152602568 / 281474976710656,
  1180433147354032 / 281474976710656,
  1419995472350936 / 281474976710656,
  1071435032521897 / 281474976710656,
  1272982561637884 / 281474976710656,
  1142586909146359 / 281474976710656,
  1474121279668661 / 281474976710656,
  1243592123373234 / 281474976710656,
  1342743661987387 / 281474976710656,
  1112423029073113 / 281474976710656,
  1400966656955852 / 281474976710656,
  1327592107819351 / 281474976710656,
  1477432469765010 / 281474976710656,
  1206829220136682 / 281474976710656,
  1330255626831565 / 281474976710656,
  1285889570559167 / 281474976710656,
  1526137483491264 / 281474976710656,
  1372457233175580 / 281474976710656,
  1381998157759053 / 281474976710656,
  1244955999472276 / 281474976710656,
  1446798031663079 / 281474976710656,
  1457624887024319 / 281474976710656,
  1507561344843028 / 281474976710656,
  1327174856170894 / 281474976710656,
  1363348772520555 / 281474976710656,
  1415129907821940 / 281474976710656,
  1555484884931051 / 281474976710656,
  1487975775818798 / 281474976710656,
  1401263568757412 / 281474976710656,
  1365516800287673 / 281474976710656,
  1474313450719732 / 281474976710656,
  1575521805100290 / 281474976710656,
  1520922098331960 / 281474976710656,
  1436455207172896 / 281474976710656,
  1381924297074027 / 281474976710656,
  1533373889551385 / 281474976710656,
  1571108137766769 / 281474976710656,
  1592521819504412 / 281474976710656,
  1408898889530742 / 281474976710656,
  1475823397266514 / 281474976710656
]

/-- Upper ends. -/
def diagHi : List ℚ := [
  -1080932725368509 / 281474976710656,
  40565971553538 / 281474976710656,
  39348112101302 / 281474976710656,
  568993505677122 / 281474976710656,
  193711750635771 / 281474976710656,
  587854758600501 / 281474976710656,
  357613549733867 / 281474976710656,
  897424561485828 / 281474976710656,
  574316999915812 / 281474976710656,
  874506323461340 / 281474976710656,
  487586503266910 / 281474976710656,
  961585645435226 / 281474976710656,
  743359949549282 / 281474976710656,
  1121940247092172 / 281474976710656,
  683484981860380 / 281474976710656,
  1000844652504566 / 281474976710656,
  756687099465588 / 281474976710656,
  1229247060549216 / 281474976710656,
  899939161787615 / 281474976710656,
  1140763922158773 / 281474976710656,
  774671811352446 / 281474976710656,
  1198496551486738 / 281474976710656,
  1001593644381401 / 281474976710656,
  1316810394530883 / 281474976710656,
  909190881008574 / 281474976710656,
  1175427827733015 / 281474976710656,
  975701178887316 / 281474976710656,
  1385186235898011 / 281474976710656,
  1093631108772958 / 281474976710656,
  1270717504112442 / 281474976710656,
  961688083276823 / 281474976710656,
  1325309157535648 / 281474976710656,
  1180433152287113 / 281474976710656,
  1419995477284017 / 281474976710656,
  1071435037454977 / 281474976710656,
  1272982566570965 / 281474976710656,
  1142586914079439 / 281474976710656,
  1474121284601741 / 281474976710656,
  1243592128306315 / 281474976710656,
  1342743666920467 / 281474976710656,
  1112423034006193 / 281474976710656,
  1400966661888932 / 281474976710656,
  1327592112752432 / 281474976710656,
  1477432474698091 / 281474976710656,
  1206829225069762 / 281474976710656,
  1330255631764645 / 281474976710656,
  1285889575492247 / 281474976710656,
  1526137488424344 / 281474976710656,
  1372457238108661 / 281474976710656,
  1381998162692134 / 281474976710656,
  1244956004405356 / 281474976710656,
  1446798036596159 / 281474976710656,
  1457624891957399 / 281474976710656,
  1507561349776108 / 281474976710656,
  1327174861103975 / 281474976710656,
  1363348777453635 / 281474976710656,
  1415129912755020 / 281474976710656,
  1555484889864131 / 281474976710656,
  1487975780751879 / 281474976710656,
  1401263573690493 / 281474976710656,
  1365516805220753 / 281474976710656,
  1474313455652812 / 281474976710656,
  1575521810033370 / 281474976710656,
  1520922103265041 / 281474976710656,
  1436455212105977 / 281474976710656,
  1381924302007107 / 281474976710656,
  1533373894484466 / 281474976710656,
  1571108142699849 / 281474976710656,
  1592521824437492 / 281474976710656,
  1408898894463822 / 281474976710656,
  1475823402199594 / 281474976710656
]

def diagAll : Bool :=
  (List.range 71).all fun n => diagCheck n (diagLo.getD n 0) (diagHi.getD n 0)

set_option maxRecDepth 100000 in
theorem diagAll_true : diagAll = true := by decide +kernel

/-- **The diagonal of the `L = 11/8` low block**: `cvsEntry M (11/8) n n` for `n = 0, …, 70` and
every prime cutoff `M ≥ 3`, each box of width at most `2·10⁻⁸`. -/
theorem diag_mem {M : ℕ} (hM : 3 ≤ M) {n : ℕ} (hn : n ≤ 70) :
    ((diagLo.getD n 0 : ℚ) : ℝ) ≤ cvsEntry M (11 / 8) n n ∧
      cvsEntry M (11 / 8) n n ≤ ((diagHi.getD n 0 : ℚ) : ℝ) := by
  have h := diagAll_true
  simp only [diagAll, List.all_eq_true, List.mem_range] at h
  exact diagCheck_sound hM (h n (by omega))

theorem Dser_neg (r : ℝ) : Dser (-r) = Dser r := by
  simp only [Dser, neg_sq]

/-- The diagonal is even in `n`. -/
theorem cvsEntry_diag_neg {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (11 / 8) (-n) (-n) = cvsEntry M (11 / 8) n n := by
  rw [cvsEntry_diag_eq hM, cvsEntry_diag_eq hM]
  have e : 2 * Real.pi * ((-n : ℤ) : ℝ) / (11 / 8) = -(2 * Real.pi * (n : ℝ) / (11 / 8)) := by
    push_cast; ring
  rw [e, hplus_neg, Dser_neg]
  have c2 : Real.cos (-(2 * Real.pi * (n : ℝ) / (11 / 8)) * Real.log 2) =
      Real.cos (2 * Real.pi * (n : ℝ) / (11 / 8) * Real.log 2) := by rw [neg_mul, Real.cos_neg]
  have c3 : Real.cos (-(2 * Real.pi * (n : ℝ) / (11 / 8)) * Real.log 3) =
      Real.cos (2 * Real.pi * (n : ℝ) / (11 / 8) * Real.log 3) := by rw [neg_mul, Real.cos_neg]
  rw [c2, c3]

end AEGIS.CvSDiagL118V1

#print axioms AEGIS.CvSDiagL118V1.D_bounds
#print axioms AEGIS.CvSDiagL118V1.cvsEntry_diag_eq
#print axioms AEGIS.CvSDiagL118V1.Pd_bounds
#print axioms AEGIS.CvSDiagL118V1.diagCheck_sound
#print axioms AEGIS.CvSDiagL118V1.diagAll_true
#print axioms AEGIS.CvSDiagL118V1.diag_mem
#print axioms AEGIS.CvSDiagL118V1.cvsEntry_diag_neg
