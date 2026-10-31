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
import CvSTauL43V1
import CvSTauPrimeL43V1
import CvSDiagL12V1

/-!
# The diagonal entries `cvsEntry M (4/3) n n`, `n = 0, …, 70`

The diagonal of `CvSDiagL12V1` with the window moved to `L = 4/3`. For every prime cutoff `M ≥ 3`,
with `ω = 2πn/L`,

  `cvsEntry M L n n = L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`

(`cvsEntry_diag_eq`; the prime powers `≥ 4` sit at the window end, `CvSTauPrimeL43V1.node_big`).
The logarithms, the interval division, `h₊` (`hplus_bounds`) and the window-free parts of the
telescoped tail are those of `CvSDiagL12V1`; here `e^{−c_k L} = (e^{−2/3})^{4k+1}`
(`CvSTauL43V1.E_bounds`) and `ω = 3πn/2`. `diag_mem`: one `decide +kernel` over `n = 0, …, 70`,
every box of width at most `2·10⁻⁸` (data from `tools/gen_diag43.py`, untrusted);
`cvsEntry_diag_neg` gives `n ≤ −1`. Not RH.
-/

open Finset

namespace AEGIS.CvSDiagL43V1

open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSDiagTelV1
open AEGIS.CvSTauL43V1 (Elo Ehi E_bounds)
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds cw cw_cast rdn rup rdn_le le_rup)
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds s2Lo s3Lo thLo sinPiLo
  sinPiHi sinPi_bounds mul_lo mul_hi piLo_nonneg w2Lo w2Hi w3Lo w3Hi w2_bounds w3_bounds)
open AEGIS.CvSTauPrimeL43V1 (node_one node_two node_big)
open AEGIS.CvSDiagL12V1 (logOk aK aK_cast idivLo idivHi idiv_bounds hpLo hpHi hplus_bounds fLo fHi
  gDLo gDHi ppw_zero)

/-! ### The archimedean diagonal series for `r² ∈ [ql, qh]` -/

/-- Outward-rounded `e^{−c_k·4/3}`, `k < 40` (checked once by `E_check`). -/
def EloL : List ℚ := [
  9470874197855498412 / 18446744073709551616,
  658069025363982135 / 18446744073709551616,
  45724907025114798 / 18446744073709551616,
  3177124346946699 / 18446744073709551616,
  220757564589846 / 18446744073709551616,
  15338997471243 / 18446744073709551616,
  1065806482599 / 18446744073709551616,
  74055912746 / 18446744073709551616,
  5145660401 / 18446744073709551616,
  357538243 / 18446744073709551616,
  24842991 / 18446744073709551616,
  1726176 / 18446744073709551616,
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
  9470874197855498413 / 18446744073709551616,
  658069025363982136 / 18446744073709551616,
  45724907025114799 / 18446744073709551616,
  3177124346946700 / 18446744073709551616,
  220757564589847 / 18446744073709551616,
  15338997471244 / 18446744073709551616,
  1065806482600 / 18446744073709551616,
  74055912747 / 18446744073709551616,
  5145660402 / 18446744073709551616,
  357538244 / 18446744073709551616,
  24842992 / 18446744073709551616,
  1726177 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616,
  119941 / 18446744073709551616
]

/-- An upper bound for `e^{−c_40·4/3}`. -/
def ehK : ℚ := 119941 / 18446744073709551616

theorem E_check : ((List.range 40).all fun k => decide (EloL.getD k 0 ≤ Elo k) &&
    decide (Ehi k ≤ EhiL.getD k 1) && decide (EhiL.getD k 1 ≤ 1)) = true ∧ Ehi 40 ≤ ehK := by
  decide +kernel

theorem EL_bounds {k : ℕ} (hk : k < 40) :
    ((EloL.getD k 0 : ℚ) : ℝ) ≤ Real.exp (-archWidth k * (4 / 3)) ∧
      Real.exp (-archWidth k * (4 / 3)) ≤ ((EhiL.getD k 1 : ℚ) : ℝ) ∧
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
  ∑' k, (1 - Real.exp (-archWidth k * (4 / 3))) * (archWidth k ^ 2 - r ^ 2) /
    (archWidth k ^ 2 + r ^ 2) ^ 2

theorem D_bounds {r : ℝ} {ql qh : ℚ} (h0 : 0 ≤ ql) (h1 : (ql : ℝ) ≤ r ^ 2) (h2 : r ^ 2 ≤ qh) :
    (DLo ql qh : ℝ) ≤ Dser r ∧ Dser r ≤ DHi ql qh := by
  have T := abs_le.mp (diagSeries_tel r (L := 4 / 3) (by norm_num) (K := 40) (by norm_num))
  simp only [gD, hD] at T
  rw [← aK_cast] at T
  have h0' : (0 : ℝ) ≤ ql := by exact_mod_cast h0
  have ha : (0 : ℝ) < aK := by norm_num [aK]
  -- the head
  have hcast : ∀ k : ℕ, ((cw k : ℚ) : ℝ) = archWidth k := cw_cast
  have H : (DhLo ql qh : ℝ) ≤ ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (4 / 3))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
      ∑ k ∈ range 40, (1 - Real.exp (-archWidth k * (4 / 3))) *
        (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 ≤ ((DhHi ql qh : ℚ) : ℝ) := by
    simp only [DhLo, DhHi]
    push_cast
    have hterm : ∀ k ∈ range 40, ((min ((1 - EhiL.getD k 1) * fLo k ql qh)
          ((1 - EloL.getD k 0) * fLo k ql qh) : ℚ) : ℝ) ≤
          (1 - Real.exp (-archWidth k * (4 / 3))) * (archWidth k ^ 2 - r ^ 2) /
            (archWidth k ^ 2 + r ^ 2) ^ 2 ∧
        (1 - Real.exp (-archWidth k * (4 / 3))) * (archWidth k ^ 2 - r ^ 2) /
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
  have hE : Real.exp (-archWidth 40 * (4 / 3)) ≤ ehK := by
    have e := (E_bounds 40).2.1
    exact e.trans (by exact_mod_cast E_check.2)
  have hT : 1 / (4 * (aK : ℝ) ^ 5) + Real.exp (-archWidth 40 * (4 / 3)) / (2 * aK) ≤ hDHi := by
    simp only [hDHi]; push_cast
    have : Real.exp (-archWidth 40 * (4 / 3)) / (2 * aK) ≤ (ehK : ℝ) / (2 * aK) := by gcongr
    linarith
  simp only [DLo, DHi, gDLo, gDHi, Dser]
  push_cast
  constructor <;> linarith [T.1, T.2, H.1, H.2, C.1, C.2]

/-! ### The diagonal entry `cvsEntry M (4/3) n n` -/

open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSQuadV1 AEGIS.CvSArchDiagV1 AEGIS.CvSRowTailV1
open AEGIS.RHKreinZetaBridgeV3

/-- **The diagonal entry at `L = 4/3`**: `L h₊(ω) + 2 D(ω) − L Σ_{p=2,3} ppw_p (1 − log p/L) cos(ω log p)`
with `ω = 2πn/L`, for every prime cutoff `M ≥ 3`. -/
theorem cvsEntry_diag_eq {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (4 / 3) n n = 4 / 3 * hplus (2 * Real.pi * n / (4 / 3)) +
      2 * Dser (2 * Real.pi * n / (4 / 3)) -
      4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3)) * Real.cos (2 * Real.pi * n / (4 / 3) * Real.log 2) +
        ppw 2 * (1 - Real.log 3 / (4 / 3)) * Real.cos (2 * Real.pi * n / (4 / 3) * Real.log 3)) := by
  have hL : (0 : ℝ) < 4 / 3 := by norm_num
  rw [cvsEntry, hplus_cosB_diag hL n]
  simp only [blockFn_diag hL n]
  have hz : ∀ j ∈ range M, j ∉ range 3 → ppw j * (Real.pi * (4 / 3 * diagProfile (4 / 3) n
      (min |Real.log ((j + 1 : ℕ) : ℝ)| (4 / 3)))) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    have h := node_big hj
    simp only [node] at h
    rw [h, diagProfile]
    simp
  rw [← sum_subset (range_mono hM) hz]
  have h1 : min |Real.log ((1 + 1 : ℕ) : ℝ)| (4 / 3 : ℝ) = Real.log 2 := node_one
  have h2 : min |Real.log ((2 + 1 : ℕ) : ℝ)| (4 / 3 : ℝ) = Real.log 3 := node_two
  simp only [sum_range_succ, sum_range_zero, ppw_zero, zero_mul, zero_add, h1, h2]
  simp only [diagProfile, Dser]
  field_simp
  ring

/-! ### The prime part of the diagonal -/

def cf2Lo : ℚ := 4 / 3 * w2Lo * (1 - 3 * l2Hi / 4)
def cf2Hi : ℚ := 4 / 3 * w2Hi * (1 - 3 * l2Lo / 4)
def cf3Lo : ℚ := 4 / 3 * w3Lo * (1 - 3 * l3Hi / 4)
def cf3Hi : ℚ := 4 / 3 * w3Hi * (1 - 3 * l3Lo / 4)

theorem cf_bounds :
    ((cf2Lo : ℝ) ≤ 4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3))) ∧
      4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3))) ≤ cf2Hi) ∧
    ((cf3Lo : ℝ) ≤ 4 / 3 * (ppw 2 * (1 - Real.log 3 / (4 / 3))) ∧
      4 / 3 * (ppw 2 * (1 - Real.log 3 / (4 / 3))) ≤ cf3Hi) ∧
    (0 : ℝ) ≤ cf2Lo ∧ (0 : ℝ) ≤ cf3Lo := by
  have a := log2_bounds
  have b := log3_bounds
  have w2 := w2_bounds
  have w3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have p2 : (0 : ℝ) ≤ 1 - 3 * (l2Hi : ℝ) / 4 := by norm_num [l2Hi]
  have p3 : (0 : ℝ) ≤ 1 - 3 * (l3Hi : ℝ) / 4 := by norm_num [l3Hi]
  simp only [cf2Lo, cf2Hi, cf3Lo, cf3Hi]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by positivity, by positivity⟩
  · have := mul_le_mul w2.1 (show 1 - 3 * (l2Hi : ℝ) / 4 ≤ 1 - Real.log 2 / (4 / 3) by linarith [a.2])
      p2 (by linarith)
    nlinarith
  · have := mul_le_mul w2.2 (show 1 - Real.log 2 / (4 / 3) ≤ 1 - 3 * (l2Lo : ℝ) / 4 by linarith [a.1])
      (by linarith [a.2]) (by linarith)
    nlinarith
  · have := mul_le_mul w3.1 (show 1 - 3 * (l3Hi : ℝ) / 4 ≤ 1 - Real.log 3 / (4 / 3) by linarith [b.2])
      p3 (by linarith)
    nlinarith
  · have := mul_le_mul w3.2 (show 1 - Real.log 3 / (4 / 3) ≤ 1 - 3 * (l3Lo : ℝ) / 4 by linarith [b.1])
      (by linarith [b.2]) (by linarith)
    nlinarith

theorem cos_eq_sin (n : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * (n : ℤ) / (4 / 3) * x) = Real.sin (Real.pi * (3 * n * x / 2 + 1 / 2)) := by
  rw [← Real.sin_add_pi_div_two]
  congr 1
  push_cast
  ring

def co2l (n : ℕ) : ℚ := sinPiLo (3 * n * l2Lo / 2 + 1 / 2) (3 * n * l2Hi / 2 + 1 / 2)
def co2h (n : ℕ) : ℚ := sinPiHi (3 * n * l2Lo / 2 + 1 / 2) (3 * n * l2Hi / 2 + 1 / 2)
def co3l (n : ℕ) : ℚ := sinPiLo (3 * n * l3Lo / 2 + 1 / 2) (3 * n * l3Hi / 2 + 1 / 2)
def co3h (n : ℕ) : ℚ := sinPiHi (3 * n * l3Lo / 2 + 1 / 2) (3 * n * l3Hi / 2 + 1 / 2)

def PdLo (n : ℕ) : ℚ := min (cf2Lo * co2l n) (cf2Hi * co2l n) + min (cf3Lo * co3l n) (cf3Hi * co3l n)
def PdHi (n : ℕ) : ℚ := max (cf2Lo * co2h n) (cf2Hi * co2h n) + max (cf3Lo * co3h n) (cf3Hi * co3h n)

theorem Pd_bounds (n : ℕ) (h2 : |thLo (3 * n * l2Lo / 2 + 1 / 2)| ≤ 2)
    (h3 : |thLo (3 * n * l3Lo / 2 + 1 / 2)| ≤ 2) :
    (PdLo n : ℝ) ≤ 4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (4 / 3) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (4 / 3)) * Real.cos (2 * Real.pi * (n : ℤ) / (4 / 3) * Real.log 3)) ∧
    4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3)) *
        Real.cos (2 * Real.pi * (n : ℤ) / (4 / 3) * Real.log 2) +
      ppw 2 * (1 - Real.log 3 / (4 / 3)) * Real.cos (2 * Real.pi * (n : ℤ) / (4 / 3) * Real.log 3)) ≤
      PdHi n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have l2 := log2_bounds
  have l3 := log3_bounds
  have s2 : (co2l n : ℝ) ≤ Real.sin (Real.pi * (3 * n * Real.log 2 / 2 + 1 / 2)) ∧
      Real.sin (Real.pi * (3 * n * Real.log 2 / 2 + 1 / 2)) ≤ co2h n :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have s3 : (co3l n : ℝ) ≤ Real.sin (Real.pi * (3 * n * Real.log 3 / 2 + 1 / 2)) ∧
      Real.sin (Real.pi * (3 * n * Real.log 3 / 2 + 1 / 2)) ≤ co3h n :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  obtain ⟨c2, c3, z2, z3⟩ := cf_bounds
  rw [cos_eq_sin, cos_eq_sin]
  have e : 4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3)) * Real.sin (Real.pi * (3 * n * Real.log 2 / 2 + 1 / 2)) +
      ppw 2 * (1 - Real.log 3 / (4 / 3)) * Real.sin (Real.pi * (3 * n * Real.log 3 / 2 + 1 / 2))) =
      4 / 3 * (ppw 1 * (1 - Real.log 2 / (4 / 3))) * Real.sin (Real.pi * (3 * n * Real.log 2 / 2 + 1 / 2)) +
      4 / 3 * (ppw 2 * (1 - Real.log 3 / (4 / 3))) * Real.sin (Real.pi * (3 * n * Real.log 3 / 2 + 1 / 2)) := by
    ring
  rw [e]
  simp only [PdLo, PdHi]
  push_cast
  constructor
  · exact add_le_add (mul_lo z2 c2.1 c2.2 s2.1) (mul_lo z3 c3.1 c3.2 s3.1)
  · exact add_le_add (mul_hi z2 c2.1 c2.2 s2.2) (mul_hi z3 c3.1 c3.2 s3.2)

/-! ### The kernel check -/

def ql (n : ℕ) : ℚ := (3 * piLo * n / 2) ^ 2
def qh (n : ℕ) : ℚ := (3 * piHi * n / 2) ^ 2

theorem q_bounds (n : ℕ) : (ql n : ℝ) ≤ (2 * Real.pi * (n : ℤ) / (4 / 3)) ^ 2 ∧
    (2 * Real.pi * (n : ℤ) / (4 / 3)) ^ 2 ≤ qh n := by
  have hp := pi_bounds
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp0 : (0 : ℝ) ≤ piLo := piLo_nonneg
  have e : 2 * Real.pi * ((n : ℤ) : ℝ) / (4 / 3) = 3 * Real.pi * n / 2 := by push_cast; ring
  rw [e]
  simp only [ql, qh]
  push_cast
  constructor
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.1.le) 2
  · exact pow_le_pow_left₀ (by positivity) (by gcongr; exact hp.2.le) 2

def entryLo (n : ℕ) : ℚ := 4 / 3 * hpLo (ql n) (qh n) + 2 * DLo (ql n) (qh n) - PdHi n
def entryHi (n : ℕ) : ℚ := 4 / 3 * hpHi (ql n) (qh n) + 2 * DHi (ql n) (qh n) - PdLo n

def diagCheck (n : ℕ) (lo hi : ℚ) : Bool :=
  logOk (aK ^ 2 + ql n) && logOk (aK ^ 2 + qh n) &&
    decide (|thLo (3 * n * l2Lo / 2 + 1 / 2)| ≤ 2) && decide (|thLo (3 * n * l3Lo / 2 + 1 / 2)| ≤ 2) &&
    decide (lo ≤ entryLo n) && decide (entryHi n ≤ hi)

theorem diagCheck_sound {M : ℕ} (hM : 3 ≤ M) {n : ℕ} {lo hi : ℚ} (h : diagCheck n lo hi = true) :
    (lo : ℝ) ≤ cvsEntry M (4 / 3) n n ∧ cvsEntry M (4 / 3) n n ≤ hi := by
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

/-- Boxes for `cvsEntry M (4/3) n n`, `n = 0, …, 70` (untrusted, from `tools/gen_diag43.py`). -/
def diagLo : List ℚ := [
  -1015719325478363 / 281474976710656,
  35430148505067 / 281474976710656,
  32794432987184 / 281474976710656,
  552006849944428 / 281474976710656,
  281455165375011 / 281474976710656,
  578518436570132 / 281474976710656,
  356640420525139 / 281474976710656,
  726592240696849 / 281474976710656,
  647151743308436 / 281474976710656,
  865514959757972 / 281474976710656,
  694729406428904 / 281474976710656,
  749573267446974 / 281474976710656,
  747985421841741 / 281474976710656,
  865711801339886 / 281474976710656,
  995215796715976 / 281474976710656,
  909200750336497 / 281474976710656,
  971488528270456 / 281474976710656,
  779224897252484 / 281474976710656,
  1046282107403834 / 281474976710656,
  917380075808858 / 281474976710656,
  1240505050297271 / 281474976710656,
  908930261815451 / 281474976710656,
  1156588936181002 / 281474976710656,
  818747578009028 / 281474976710656,
  1246387611333053 / 281474976710656,
  991610979776633 / 281474976710656,
  1364690276093625 / 281474976710656,
  955255046441948 / 281474976710656,
  1232758485280150 / 281474976710656,
  932717429896231 / 281474976710656,
  1330433602511496 / 281474976710656,
  1129619495858138 / 281474976710656,
  1365192062944456 / 281474976710656,
  1074820775480230 / 281474976710656,
  1211965102604884 / 281474976710656,
  1122372630846870 / 281474976710656,
  1319271039514679 / 281474976710656,
  1313919220894210 / 281474976710656,
  1283087618065111 / 281474976710656,
  1238457913855441 / 281474976710656,
  1146855396476543 / 281474976710656,
  1338246739750532 / 281474976710656,
  1271500923376924 / 281474976710656,
  1486886532658335 / 281474976710656,
  1190454802388670 / 281474976710656,
  1385466180840277 / 281474976710656,
  1109237588837904 / 281474976710656,
  1510958724574780 / 281474976710656,
  1255511749127843 / 281474976710656,
  1585659812698064 / 281474976710656,
  1156830297564798 / 281474976710656,
  1460692287242029 / 281474976710656,
  1154530942729002 / 281474976710656,
  1589616441226473 / 281474976710656,
  1314203356690544 / 281474976710656,
  1578345304942489 / 281474976710656,
  1215478643416324 / 281474976710656,
  1446777539777182 / 281474976710656,
  1293152110543925 / 281474976710656,
  1569066977171665 / 281474976710656,
  1442738147957257 / 281474976710656,
  1483234418225010 / 281474976710656,
  1348276215826098 / 281474976710656,
  1375012831308990 / 281474976710656,
  1484904976059181 / 281474976710656,
  1492189375946288 / 281474976710656,
  1591812458165352 / 281474976710656,
  1361084136862563 / 281474976710656,
  1497492629908190 / 281474976710656,
  1309269706941395 / 281474976710656,
  1659797429510625 / 281474976710656
]

/-- Upper ends. -/
def diagHi : List ℚ := [
  -1015719320692084 / 281474976710656,
  35430153291346 / 281474976710656,
  32794437773463 / 281474976710656,
  552006854730706 / 281474976710656,
  281455170161289 / 281474976710656,
  578518441356411 / 281474976710656,
  356640425311418 / 281474976710656,
  726592245483128 / 281474976710656,
  647151748094715 / 281474976710656,
  865514964544251 / 281474976710656,
  694729411215183 / 281474976710656,
  749573272233253 / 281474976710656,
  747985426628020 / 281474976710656,
  865711806126165 / 281474976710656,
  995215801502255 / 281474976710656,
  909200755122776 / 281474976710656,
  971488533056735 / 281474976710656,
  779224902038762 / 281474976710656,
  1046282112190113 / 281474976710656,
  917380080595137 / 281474976710656,
  1240505055083550 / 281474976710656,
  908930266601730 / 281474976710656,
  1156588940967281 / 281474976710656,
  818747582795307 / 281474976710656,
  1246387616119332 / 281474976710656,
  991610984562912 / 281474976710656,
  1364690280879904 / 281474976710656,
  955255051228227 / 281474976710656,
  1232758490066429 / 281474976710656,
  932717434682510 / 281474976710656,
  1330433607297775 / 281474976710656,
  1129619500644417 / 281474976710656,
  1365192067730735 / 281474976710656,
  1074820780266509 / 281474976710656,
  1211965107391163 / 281474976710656,
  1122372635633149 / 281474976710656,
  1319271044300958 / 281474976710656,
  1313919225680489 / 281474976710656,
  1283087622851390 / 281474976710656,
  1238457918641720 / 281474976710656,
  1146855401262822 / 281474976710656,
  1338246744536811 / 281474976710656,
  1271500928163203 / 281474976710656,
  1486886537444614 / 281474976710656,
  1190454807174949 / 281474976710656,
  1385466185626556 / 281474976710656,
  1109237593624183 / 281474976710656,
  1510958729361058 / 281474976710656,
  1255511753914122 / 281474976710656,
  1585659817484342 / 281474976710656,
  1156830302351077 / 281474976710656,
  1460692292028308 / 281474976710656,
  1154530947515281 / 281474976710656,
  1589616446012752 / 281474976710656,
  1314203361476823 / 281474976710656,
  1578345309728768 / 281474976710656,
  1215478648202603 / 281474976710656,
  1446777544563461 / 281474976710656,
  1293152115330204 / 281474976710656,
  1569066981957944 / 281474976710656,
  1442738152743536 / 281474976710656,
  1483234423011289 / 281474976710656,
  1348276220612376 / 281474976710656,
  1375012836095269 / 281474976710656,
  1484904980845460 / 281474976710656,
  1492189380732567 / 281474976710656,
  1591812462951631 / 281474976710656,
  1361084141648842 / 281474976710656,
  1497492634694469 / 281474976710656,
  1309269711727674 / 281474976710656,
  1659797434296904 / 281474976710656
]

def diagAll : Bool :=
  (List.range 71).all fun n => diagCheck n (diagLo.getD n 0) (diagHi.getD n 0)

set_option maxRecDepth 100000 in
theorem diagAll_true : diagAll = true := by decide +kernel

/-- **The diagonal of the `L = 4/3` low block**: `cvsEntry M (4/3) n n` for `n = 0, …, 70` and
every prime cutoff `M ≥ 3`, each box of width at most `2·10⁻⁸`. -/
theorem diag_mem {M : ℕ} (hM : 3 ≤ M) {n : ℕ} (hn : n ≤ 70) :
    ((diagLo.getD n 0 : ℚ) : ℝ) ≤ cvsEntry M (4 / 3) n n ∧
      cvsEntry M (4 / 3) n n ≤ ((diagHi.getD n 0 : ℚ) : ℝ) := by
  have h := diagAll_true
  simp only [diagAll, List.all_eq_true, List.mem_range] at h
  exact diagCheck_sound hM (h n (by omega))

theorem Dser_neg (r : ℝ) : Dser (-r) = Dser r := by
  simp only [Dser, neg_sq]

/-- The diagonal is even in `n`. -/
theorem cvsEntry_diag_neg {M : ℕ} (hM : 3 ≤ M) (n : ℤ) :
    cvsEntry M (4 / 3) (-n) (-n) = cvsEntry M (4 / 3) n n := by
  rw [cvsEntry_diag_eq hM, cvsEntry_diag_eq hM]
  have e : 2 * Real.pi * ((-n : ℤ) : ℝ) / (4 / 3) = -(2 * Real.pi * (n : ℝ) / (4 / 3)) := by
    push_cast; ring
  rw [e, hplus_neg, Dser_neg]
  have c2 : Real.cos (-(2 * Real.pi * (n : ℝ) / (4 / 3)) * Real.log 2) =
      Real.cos (2 * Real.pi * (n : ℝ) / (4 / 3) * Real.log 2) := by rw [neg_mul, Real.cos_neg]
  have c3 : Real.cos (-(2 * Real.pi * (n : ℝ) / (4 / 3)) * Real.log 3) =
      Real.cos (2 * Real.pi * (n : ℝ) / (4 / 3) * Real.log 3) := by rw [neg_mul, Real.cos_neg]
  rw [c2, c3]

end AEGIS.CvSDiagL43V1

#print axioms AEGIS.CvSDiagL43V1.D_bounds
#print axioms AEGIS.CvSDiagL43V1.cvsEntry_diag_eq
#print axioms AEGIS.CvSDiagL43V1.Pd_bounds
#print axioms AEGIS.CvSDiagL43V1.diagCheck_sound
#print axioms AEGIS.CvSDiagL43V1.diagAll_true
#print axioms AEGIS.CvSDiagL43V1.diag_mem
#print axioms AEGIS.CvSDiagL43V1.cvsEntry_diag_neg
