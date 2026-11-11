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
import CvSTauL32V1
import CvSNodeL32V1
import CvSTraceM4SlackV1

/-!
# `τ_k` at `L = 3/2` for every prime cutoff `M ≥ 4`: the check with integer head sums

`CvSTauL32V1.tauCheck` sums the head `Σ_{j<J} 2ω(1 − e^{−c_j L})/(c_j² + ω²)` in rationals. At
`L = 3/2` the boxes must be about 200 times tighter than at `11/8`, so `J` reaches about `9400`, and
the rational head costs about `3.5 ms` per term in the kernel. Here the same head is summed in
natural numbers: with `ω ∈ [a/D, b/D]` (`a = 4⌊π⌋₂₀k`, `D = 3·10²⁰`), each term is
`⌊8 a N_j D / ((4j+1)² D² + 4 b²)⌋ / 2⁶⁴` with `N_j/2⁶⁴ ≤ 1 − e^{−c_j L}` (`hLo`), and
`(⌊8 b N'_j D / ((4j+1)² D² + 4 a²)⌋ + 1) / 2⁶⁴` with `1 − e^{−c_j L} ≤ N'_j/2⁶⁴` (`hHi`); only
`Nat` arithmetic, about 15 times faster. `h_bounds` is the induction, `srcCheck_sound` the
`CvSTauL32V1.tauCheck_sound` argument with this head (the source bracket, the arctan tail and the
`e^{−c_J L}` term are unchanged).

The prime part: at `L = 3/2` the prime powers `2, 3, 4` contribute (`primeSum_eq`, from
`CvSNodeL32V1`), with `ppw 3 = log 2` (`CvSTraceM4SlackV1.ppw_three`). `tauF_sound` turns a passing
check into `lo ≤ τ_k ≤ hi` for every `M ≥ 4`. Not RH.
-/

open Finset

namespace AEGIS.CvSTauFastL32V1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
  AEGIS.CvSArctanTailV1 AEGIS.CvSTauSourceV1
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds j0 cw cw_cast atPartial atPartial_cast term_lo term_hi)
open AEGIS.CvSTauL32V1 (Elo Ehi E_bounds Ehi_mono omLo omHi)

/-! ### `1 − e^{−c_j L}` in units of `2⁻⁶⁴` -/

/-- `⌊2⁶⁴ (1 − Ehi j)⌋`, `j ≤ 12` (constant from `j0 = 12` on). -/
def NEloT : List ℕ := [9733119166315628212, 18012918234713208232, 18425145157003694732,
  18445668726966845320, 18446690535347753337, 18446741408191472461, 18446743941001220773,
  18446744067102392875, 18446744073380600552, 18446744073693174106, 18446744073708736227,
  18446744073709511020, 18446744073709549594]

/-- `⌈2⁶⁴ (1 − Elo j)⌉`, `j ≤ 12` (`Elo j = 0` from `j0 = 12` on). -/
def NEhiT : List ℕ := [9733119166315628213, 18012918234713208233, 18425145157003694733,
  18445668726966845321, 18446690535347753338, 18446741408191472462, 18446743941001220774,
  18446744067102392876, 18446744073380600553, 18446744073693174107, 18446744073708736228,
  18446744073709511021, 18446744073709551616]

def NElo (j : ℕ) : ℕ := NEloT.getD (min j 12) 0
def NEhi (j : ℕ) : ℕ := NEhiT.getD (min j 12) 0

theorem NE_check : ((List.range 13).all fun i =>
    decide (((NEloT.getD i 0 : ℕ) : ℚ) ≤ 2 ^ 64 * (1 - Ehi i)) &&
      decide (2 ^ 64 * (1 - Elo i) ≤ ((NEhiT.getD i 0 : ℕ) : ℚ))) = true := by
  decide +kernel

theorem Ehi_min (j : ℕ) : Ehi (min j 12) = Ehi j := by
  have h : min (min j 12) j0 = min j j0 := by simp only [j0]; omega
  simp only [AEGIS.CvSTauL32V1.Ehi, h]

theorem Elo_min (j : ℕ) : Elo (min j 12) = Elo j := by
  by_cases h : j < 12
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right (by omega : 12 ≤ j)]
    simp only [AEGIS.CvSTauL32V1.Elo, j0]
    simp [h]

theorem NE_bounds (j : ℕ) :
    ((NElo j : ℕ) : ℝ) / 2 ^ 64 ≤ 1 - Real.exp (-archWidth j * (3 / 2)) ∧
      1 - Real.exp (-archWidth j * (3 / 2)) ≤ ((NEhi j : ℕ) : ℝ) / 2 ^ 64 := by
  have h := NE_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h (min j 12) (by omega)
  rw [Ehi_min] at h1
  rw [Elo_min] at h2
  obtain ⟨elo, ehi, _⟩ := E_bounds j
  have h1' : ((NElo j : ℕ) : ℝ) ≤ 2 ^ 64 * (1 - ((Ehi j : ℚ) : ℝ)) := by
    simp only [NElo]; exact_mod_cast h1
  have h2' : 2 ^ 64 * (1 - ((Elo j : ℚ) : ℝ)) ≤ ((NEhi j : ℕ) : ℝ) := by
    simp only [NEhi]; exact_mod_cast h2
  constructor
  · rw [div_le_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith

/-! ### The head in natural numbers -/

/-- `2⁶⁴ ×` a lower bound for the head, for `ω ∈ [a/D, b/D]`. -/
def hLo (a b D : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => hLo a b D j + 8 * a * NElo j * D / ((4 * j + 1) ^ 2 * D ^ 2 + 4 * b ^ 2)

/-- `2⁶⁴ ×` an upper bound for the head, for `ω ∈ [a/D, b/D]`. -/
def hHi (a b D : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => hHi a b D j + (8 * b * NEhi j * D / ((4 * j + 1) ^ 2 * D ^ 2 + 4 * a ^ 2) + 1)

theorem term_eq (j a b D n : ℕ) (hD : 0 < D) :
    2 * ((a : ℝ) / D) * (1 - (1 - (n : ℝ) / 2 ^ 64)) / (archWidth j ^ 2 + ((b : ℝ) / D) ^ 2) =
      ((8 * a * n * D : ℕ) : ℝ) / (((4 * j + 1) ^ 2 * D ^ 2 + 4 * b ^ 2 : ℕ) : ℝ) / 2 ^ 64 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hq : (0 : ℝ) < (4 * j + 1) ^ 2 * D ^ 2 + 4 * b ^ 2 := by positivity
  have hq' : (0 : ℝ) < (2 * j + 1 / 2) ^ 2 + ((b : ℝ) / D) ^ 2 := by positivity
  simp only [archWidth]
  push_cast
  rw [div_div, div_eq_div_iff hq'.ne' (by positivity)]
  field_simp
  ring

theorem div_le_succ (m n : ℕ) (hn : 0 < n) : (m : ℝ) / n ≤ ((m / n : ℕ) : ℝ) + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (m : ℝ) = n * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod m n).symm
  have h3 : ((m % n : ℕ) : ℝ) < n := by exact_mod_cast Nat.mod_lt m hn
  rw [div_le_iff₀ hn']
  linarith

theorem h_bounds {ω : ℝ} {a b D : ℕ} (hD : 0 < D) (hl : (a : ℝ) / D ≤ ω) (hh : ω ≤ (b : ℝ) / D)
    (J : ℕ) :
    (hLo a b D J : ℝ) / 2 ^ 64 ≤ ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (3 / 2))) /
        (archWidth j ^ 2 + ω ^ 2) ∧
      ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (3 / 2))) /
        (archWidth j ^ 2 + ω ^ 2) ≤ (hHi a b D J : ℝ) / 2 ^ 64 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ha : (0 : ℝ) ≤ (a : ℝ) / D := by positivity
  induction J with
  | zero => simp [hLo, hHi]
  | succ J ih =>
    obtain ⟨n1, n2⟩ := NE_bounds J
    obtain ⟨_, ehi, eh1⟩ := E_bounds J
    have hc := archWidth_pos J
    have hn0 : (0 : ℝ) ≤ ((NElo J : ℕ) : ℝ) / 2 ^ 64 := by positivity
    have hQ : 0 < (4 * J + 1) ^ 2 * D ^ 2 + 4 * b ^ 2 :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (by positivity) (pow_pos hD 2)) (Nat.le_add_right _ _)
    have hQ' : 0 < (4 * J + 1) ^ 2 * D ^ 2 + 4 * a ^ 2 :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (by positivity) (pow_pos hD 2)) (Nat.le_add_right _ _)
    have tl := term_lo (e := Real.exp (-archWidth J * (3 / 2)))
      (eh := 1 - ((NElo J : ℕ) : ℝ) / 2 ^ 64) hc ha hl hh (by linarith) (by linarith)
    rw [term_eq J a b D (NElo J) hD] at tl
    have th := term_hi (e := Real.exp (-archWidth J * (3 / 2)))
      (el := 1 - ((NEhi J : ℕ) : ℝ) / 2 ^ 64) hc ha hl hh (by linarith)
      (ehi.trans (by exact_mod_cast eh1))
    rw [term_eq J b a D (NEhi J) hD] at th
    have ql := Nat.cast_div_le (α := ℝ) (m := 8 * a * NElo J * D)
      (n := (4 * J + 1) ^ 2 * D ^ 2 + 4 * b ^ 2)
    have qh := div_le_succ (8 * b * NEhi J * D) ((4 * J + 1) ^ 2 * D ^ 2 + 4 * a ^ 2) hQ'
    have ql' : (((8 * a * NElo J * D / ((4 * J + 1) ^ 2 * D ^ 2 + 4 * b ^ 2) : ℕ) : ℝ)) / 2 ^ 64 ≤
        ((8 * a * NElo J * D : ℕ) : ℝ) / (((4 * J + 1) ^ 2 * D ^ 2 + 4 * b ^ 2 : ℕ) : ℝ) / 2 ^ 64 := by
      gcongr
    have qh' : ((8 * b * NEhi J * D : ℕ) : ℝ) / (((4 * J + 1) ^ 2 * D ^ 2 + 4 * a ^ 2 : ℕ) : ℝ) /
        2 ^ 64 ≤ (((8 * b * NEhi J * D / ((4 * J + 1) ^ 2 * D ^ 2 + 4 * a ^ 2) : ℕ) : ℝ) + 1) /
        2 ^ 64 := by
      gcongr
    rw [sum_range_succ]
    simp only [hLo, hHi]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    constructor
    · rw [add_div]; linarith [ih.1]
    · rw [add_div, add_div]; rw [add_div] at qh'; linarith [ih.2]

/-! ### The source integral -/

def pLoN : ℕ := 314159265358979323846
def pHiN : ℕ := 314159265358979323847
def Dk : ℕ := 300000000000000000000

def aN (k : ℕ) : ℕ := 4 * pLoN * k
def bN (k : ℕ) : ℕ := 4 * pHiN * k

theorem om_cast (k : ℕ) : ((aN k : ℕ) : ℝ) / (Dk : ℕ) = ((omLo k : ℚ) : ℝ) ∧
    ((bN k : ℕ) : ℝ) / (Dk : ℕ) = ((omHi k : ℚ) : ℝ) := by
  constructor <;>
    simp only [aN, bN, Dk, pLoN, pHiN, AEGIS.CvSTauL32V1.omLo, AEGIS.CvSTauL32V1.omHi, piLo,
      piHi] <;> push_cast <;> ring

def bxLo (k J K : ℕ) : ℚ :=
  (hLo (aN k) (bN k) Dk J : ℚ) / 2 ^ 64 + atPartial (omLo k / (cw J - 1)) (2 * K) -
    omHi k / 3 * (1 / (cw J - 1) ^ 3) - Ehi j0 * atPartial (omHi k / (cw J - 1)) (2 * K + 1)

def bxHi (k J K : ℕ) : ℚ :=
  (hHi (aN k) (bN k) Dk J : ℚ) / 2 ^ 64 + atPartial (omHi k / (cw J - 1)) (2 * K + 1)

/-- The conditions of `source_bracket` and of the arctan tail. -/
def srcCheck (k J K : ℕ) : Bool :=
  decide (1 ≤ omLo k) && decide (j0 ≤ J) && decide (2 < cw J) &&
    decide (omHi k ^ 2 / 3 + 3 ≤ cw J ^ 2) && decide (omHi k / (cw J - 1) < 1) &&
    decide (0 ≤ bxLo k J K) && decide (0 ≤ bxHi k J K)

/-- **Soundness of the source part**: `π_lo · bxLo ≤ ∫ h₊ S_k ≤ π_hi · bxHi` at `L = 3/2`. -/
theorem srcCheck_sound {k J K : ℕ} (h : srcCheck k J K = true) :
    ((piLo : ℝ) * bxLo k J K) ≤ ∫ r, hplus r * sourceS (3 / 2) r (k : ℤ) ∧
      ∫ r, hplus r * sourceS (3 / 2) r (k : ℤ) ≤ (piHi : ℝ) * bxHi k J K := by
  simp only [srcCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hj0⟩, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩ := h
  obtain ⟨hpl, hph⟩ := pi_bounds
  set ω : ℝ := 2 * Real.pi * ((k : ℤ) : ℝ) / (3 / 2) with hω
  have hωe : ω = 4 * Real.pi * k / 3 := by rw [hω]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hωl : ((omLo k : ℚ) : ℝ) ≤ ω := by
    rw [hωe]; simp only [AEGIS.CvSTauL32V1.omLo]; push_cast
    have := mul_le_mul_of_nonneg_right hpl.le hk0
    nlinarith
  have hωh : ω ≤ ((omHi k : ℚ) : ℝ) := by
    rw [hωe]; simp only [AEGIS.CvSTauL32V1.omHi]; push_cast
    have := mul_le_mul_of_nonneg_right hph.le hk0
    nlinarith
  have h1' : (1 : ℝ) ≤ omLo k := by exact_mod_cast h1
  have hω1 : 1 ≤ ω := h1'.trans hωl
  have hcJ : (cw J : ℝ) = archWidth J := cw_cast J
  have h2' : (2 : ℝ) < archWidth J := by rw [← hcJ]; exact_mod_cast h2
  have h3' : ((omHi k : ℚ) : ℝ) ^ 2 / 3 + 3 ≤ archWidth J ^ 2 := by
    rw [← hcJ]; exact_mod_cast h3
  have hJ : ω ^ 2 / 3 + 3 ≤ archWidth J ^ 2 := by
    have : ω ^ 2 ≤ ((omHi k : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hωh 2
    linarith
  obtain ⟨hbl, hbh⟩ := source_bracket (L := 3 / 2) (by norm_num) (k : ℤ) J hω1 h2' hJ
  rw [← hω] at hbl hbh
  set d : ℝ := archWidth J - 1 with hd
  have hd0 : 0 < d := by linarith
  have hdq : ((cw J : ℚ) : ℝ) - 1 = d := by rw [hcJ]
  set I := ∫ r, hplus r * sourceS (3 / 2) r (k : ℤ) with hI
  set H := ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (3 / 2))) /
    (archWidth j ^ 2 + ω ^ 2) with hH
  set A := Real.arctan (ω / d) with hA
  have h0l : (0 : ℝ) ≤ omLo k := by linarith
  have hDk : 0 < Dk := by norm_num [Dk]
  obtain ⟨oc1, oc2⟩ := om_cast k
  obtain ⟨hHl, hHh⟩ := h_bounds hDk (oc1.symm ▸ hωl) (oc2.symm ▸ hωh) J (ω := ω)
  -- the arctan arguments
  have hxh : ((omHi k / (cw J - 1) : ℚ) : ℝ) < 1 := by exact_mod_cast h5
  have hxh' : ((omHi k : ℚ) : ℝ) / d < 1 := by push_cast at hxh; rwa [hdq] at hxh
  have hxl0 : 0 ≤ ((omLo k : ℚ) : ℝ) / d := div_nonneg h0l hd0.le
  have hxl1 : ((omLo k : ℚ) : ℝ) / d < 1 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (hωl.trans hωh) hd0.le) hxh'
  have hxh0 : 0 ≤ ((omHi k : ℚ) : ℝ) / d := div_nonneg (by linarith) hd0.le
  have hAl : ((atPartial (omLo k / (cw J - 1)) (2 * K) : ℚ) : ℝ) ≤ A := by
    rw [atPartial_cast]; push_cast; rw [hdq]
    exact (partial_le_arctan hxl0 hxl1 K).trans
      (Real.arctan_mono (div_le_div_of_nonneg_right hωl hd0.le))
  have hAh : A ≤ ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) := by
    rw [atPartial_cast]; push_cast; rw [hdq]
    exact (Real.arctan_mono (div_le_div_of_nonneg_right hωh hd0.le)).trans
      (arctan_le_partial hxh0 hxh' K)
  have hA0 : 0 ≤ A := Real.arctan_nonneg.mpr (div_nonneg (by linarith) hd0.le)
  have hE := Ehi_mono hj0 (j := J)
  have hE0 : 0 ≤ Real.exp (-archWidth J * (3 / 2)) := (Real.exp_pos _).le
  have hcube : ω / 3 * (1 / d ^ 3) ≤ ((omHi k : ℚ) : ℝ) / 3 * (1 / d ^ 3) := by
    gcongr
  have hEA : Real.exp (-archWidth J * (3 / 2)) * A ≤
      ((Ehi j0 : ℚ) : ℝ) * ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) :=
    mul_le_mul hE hAh hA0 (hE0.trans hE)
  have hLO : ((bxLo k J K : ℚ) : ℝ) ≤ I / Real.pi := by
    have : ((bxLo k J K : ℚ) : ℝ) = (hLo (aN k) (bN k) Dk J : ℝ) / 2 ^ 64 +
        ((atPartial (omLo k / (cw J - 1)) (2 * K) : ℚ) : ℝ) -
        ((omHi k : ℚ) : ℝ) / 3 * (1 / d ^ 3) -
        ((Ehi j0 : ℚ) : ℝ) * ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) := by
      simp only [bxLo]; push_cast; rw [hdq]
    rw [this]; linarith
  have hHI : I / Real.pi ≤ ((bxHi k J K : ℚ) : ℝ) := by
    have : ((bxHi k J K : ℚ) : ℝ) = (hHi (aN k) (bN k) Dk J : ℝ) / 2 ^ 64 +
        ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) := by
      simp only [bxHi]; push_cast; ring
    rw [this]; linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h6' : (0 : ℝ) ≤ bxLo k J K := by exact_mod_cast h6
  have h7' : (0 : ℝ) ≤ bxHi k J K := by exact_mod_cast h7
  rw [le_div_iff₀ hpi0] at hLO
  rw [div_le_iff₀ hpi0] at hHI
  constructor
  · calc (piLo : ℝ) * bxLo k J K ≤ Real.pi * bxLo k J K := mul_le_mul_of_nonneg_right hpl.le h6'
      _ ≤ I := by linarith
  · calc I ≤ bxHi k J K * Real.pi := hHI
      _ ≤ bxHi k J K * piHi := mul_le_mul_of_nonneg_left hph.le h7'
      _ = (piHi : ℝ) * bxHi k J K := by ring

/-! ### The prime part at `L = 3/2`: prime powers `2, 3, 4` -/

open AEGIS.CvSRowTailV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds s2Lo s3Lo thLo sinPiLo
  sinPiHi sinPi_bounds mul_lo mul_hi piLo_nonneg w2Lo w2Hi w3Lo w3Hi w2_bounds w3_bounds)
open AEGIS.CvSNodeL32V1 (node_zero node_one node_two node_three node_big)
open AEGIS.CvSTraceM4SlackV1 (ppw_three)

/-- **At `L = 3/2` the prime powers `2, 3, 4` contribute to the prime sum** (for any `M ≥ 4`). -/
theorem primeSum_eq {M : ℕ} (hM : 4 ≤ M) (k : ℤ) :
    ∑ j ∈ range M, ppw j * Real.sin (2 * Real.pi * k * node (3 / 2) j / (3 / 2)) =
      ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
        ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3)) := by
  have hz : ∀ j ∈ range M, j ∉ range 4 →
      ppw j * Real.sin (2 * Real.pi * k * node (3 / 2) j / (3 / 2)) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [node_big hj, show 2 * Real.pi * k * (3 / 2) / (3 / 2) = ((2 * k : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.sin_int_mul_pi, mul_zero]
  rw [← sum_subset (range_mono hM) hz]
  simp only [sum_range_succ, sum_range_zero, node_zero, node_one, node_two, node_three]
  rw [show 2 * Real.pi * k * Real.log 2 / (3 / 2) = Real.pi * (4 * k * Real.log 2 / 3) by ring,
    show 2 * Real.pi * k * Real.log 3 / (3 / 2) = Real.pi * (4 * k * Real.log 3 / 3) by ring,
    show 2 * Real.pi * k * (2 * Real.log 2) / (3 / 2) = Real.pi * (8 * k * Real.log 2 / 3) by ring]
  simp

def s2l (k : ℕ) : ℚ := sinPiLo (4 * k * l2Lo / 3) (4 * k * l2Hi / 3)
def s2h (k : ℕ) : ℚ := sinPiHi (4 * k * l2Lo / 3) (4 * k * l2Hi / 3)
def s3l (k : ℕ) : ℚ := sinPiLo (4 * k * l3Lo / 3) (4 * k * l3Hi / 3)
def s3h (k : ℕ) : ℚ := sinPiHi (4 * k * l3Lo / 3) (4 * k * l3Hi / 3)
def s4l (k : ℕ) : ℚ := sinPiLo (8 * k * l2Lo / 3) (8 * k * l2Hi / 3)
def s4h (k : ℕ) : ℚ := sinPiHi (8 * k * l2Lo / 3) (8 * k * l2Hi / 3)

def sumLo (k : ℕ) : ℚ := min (w2Lo * s2l k) (w2Hi * s2l k) + min (w3Lo * s3l k) (w3Hi * s3l k) +
  min (l2Lo * s4l k) (l2Hi * s4l k)
def sumHi (k : ℕ) : ℚ := max (w2Lo * s2h k) (w2Hi * s2h k) + max (w3Lo * s3h k) (w3Hi * s3h k) +
  max (l2Lo * s4h k) (l2Hi * s4h k)

def primeLo (k : ℕ) : ℚ := min (piLo * sumLo k) (piHi * sumLo k)
def primeHi (k : ℕ) : ℚ := max (piLo * sumHi k) (piHi * sumHi k)

theorem prime_bounds (k : ℕ) (h2 : |thLo (4 * k * l2Lo / 3)| ≤ 2)
    (h3 : |thLo (4 * k * l3Lo / 3)| ≤ 2) (h4 : |thLo (8 * k * l2Lo / 3)| ≤ 2) :
    (primeLo k : ℝ) ≤ Real.pi * (ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
        ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3))) ∧
      Real.pi * (ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
        ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3))) ≤ primeHi k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have l2 := log2_bounds
  have l3 := log3_bounds
  have hs2 : (s2l k : ℝ) ≤ Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) ∧
      Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) ≤ s2h k :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have hs3 : (s3l k : ℝ) ≤ Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) ∧
      Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) ≤ s3h k :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  have hs4 : (s4l k : ℝ) ≤ Real.sin (Real.pi * (8 * k * Real.log 2 / 3)) ∧
      Real.sin (Real.pi * (8 * k * Real.log 2 / 3)) ≤ s4h k :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h4
  have hw2 := w2_bounds
  have hw3 := w3_bounds
  have hw4 : (l2Lo : ℝ) ≤ ppw 3 ∧ ppw 3 ≤ l2Hi := by rw [ppw_three]; exact l2
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have z4 : (0 : ℝ) ≤ l2Lo := by norm_num [l2Lo]
  have hπ := pi_bounds
  have hlo : (sumLo k : ℝ) ≤ ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
      ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
      ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3)) := by
    simp only [sumLo]
    push_cast
    exact add_le_add (add_le_add (mul_lo z2 hw2.1 hw2.2 hs2.1) (mul_lo z3 hw3.1 hw3.2 hs3.1))
      (mul_lo z4 hw4.1 hw4.2 hs4.1)
  have hhi : ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
      ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
      ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3)) ≤ sumHi k := by
    simp only [sumHi]
    push_cast
    exact add_le_add (add_le_add (mul_hi z2 hw2.1 hw2.2 hs2.2) (mul_hi z3 hw3.1 hw3.2 hs3.2))
      (mul_hi z4 hw4.1 hw4.2 hs4.2)
  constructor
  · simp only [primeLo]
    push_cast
    exact mul_lo piLo_nonneg hπ.1.le hπ.2.le hlo
  · simp only [primeHi]
    push_cast
    exact mul_hi piLo_nonneg hπ.1.le hπ.2.le hhi

/-! ### `τ_k` at `L = 3/2` -/

theorem tau_eq {M : ℕ} (hM : 4 ≤ M) (k : ℤ) :
    tau M (3 / 2) k = (∫ r, hplus r * sourceS (3 / 2) r k) +
      Real.pi * (ppw 1 * Real.sin (Real.pi * (4 * k * Real.log 2 / 3)) +
        ppw 2 * Real.sin (Real.pi * (4 * k * Real.log 3 / 3)) +
        ppw 3 * Real.sin (Real.pi * (8 * k * Real.log 2 / 3))) := by
  rw [tau, primeSum_eq hM]

/-- **The full check for one `k`**: the source box with `J` head terms and `2K` arctan terms, plus
the prime part, inside `[lo, hi]`. -/
def tauF (k J K : ℕ) (lo hi : ℚ) : Bool :=
  srcCheck k J K && decide (|thLo (4 * k * l2Lo / 3)| ≤ 2) &&
    decide (|thLo (4 * k * l3Lo / 3)| ≤ 2) && decide (|thLo (8 * k * l2Lo / 3)| ≤ 2) &&
    decide (lo ≤ piLo * bxLo k J K + primeLo k) && decide (piHi * bxHi k J K + primeHi k ≤ hi)

/-- **Soundness**: a passing check encloses `τ_k` at `L = 3/2` for every prime cutoff `M ≥ 4`. -/
theorem tauF_sound {M : ℕ} (hM : 4 ≤ M) {k J K : ℕ} {lo hi : ℚ} (h : tauF k J K lo hi = true) :
    (lo : ℝ) ≤ tau M (3 / 2) k ∧ tau M (3 / 2) k ≤ hi := by
  simp only [tauF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, h2⟩, h3⟩, h4⟩, hl⟩, hh⟩ := h
  have S := srcCheck_sound hs
  have P := prime_bounds k h2 h3 h4
  have hl' : (lo : ℝ) ≤ (piLo : ℝ) * bxLo k J K + (primeLo k : ℝ) := by exact_mod_cast hl
  have hh' : (piHi : ℝ) * bxHi k J K + (primeHi k : ℝ) ≤ hi := by exact_mod_cast hh
  rw [tau_eq hM]
  push_cast at S P ⊢
  constructor <;> linarith [S.1, S.2, P.1, P.2]

end AEGIS.CvSTauFastL32V1

#print axioms AEGIS.CvSTauFastL32V1.NE_bounds
#print axioms AEGIS.CvSTauFastL32V1.h_bounds
#print axioms AEGIS.CvSTauFastL32V1.srcCheck_sound
#print axioms AEGIS.CvSTauFastL32V1.primeSum_eq
#print axioms AEGIS.CvSTauFastL32V1.prime_bounds
#print axioms AEGIS.CvSTauFastL32V1.tauF_sound
