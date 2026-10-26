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
import CvSTauL12V1

/-!
# Kernel check for the source integrals at `L = 4/3`

The check of `CvSTauL12V1` with the window moved to `L = 4/3`: `e^{−2/3}` from `Real.exp_bound`
(`e23_bounds`), `e^{−c_j L} = (e^{−2/3})^{4j+1}` and `ω_k = 3πk/2`. The rational `π` bounds, the
outward rounding, the arctan partial sums and the term bounds are those of `CvSTauL12V1`.
`tauCheck_sound` turns a passing check into `lo ≤ ∫ h₊ S_k ≤ hi`. No `native_decide`. Not RH.
-/

open Finset

namespace AEGIS.CvSTauL43V1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
  AEGIS.CvSArctanTailV1 AEGIS.CvSTauSourceV1
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds j0 cw cw_cast rdn rup rdn_le le_rup atPartial
  atPartial_cast term_lo term_hi)

/-! ## Rational enclosures of the constants -/

def e23Lo : ℚ := 158894902126248433646108355 / 309485009821345068724781056
def e23Hi : ℚ := 635579608504993734584433421 / 1237940039285380274899124224

theorem e23_bounds : (e23Lo : ℝ) ≤ Real.exp (-2 / 3) ∧ Real.exp (-2 / 3) ≤ e23Hi := by
  have h := Real.exp_bound (x := -2 / 3) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e23Lo, e23Hi] <;> push_cast <;> linarith [h.1, h.2]

theorem exp_width (j : ℕ) :
    Real.exp (-archWidth j * (4 / 3)) = Real.exp (-2 / 3) ^ (4 * j + 1) := by
  rw [← Real.exp_nat_mul]; congr 1; unfold archWidth; push_cast; ring

def Ehi (j : ℕ) : ℚ := e23Hi ^ (4 * min j j0 + 1)

def Elo (j : ℕ) : ℚ := if j < j0 then e23Lo ^ (4 * j + 1) else 0

theorem E_bounds (j : ℕ) :
    (Elo j : ℝ) ≤ Real.exp (-archWidth j * (4 / 3)) ∧
      Real.exp (-archWidth j * (4 / 3)) ≤ Ehi j ∧ (Ehi j : ℝ) ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := e23_bounds
  have hpos : 0 < Real.exp (-2 / 3) := Real.exp_pos _
  have hle1 : Real.exp (-2 / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hlo0 : (0 : ℝ) ≤ e23Lo := by simp only [e23Lo]; norm_num
  have hhi1 : (e23Hi : ℝ) ≤ 1 := by simp only [e23Hi]; norm_num
  rw [exp_width]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Elo]
    split_ifs
    · push_cast; exact pow_le_pow_left₀ hlo0 hlo _
    · push_cast; positivity
  · simp only [Ehi]; push_cast
    calc Real.exp (-2 / 3) ^ (4 * j + 1) ≤ Real.exp (-2 / 3) ^ (4 * min j j0 + 1) :=
          pow_le_pow_of_le_one hpos.le hle1 (by omega)
      _ ≤ (e23Hi : ℝ) ^ (4 * min j j0 + 1) := pow_le_pow_left₀ hpos.le hhi _
  · simp only [Ehi]; push_cast
    exact pow_le_one₀ (by simp only [e23Hi]; norm_num) hhi1

theorem Ehi_mono {j : ℕ} (hj : j0 ≤ j) :
    Real.exp (-archWidth j * (4 / 3)) ≤ Ehi j0 := by
  have h := (E_bounds j).2.1
  have : Ehi j = Ehi j0 := by simp only [Ehi]; rw [Nat.min_eq_right hj, Nat.min_self]
  rwa [this] at h

/-! ## The head sums -/

def headLo (ωl ωh : ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => rdn (headLo ωl ωh j + 2 * ωl * (1 - Ehi j) / (cw j ^ 2 + ωh ^ 2))

def headHi (ωl ωh : ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => rup (headHi ωl ωh j + 2 * ωh * (1 - Elo j) / (cw j ^ 2 + ωl ^ 2))

theorem head_bounds {ω : ℝ} {ωl ωh : ℚ} (h0 : (0 : ℝ) ≤ ωl) (hl : (ωl : ℝ) ≤ ω)
    (hh : ω ≤ ωh) (J : ℕ) :
    (headLo ωl ωh J : ℝ) ≤ ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (4 / 3))) /
        (archWidth j ^ 2 + ω ^ 2) ∧
      ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (4 / 3))) /
        (archWidth j ^ 2 + ω ^ 2) ≤ (headHi ωl ωh J : ℝ) := by
  induction J with
  | zero => simp [headLo, headHi]
  | succ J ih =>
    obtain ⟨elo, ehi, eh1⟩ := E_bounds J
    have hc := archWidth_pos J
    have he1 : Real.exp (-archWidth J * (4 / 3)) ≤ 1 := ehi.trans eh1
    rw [sum_range_succ]
    simp only [headLo, headHi]
    constructor
    · refine (rdn_le _).trans ?_
      push_cast
      rw [cw_cast]
      exact add_le_add ih.1 (term_lo hc h0 hl hh ehi eh1)
    · refine le_trans ?_ (le_rup _)
      push_cast
      rw [cw_cast]
      exact add_le_add ih.2 (term_hi hc h0 hl hh elo he1)

/-! ## The check -/

def omLo (k : ℕ) : ℚ := 3 * piLo * k / 2
def omHi (k : ℕ) : ℚ := 3 * piHi * k / 2

def boxLo (k J K : ℕ) : ℚ :=
  headLo (omLo k) (omHi k) J + atPartial (omLo k / (cw J - 1)) (2 * K) -
    omHi k / 3 * (1 / (cw J - 1) ^ 3) - Ehi j0 * atPartial (omHi k / (cw J - 1)) (2 * K + 1)

def boxHi (k J K : ℕ) : ℚ :=
  headHi (omLo k) (omHi k) J + atPartial (omHi k / (cw J - 1)) (2 * K + 1)

/-- The kernel check for one frequency `k`: conditions of `source_bracket` and the output box. -/
def tauCheck (k J K : ℕ) (lo hi : ℚ) : Bool :=
  decide (1 ≤ omLo k) && decide (j0 ≤ J) && decide (2 < cw J) &&
    decide (omHi k ^ 2 / 3 + 3 ≤ cw J ^ 2) && decide (omHi k / (cw J - 1) < 1) &&
    decide (0 ≤ boxLo k J K) && decide (0 ≤ boxHi k J K) &&
    decide (lo ≤ piLo * boxLo k J K) && decide (piHi * boxHi k J K ≤ hi)

/-- **Soundness.** A passing check encloses `∫ h₊ S_k` at `L = 4/3`. -/
theorem tauCheck_sound {k J K : ℕ} {lo hi : ℚ} (h : tauCheck k J K lo hi = true) :
    (lo : ℝ) ≤ ∫ r, hplus r * sourceS (4 / 3) r (k : ℤ) ∧
      ∫ r, hplus r * sourceS (4 / 3) r (k : ℤ) ≤ hi := by
  simp only [tauCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, hj0⟩, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  obtain ⟨hpl, hph⟩ := pi_bounds
  set ω : ℝ := 2 * Real.pi * ((k : ℤ) : ℝ) / (4 / 3) with hω
  have hωe : ω = 3 * Real.pi * k / 2 := by rw [hω]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hωl : ((omLo k : ℚ) : ℝ) ≤ ω := by
    rw [hωe]; simp only [omLo]; push_cast
    have := mul_le_mul_of_nonneg_right hpl.le hk0
    nlinarith
  have hωh : ω ≤ ((omHi k : ℚ) : ℝ) := by
    rw [hωe]; simp only [omHi]; push_cast
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
  obtain ⟨hbl, hbh⟩ := source_bracket (L := 4 / 3) (by norm_num) (k : ℤ) J hω1 h2' hJ
  rw [← hω] at hbl hbh
  set d : ℝ := archWidth J - 1 with hd
  have hd0 : 0 < d := by linarith
  have hdq : ((cw J : ℚ) : ℝ) - 1 = d := by rw [hcJ]
  set I := ∫ r, hplus r * sourceS (4 / 3) r (k : ℤ) with hI
  set H := ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (4 / 3))) /
    (archWidth j ^ 2 + ω ^ 2) with hH
  set A := Real.arctan (ω / d) with hA
  have h0l : (0 : ℝ) ≤ omLo k := by linarith
  obtain ⟨hHl, hHh⟩ := head_bounds h0l hωl hωh J
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
  have hE0 : 0 ≤ Real.exp (-archWidth J * (4 / 3)) := (Real.exp_pos _).le
  have hcube : ω / 3 * (1 / d ^ 3) ≤ ((omHi k : ℚ) : ℝ) / 3 * (1 / d ^ 3) := by
    gcongr
  have hEA : Real.exp (-archWidth J * (4 / 3)) * A ≤
      ((Ehi j0 : ℚ) : ℝ) * ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) :=
    mul_le_mul hE hAh hA0 (hE0.trans hE)
  have hLO : ((boxLo k J K : ℚ) : ℝ) ≤ I / Real.pi := by
    have : ((boxLo k J K : ℚ) : ℝ) = (headLo (omLo k) (omHi k) J : ℝ) +
        ((atPartial (omLo k / (cw J - 1)) (2 * K) : ℚ) : ℝ) -
        ((omHi k : ℚ) : ℝ) / 3 * (1 / d ^ 3) -
        ((Ehi j0 : ℚ) : ℝ) * ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) := by
      simp only [boxLo]; push_cast; rw [hdq]
    rw [this]; linarith
  have hHI : I / Real.pi ≤ ((boxHi k J K : ℚ) : ℝ) := by
    have : ((boxHi k J K : ℚ) : ℝ) = (headHi (omLo k) (omHi k) J : ℝ) +
        ((atPartial (omHi k / (cw J - 1)) (2 * K + 1) : ℚ) : ℝ) := by
      rw [boxHi, Rat.cast_add]
    rw [this]; linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h6' : (0 : ℝ) ≤ boxLo k J K := by exact_mod_cast h6
  have h7' : (0 : ℝ) ≤ boxHi k J K := by exact_mod_cast h7
  have h8' : (lo : ℝ) ≤ piLo * boxLo k J K := by exact_mod_cast h8
  have h9' : (piHi : ℝ) * boxHi k J K ≤ hi := by exact_mod_cast h9
  rw [le_div_iff₀ hpi0] at hLO
  rw [div_le_iff₀ hpi0] at hHI
  constructor
  · calc (lo : ℝ) ≤ piLo * boxLo k J K := h8'
      _ ≤ Real.pi * boxLo k J K := mul_le_mul_of_nonneg_right hpl.le h6'
      _ ≤ I := by linarith
  · calc I ≤ boxHi k J K * Real.pi := hHI
      _ ≤ boxHi k J K * piHi := mul_le_mul_of_nonneg_left hph.le h7'
      _ ≤ hi := by linarith

end AEGIS.CvSTauL43V1

#print axioms AEGIS.CvSTauL43V1.e23_bounds
#print axioms AEGIS.CvSTauL43V1.head_bounds
#print axioms AEGIS.CvSTauL43V1.tauCheck_sound
