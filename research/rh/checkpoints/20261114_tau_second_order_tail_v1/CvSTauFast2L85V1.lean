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
import CvSTauFastL85V1
import CvSTauSource2V1

/-!
# `τ_k` at `L = 8/5` with the second-order tail

`CvSTauFastL85V1.tauF` with `CvSTauSource2V1.source_bracket2` in place of the first-order tail.
The head is the same integer sum (`hLo`, `hHi`); the tail is `phi2 ω d` with `d = c_J − 1`, its
arctan taken on either side of `1` (`CvSTauSource2V1.atLo`, `atHi`),
plus `ε = 5 arctan(ω/d)/(c_J² + ω²)²`. There is no condition between `c_J` and `ω`, so `J` stays
fixed for large `k`. `tauF2_sound` encloses `τ_k` for every prime cutoff `M ≥ 4`. Not RH.
-/

open Finset

namespace AEGIS.CvSTauFast2L85V1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
  AEGIS.CvSArctanTailV1 AEGIS.CvSTauSourceV1 AEGIS.CvSArctanTail2V1 AEGIS.CvSTauSource2V1
open AEGIS.CvSRowTailV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds j0 cw cw_cast)
open AEGIS.CvSTauL85V1 (Ehi Ehi_mono omLo omHi)
open AEGIS.CvSTauFastL85V1 (hLo hHi h_bounds aN bN Dk om_cast primeLo primeHi prime_bounds
  tau_eq)
open AEGIS.CvSTauPrimeL12V1 (l2Lo l3Lo thLo)

/-! ### The source box -/

def dq (J : ℕ) : ℚ := cw J - 1

/-- Lower bound of `phi2 ω d`. -/
def p2Lo (k J K : ℕ) : ℚ :=
  atLo (omLo k / dq J) K - dq J * omHi k / (3 * (dq J ^ 2 + omLo k ^ 2) ^ 2)

/-- Upper bound of `phi2 ω d`. -/
def p2Hi (k J K : ℕ) : ℚ :=
  atHi (omHi k / dq J) K - dq J * omLo k / (3 * (dq J ^ 2 + omHi k ^ 2) ^ 2)

/-- Upper bound of `ε = 5 arctan(ω/d)/(c_J² + ω²)²`. -/
def epsHi (k J K : ℕ) : ℚ := 5 * atHi (omHi k / dq J) K / (cw J ^ 2 + omLo k ^ 2) ^ 2

def bx2Lo (k J K : ℕ) : ℚ :=
  (hLo (aN k) (bN k) Dk J : ℚ) / 2 ^ 64 + p2Lo k J K - epsHi k J K -
    2 * Ehi j0 * atHi (omHi k / dq J) K

def bx2Hi (k J K : ℕ) : ℚ := (hHi (aN k) (bN k) Dk J : ℚ) / 2 ^ 64 + p2Hi k J K + epsHi k J K

/-- The conditions of `source_bracket2` and of the arctan evaluation. -/
def srcCheck2 (k J K : ℕ) : Bool :=
  decide (1 ≤ omLo k) && decide (j0 ≤ J) && decide (2 ≤ cw J) &&
    decide (omLo k / dq J ≠ 1) && decide (omHi k / dq J ≠ 1) &&
    decide (0 ≤ bx2Lo k J K) && decide (0 ≤ bx2Hi k J K)

/-- **Soundness of the source part**: `π_lo · bx2Lo ≤ ∫ h₊ S_k ≤ π_hi · bx2Hi` at `L = 8/5`. -/
theorem srcCheck2_sound {k J K : ℕ} (h : srcCheck2 k J K = true) :
    ((piLo : ℝ) * bx2Lo k J K) ≤ ∫ r, hplus r * sourceS (8 / 5) r (k : ℤ) ∧
      ∫ r, hplus r * sourceS (8 / 5) r (k : ℤ) ≤ (piHi : ℝ) * bx2Hi k J K := by
  simp only [srcCheck2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hj0⟩, h2⟩, hn1⟩, hn2⟩, h6⟩, h7⟩ := h
  obtain ⟨hpl, hph⟩ := pi_bounds
  set ω : ℝ := 2 * Real.pi * ((k : ℤ) : ℝ) / (8 / 5) with hω
  have hωe : ω = 5 * Real.pi * k / 4 := by rw [hω]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hωl : ((omLo k : ℚ) : ℝ) ≤ ω := by
    rw [hωe]; simp only [AEGIS.CvSTauL85V1.omLo]; push_cast
    have := mul_le_mul_of_nonneg_right hpl.le hk0
    nlinarith
  have hωh : ω ≤ ((omHi k : ℚ) : ℝ) := by
    rw [hωe]; simp only [AEGIS.CvSTauL85V1.omHi]; push_cast
    have := mul_le_mul_of_nonneg_right hph.le hk0
    nlinarith
  have h1' : (1 : ℝ) ≤ omLo k := by exact_mod_cast h1
  have hω1 : 1 ≤ ω := h1'.trans hωl
  have hcJ : (cw J : ℝ) = archWidth J := cw_cast J
  have h2' : (2 : ℝ) ≤ archWidth J := by rw [← hcJ]; exact_mod_cast h2
  obtain ⟨hbl, hbh⟩ := source_bracket2 (L := 8 / 5) (by norm_num) (k : ℤ) J hω1 h2'
  rw [← hω] at hbl hbh
  set c : ℝ := archWidth J with hc
  set d : ℝ := archWidth J - 1 with hd
  have hd0 : 0 < d := by linarith
  have hdq : ((dq J : ℚ) : ℝ) = d := by simp only [dq]; push_cast; rw [hcJ]
  set I := ∫ r, hplus r * sourceS (8 / 5) r (k : ℤ) with hI
  set H := ∑ j ∈ range J, 2 * ω * (1 - Real.exp (-archWidth j * (8 / 5))) /
    (archWidth j ^ 2 + ω ^ 2) with hH
  set A := Real.arctan (ω / d) with hA
  have h0l : (0 : ℝ) ≤ omLo k := by linarith
  have hDk : 0 < Dk := by norm_num [Dk]
  obtain ⟨oc1, oc2⟩ := om_cast k
  obtain ⟨hHl, hHh⟩ := h_bounds hDk (oc1.symm ▸ hωl) (oc2.symm ▸ hωh) J (ω := ω)
  -- the arctan values
  have hq0 : (0 : ℚ) < dq J := by
    have : (0 : ℝ) < (dq J : ℝ) := by rw [hdq]; exact hd0
    exact_mod_cast this
  have hxl0 : (0 : ℚ) ≤ omLo k / dq J := div_nonneg (by exact_mod_cast h0l) hq0.le
  have hxh0 : (0 : ℚ) ≤ omHi k / dq J :=
    div_nonneg (by have : (0 : ℝ) ≤ omHi k := by linarith
                   exact_mod_cast this) hq0.le
  obtain ⟨al, -⟩ := at_bounds hxl0 hn1 K
  obtain ⟨-, ah⟩ := at_bounds hxh0 hn2 K
  push_cast at al ah
  rw [hdq] at al ah
  have hAl : ((atLo (omLo k / dq J) K : ℚ) : ℝ) ≤ A :=
    al.trans (Real.arctan_mono (div_le_div_of_nonneg_right hωl hd0.le))
  have hAh : A ≤ ((atHi (omHi k / dq J) K : ℚ) : ℝ) :=
    (Real.arctan_mono (div_le_div_of_nonneg_right hωh hd0.le)).trans ah
  have hA0 : 0 ≤ A := Real.arctan_nonneg.mpr (div_nonneg (by linarith) hd0.le)
  -- the rational part of `phi2`
  have hP : phi2 ω d = A - d * ω / (3 * (d ^ 2 + ω ^ 2) ^ 2) := rfl
  have hr1 : d * ω / (3 * (d ^ 2 + ω ^ 2) ^ 2) ≤
      d * ((omHi k : ℚ) : ℝ) / (3 * (d ^ 2 + ((omLo k : ℚ) : ℝ) ^ 2) ^ 2) := by
    have hd2 : 0 < d ^ 2 := pow_pos hd0 2
    apply div_le_div₀ (mul_nonneg hd0.le (by linarith)) (mul_le_mul_of_nonneg_left hωh hd0.le)
      (by positivity)
    gcongr
  have hr2 : d * ((omLo k : ℚ) : ℝ) / (3 * (d ^ 2 + ((omHi k : ℚ) : ℝ) ^ 2) ^ 2) ≤
      d * ω / (3 * (d ^ 2 + ω ^ 2) ^ 2) := by
    have hd2 : 0 < d ^ 2 := pow_pos hd0 2
    apply div_le_div₀ (mul_nonneg hd0.le (by linarith)) (mul_le_mul_of_nonneg_left hωl hd0.le)
      (by positivity)
    gcongr
  -- `ε`
  have heps : 5 * A / (c ^ 2 + ω ^ 2) ^ 2 ≤
      5 * ((atHi (omHi k / dq J) K : ℚ) : ℝ) / (c ^ 2 + ((omLo k : ℚ) : ℝ) ^ 2) ^ 2 := by
    have hc0 : 0 < c := by linarith
    apply div_le_div₀ (by linarith) (by linarith) (by positivity)
    gcongr
  have hE := Ehi_mono hj0 (j := J)
  have hE0 : 0 ≤ Real.exp (-archWidth J * (8 / 5)) := (Real.exp_pos _).le
  have hEA : 2 * Real.exp (-archWidth J * (8 / 5)) * A ≤
      2 * ((Ehi j0 : ℚ) : ℝ) * ((atHi (omHi k / dq J) K : ℚ) : ℝ) := by
    have := mul_le_mul hE hAh hA0 (hE0.trans hE)
    linarith
  have hcq : ((cw J : ℚ) : ℝ) = c := hcJ
  have hLO : ((bx2Lo k J K : ℚ) : ℝ) ≤ I / Real.pi := by
    have : ((bx2Lo k J K : ℚ) : ℝ) = (hLo (aN k) (bN k) Dk J : ℝ) / 2 ^ 64 +
        (((atLo (omLo k / dq J) K : ℚ) : ℝ) -
          d * ((omHi k : ℚ) : ℝ) / (3 * (d ^ 2 + ((omLo k : ℚ) : ℝ) ^ 2) ^ 2)) -
        5 * ((atHi (omHi k / dq J) K : ℚ) : ℝ) / (c ^ 2 + ((omLo k : ℚ) : ℝ) ^ 2) ^ 2 -
        2 * ((Ehi j0 : ℚ) : ℝ) * ((atHi (omHi k / dq J) K : ℚ) : ℝ) := by
      simp only [bx2Lo, p2Lo, epsHi]; push_cast; rw [hdq, hcq]
    rw [this]
    rw [hP] at hbl
    linarith
  have hHI : I / Real.pi ≤ ((bx2Hi k J K : ℚ) : ℝ) := by
    have : ((bx2Hi k J K : ℚ) : ℝ) = (hHi (aN k) (bN k) Dk J : ℝ) / 2 ^ 64 +
        (((atHi (omHi k / dq J) K : ℚ) : ℝ) -
          d * ((omLo k : ℚ) : ℝ) / (3 * (d ^ 2 + ((omHi k : ℚ) : ℝ) ^ 2) ^ 2)) +
        5 * ((atHi (omHi k / dq J) K : ℚ) : ℝ) / (c ^ 2 + ((omLo k : ℚ) : ℝ) ^ 2) ^ 2 := by
      simp only [bx2Hi, p2Hi, epsHi]; push_cast; rw [hdq, hcq]
    rw [this]
    rw [hP] at hbh
    linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h6' : (0 : ℝ) ≤ bx2Lo k J K := by exact_mod_cast h6
  have h7' : (0 : ℝ) ≤ bx2Hi k J K := by exact_mod_cast h7
  rw [le_div_iff₀ hpi0] at hLO
  rw [div_le_iff₀ hpi0] at hHI
  constructor
  · calc (piLo : ℝ) * bx2Lo k J K ≤ Real.pi * bx2Lo k J K := mul_le_mul_of_nonneg_right hpl.le h6'
      _ ≤ I := by linarith
  · calc I ≤ bx2Hi k J K * Real.pi := hHI
      _ ≤ bx2Hi k J K * piHi := mul_le_mul_of_nonneg_left hph.le h7'
      _ = (piHi : ℝ) * bx2Hi k J K := by ring

/-! ### `τ_k` -/

/-- **The check for one `k`** with the second-order tail. -/
def tauF2 (k J K : ℕ) (lo hi : ℚ) : Bool :=
  srcCheck2 k J K && decide (|thLo (5 * k * l2Lo / 4)| ≤ 2) &&
    decide (|thLo (5 * k * l3Lo / 4)| ≤ 2) && decide (|thLo (5 * k * l2Lo / 2)| ≤ 2) &&
    decide (lo ≤ piLo * bx2Lo k J K + primeLo k) && decide (piHi * bx2Hi k J K + primeHi k ≤ hi)

/-- **Soundness**: a passing check encloses `τ_k` at `L = 8/5` for every prime cutoff `M ≥ 4`. -/
theorem tauF2_sound {M : ℕ} (hM : 4 ≤ M) {k J K : ℕ} {lo hi : ℚ} (h : tauF2 k J K lo hi = true) :
    (lo : ℝ) ≤ tau M (8 / 5) k ∧ tau M (8 / 5) k ≤ hi := by
  simp only [tauF2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, h2⟩, h3⟩, h4⟩, hl⟩, hh⟩ := h
  have S := srcCheck2_sound hs
  have P := prime_bounds k h2 h3 h4
  have hl' : (lo : ℝ) ≤ (piLo : ℝ) * bx2Lo k J K + (primeLo k : ℝ) := by exact_mod_cast hl
  have hh' : (piHi : ℝ) * bx2Hi k J K + (primeHi k : ℝ) ≤ hi := by exact_mod_cast hh
  rw [tau_eq hM]
  push_cast at S P ⊢
  constructor <;> linarith [S.1, S.2, P.1, P.2]

end AEGIS.CvSTauFast2L85V1

#print axioms AEGIS.CvSTauFast2L85V1.srcCheck2_sound
#print axioms AEGIS.CvSTauFast2L85V1.tauF2_sound
