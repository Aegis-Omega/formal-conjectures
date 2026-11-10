import RHIndependentFinePrimeSupportV1
import AEGISOverlay.RHActualMixedDefectV1

/-!
Actual independent-packet reciprocal-prime norm bounds. The only analytic
estimate used is the existing distinct-packet ordinary-energy theorem.
-/

open Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHIndependentFinePrimeNormV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.RHActualMixedDefectV1
open AEGIS.RHIndependentFinePrimeSupportV1

theorem reciprocal_mixed_norm_le_mean_energy
    (p q : WeilCompactSmoothGV1) (m : ℕ) (hm : 0 < m) :
    ‖(1 / (m : ℂ)) * mixed p q ((m : ℝ)⁻¹)‖ ≤
      Real.exp (-Real.log (m : ℝ) / 2) *
        ((energy p.1 + energy q.1) / 2) := by
  exact distinct_reciprocal_mixed_norm_le_mean_energy_v1 p q m hm

theorem reciprocal_mixed_norm_le_sqrt_mean_energy
    (p q : WeilCompactSmoothGV1) (m : ℕ) (hm : 0 < m) :
    ‖(1 / (m : ℂ)) * mixed p q ((m : ℝ)⁻¹)‖ ≤
      (1 / Real.sqrt (m : ℝ)) *
        ((energy p.1 + energy q.1) / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h := reciprocal_mixed_norm_le_mean_energy p q m hm
  rw [show -Real.log (m : ℝ) / 2 = -(Real.log (m : ℝ) / 2) by ring,
    Real.exp_neg, Real.exp_half, Real.exp_log hmpos] at h
  simpa only [one_div] using h

/-- The old denominator25 and37 bounds are obtained by N=25 and N=37.
Only the original scalar integer-square comparison is required. -/
theorem reciprocal_mixed_norm_le_of_square_le
    (p q : WeilCompactSmoothGV1) (m : ℕ) (hm : 0 < m)
    (N : ℝ) (hN : 0 < N) (hNm : N ^ 2 ≤ (m : ℝ)) :
    ‖(1 / (m : ℂ)) * mixed p q ((m : ℝ)⁻¹)‖ ≤
      (1 / N) * ((energy p.1 + energy q.1) / 2) := by
  have hsqrt : N ≤ Real.sqrt (m : ℝ) :=
    Real.le_sqrt_of_sq_le hNm
  have hmean : 0 ≤ (energy p.1 + energy q.1) / 2 := by
    exact div_nonneg (add_nonneg (energy_nonnegative p.1)
      (energy_nonnegative q.1)) (by norm_num)
  exact (reciprocal_mixed_norm_le_sqrt_mean_energy p q m hm).trans
    (mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le hN hsqrt) hmean)

end AEGIS.RHIndependentFinePrimeNormV1

#print axioms AEGIS.RHIndependentFinePrimeNormV1.reciprocal_mixed_norm_le_mean_energy
#print axioms AEGIS.RHIndependentFinePrimeNormV1.reciprocal_mixed_norm_le_sqrt_mean_energy
#print axioms AEGIS.RHIndependentFinePrimeNormV1.reciprocal_mixed_norm_le_of_square_le
