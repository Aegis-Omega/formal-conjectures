import RHHardyNormalizationV1
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact transport of the supplied Hardy evaluator phase

The phase is `exp (-it log π / 2) * Gamma ((1/2 + it)/2) / ‖Gamma ((1/2 + it)/2)‖`.
The base π is positive, so the principal complex power has no branch ambiguity.
These identities concern Mathlib's continued Riemann zeta. They do not assert a
numerical enclosure for its value at any point.

Source: the supplied `hardy_interval_v1.py`, function `evaluate`.
-/

namespace AEGIS.RHHardyPhaseTransportV1

open AEGIS.RHCriticalLineSignV1 AEGIS.RHHardyNormalizationV1

/-- The positive real factor used by the supplied evaluator. -/
theorem pi_rpow_eq_exp :
    Real.pi ^ (-(1 / 4 : ℝ)) = Real.exp (-Real.log Real.pi / 4) := by
  rw [Real.rpow_def_of_pos Real.pi_pos]
  congr 1
  ring

/-- Split the principal π power into its positive modulus and exact phase. -/
theorem pi_cpow_line_factor (t : ℝ) :
    (Real.pi : ℂ) ^ (-lineAt t / 2) =
      ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log Real.pi : ℂ) / 2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'),
    ← Complex.ofReal_log Real.pi_pos.le, Real.rpow_def_of_pos Real.pi_pos,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [lineAt, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The supplied amplitude equals the modulus of Mathlib's archimedean factor. -/
theorem amplitude_eq_pi_rpow_gamma_norm (t : ℝ) :
    amplitude t = Real.pi ^ (-(1 / 4 : ℝ)) * ‖Complex.Gamma (lineAt t / 2)‖ := by
  rw [amplitude, Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-lineAt t / 2).re = -(1 / 4 : ℝ) := by
    simp [lineAt]
    norm_num
  rw [hre]

/-- The exponential amplitude is exactly the formula in the supplied evaluator. -/
theorem amplitude_eq_exp_gamma_norm (t : ℝ) :
    amplitude t = Real.exp (-Real.log Real.pi / 4) * ‖Complex.Gamma (lineAt t / 2)‖ := by
  rw [amplitude_eq_pi_rpow_gamma_norm, pi_rpow_eq_exp]

/-- Divide the real completed zeta by its positive amplitude in ℂ. -/
theorem completed_div_amplitude_eq_normalized (t : ℝ) :
    Xi t / (amplitude t : ℂ) = (normalized t : ℂ) := by
  apply Complex.ext
  · simp [normalized]
  · simp [Xi_im]

/-- Transport through Mathlib's completed-zeta product on the critical line. -/
theorem gammaR_phase_zeta_eq_normalized (t : ℝ) :
    Complex.Gammaℝ (lineAt t) / (amplitude t : ℂ) * riemannZeta (lineAt t) =
      (normalized t : ℂ) := by
  rw [div_mul_eq_mul_div]
  have hs : 0 < (lineAt t).re := by rw [lineAt_re]; norm_num
  rw [← completed_eq_mul hs]
  exact completed_div_amplitude_eq_normalized t

/-- The supplied direct Gamma phase equals the normalized archimedean factor. -/
theorem evaluator_phase_eq_gammaR_div_amplitude (t : ℝ) :
    Complex.exp (-(t : ℂ) * Complex.I * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (lineAt t / 2) / (‖Complex.Gamma (lineAt t / 2)‖ : ℂ) =
      Complex.Gammaℝ (lineAt t) / (amplitude t : ℂ) := by
  have hp : ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  rw [Complex.Gammaℝ_def, pi_cpow_line_factor,
    amplitude_eq_pi_rpow_gamma_norm, Complex.ofReal_mul]
  simpa only [mul_assoc] using
    (mul_div_mul_left
      (Complex.exp (-(t : ℂ) * Complex.I * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (lineAt t / 2))
      (‖Complex.Gamma (lineAt t / 2)‖ : ℂ) hp).symm

/-- Exact identity for the mathematical expression evaluated by the supplied code. -/
theorem evaluator_phase_zeta_eq_normalized (t : ℝ) :
    Complex.exp (-(t : ℂ) * Complex.I * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (lineAt t / 2) / (‖Complex.Gamma (lineAt t / 2)‖ : ℂ) *
        riemannZeta (lineAt t) = (normalized t : ℂ) := by
  rw [evaluator_phase_eq_gammaR_div_amplitude]
  exact gammaR_phase_zeta_eq_normalized t

end AEGIS.RHHardyPhaseTransportV1

#check AEGIS.RHHardyPhaseTransportV1.pi_cpow_line_factor
#check AEGIS.RHHardyPhaseTransportV1.amplitude_eq_pi_rpow_gamma_norm
#check AEGIS.RHHardyPhaseTransportV1.amplitude_eq_exp_gamma_norm
#check AEGIS.RHHardyPhaseTransportV1.gammaR_phase_zeta_eq_normalized
#check AEGIS.RHHardyPhaseTransportV1.evaluator_phase_eq_gammaR_div_amplitude
#check AEGIS.RHHardyPhaseTransportV1.evaluator_phase_zeta_eq_normalized
#print AEGIS.RHHardyPhaseTransportV1.amplitude_eq_pi_rpow_gamma_norm
#print AEGIS.RHHardyPhaseTransportV1.amplitude_eq_exp_gamma_norm
#print AEGIS.RHHardyPhaseTransportV1.evaluator_phase_zeta_eq_normalized
#print axioms AEGIS.RHHardyPhaseTransportV1.pi_rpow_eq_exp
#print axioms AEGIS.RHHardyPhaseTransportV1.pi_cpow_line_factor
#print axioms AEGIS.RHHardyPhaseTransportV1.amplitude_eq_pi_rpow_gamma_norm
#print axioms AEGIS.RHHardyPhaseTransportV1.amplitude_eq_exp_gamma_norm
#print axioms AEGIS.RHHardyPhaseTransportV1.completed_div_amplitude_eq_normalized
#print axioms AEGIS.RHHardyPhaseTransportV1.gammaR_phase_zeta_eq_normalized
#print axioms AEGIS.RHHardyPhaseTransportV1.evaluator_phase_eq_gammaR_div_amplitude
#print axioms AEGIS.RHHardyPhaseTransportV1.evaluator_phase_zeta_eq_normalized
