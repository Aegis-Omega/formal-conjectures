import WeilSeparatedArchBridgeV31
import Mathlib.Tactic

/-!
Independent-packet prime-window support and exact reciprocal normalization.
The geometric hypotheses are on the original actual packets. No common
mother, moment-free surrogate, Weil-sign hypothesis or prime bound is used.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHIndependentFinePrimeSupportV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilSeparatedArchBridgeV31

theorem mixed_exp_zero_of_log_windows
    (p q : WeilCompactSmoothGV1) (r a b u : ℝ)
    (hp : LogSupportIn p (a - r) (a + r))
    (hq : LogSupportIn q (b - r) (b + r))
    (hu : 2 * r < |u + (b - a)|) :
    mixed p q (Real.exp u) = 0 := by
  have hz : logCrossV28 p q u = 0 := by
    apply logCross_zero_outside p q (a - r) (a + r)
      (b - r) (b + r) u hp hq
    by_cases hl : u < (a - r) - (b + r)
    · exact Or.inl hl
    · right
      by_contra hh
      have hlo := le_of_not_gt hl
      have hhi := le_of_not_gt hh
      have habs : |u + (b - a)| ≤ 2 * r :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact (not_le_of_gt hu) habs
  rw [logCross_eq_mixed_v28] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by simp)

theorem mixed_nat_zero_of_log_windows
    (p q : WeilCompactSmoothGV1) (r a b : ℝ)
    (hp : LogSupportIn p (a - r) (a + r))
    (hq : LogSupportIn q (b - r) (b + r))
    (hsep : 2 * r < b - a) (m : ℕ) (hm : 0 < m) :
    mixed p q (m : ℝ) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmone
  have hu : 2 * r < |Real.log (m : ℝ) + (b - a)| :=
    lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hz := mixed_exp_zero_of_log_windows p q r a b
    (Real.log (m : ℝ)) hp hq hu
  simpa only [Real.exp_log hmpos] using hz

theorem mixed_inv_nat_zero_of_log_windows
    (p q : WeilCompactSmoothGV1) (r a b : ℝ)
    (hp : LogSupportIn p (a - r) (a + r))
    (hq : LogSupportIn q (b - r) (b + r))
    (m : ℕ) (hm : 0 < m)
    (hfar : 2 * r < |Real.log (m : ℝ) - (b - a)|) :
    mixed p q ((m : ℝ)⁻¹) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hu : 2 * r < |-Real.log (m : ℝ) + (b - a)| := by
    rw [show -Real.log (m : ℝ) + (b - a) =
      -(Real.log (m : ℝ) - (b - a)) by ring, abs_neg]
    exact hfar
  have hz := mixed_exp_zero_of_log_windows p q r a b
    (-Real.log (m : ℝ)) hp hq hu
  simpa only [Real.exp_neg, Real.exp_log hmpos] using hz

theorem mixed_nat_zero_of_fine_separation
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (hsep : (1 / 128 : ℝ) < b - a) (m : ℕ) (hm : 0 < m) :
    mixed p q (m : ℝ) = 0 := by
  apply mixed_nat_zero_of_log_windows p q (1 / 256) a b hp hq
  · norm_num
    exact hsep
  · exact hm

theorem mixed_inv_nat_zero_of_outside_fine_window
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (m : ℕ) (hm : 0 < m)
    (hfar : (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    mixed p q ((m : ℝ)⁻¹) = 0 := by
  apply mixed_inv_nat_zero_of_log_windows p q (1 / 256) a b hp hq m hm
  norm_num
  exact hfar

/-- Exact normalization of an actual reciprocal prime sample. -/
theorem reciprocal_mixed_eq_exp_logCross
    (p q : WeilCompactSmoothGV1) (m : ℕ) (hm : 0 < m) :
    (1 / (m : ℂ)) * mixed p q ((m : ℝ)⁻¹) =
      (Real.exp (-Real.log (m : ℝ) / 2) : ℂ) *
        logCrossV28 p q (-Real.log (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  let α : ℝ := Real.exp (-Real.log (m : ℝ) / 2)
  have hcross : logCrossV28 p q (-Real.log (m : ℝ)) =
      (α : ℂ) * mixed p q ((m : ℝ)⁻¹) := by
    simpa only [α, Real.exp_neg, Real.exp_log hmpos] using
      logCross_eq_mixed_v28 p q (-Real.log (m : ℝ))
  have hinv : (m : ℝ)⁻¹ = α * α := by
    dsimp [α]
    rw [← Real.exp_add]
    have harg : -Real.log (m : ℝ) / 2 + -Real.log (m : ℝ) / 2 =
        -Real.log (m : ℝ) := by ring
    rw [harg, Real.exp_neg, Real.exp_log hmpos]
  change (1 / (m : ℂ)) * mixed p q ((m : ℝ)⁻¹) =
    (α : ℂ) * logCrossV28 p q (-Real.log (m : ℝ))
  rw [hcross]
  have hscalar : (1 / (m : ℂ)) = (α : ℂ) * (α : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hinv
    push_cast at h
    simpa only [one_div] using h
  rw [hscalar]
  ring

/-- The arithmetic window input is a scalar von Mangoldt certificate,
not an assumed bound on any Weil form. The gap-1..8 sources produce it. -/
theorem prime_term_zero_of_fine_window_vonMangoldt
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (hsep : (1 / 128 : ℝ) < b - a) (n : ℕ)
    (hvm : |Real.log ((n + 1 : ℕ) : ℝ) - (b - a)| ≤ 1 / 128 →
      ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeTermV1 (mixed p q) n = 0 := by
  by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - (b - a)| ≤ 1 / 128
  · simp only [WeilPrimeTermV1, hvm hwin, Complex.ofReal_zero, zero_mul]
  · have hpos := mixed_nat_zero_of_fine_separation p q a b hp hq hsep
      (n + 1) (by omega)
    have hinv := mixed_inv_nat_zero_of_outside_fine_window p q a b hp hq
      (n + 1) (by omega) (lt_of_not_ge hwin)
    simp only [WeilPrimeTermV1, hpos, hinv, add_zero, mul_zero]

end AEGIS.RHIndependentFinePrimeSupportV1

#print axioms AEGIS.RHIndependentFinePrimeSupportV1.mixed_exp_zero_of_log_windows
#print axioms AEGIS.RHIndependentFinePrimeSupportV1.mixed_nat_zero_of_fine_separation
#print axioms AEGIS.RHIndependentFinePrimeSupportV1.mixed_inv_nat_zero_of_outside_fine_window
#print axioms AEGIS.RHIndependentFinePrimeSupportV1.reciprocal_mixed_eq_exp_logCross
#print axioms AEGIS.RHIndependentFinePrimeSupportV1.prime_term_zero_of_fine_window_vonMangoldt
