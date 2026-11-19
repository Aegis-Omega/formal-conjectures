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
import WeilWidthArchIntegralV27
import WeilH64ElementaryV7

/-!
# OPTIMUS V7: the diagonal of the actual Weil form at a general packet radius

For a packet `g` whose logarithmic lift is supported in `[a − R, a + R]` (`0 < R ≤ 1/64`), on the
actual repository functional (`B g g = WeilExplicitRightSideV1 (mixed g g)`):

* `arch_log_le_energy`: for every `u > 0` the transformed Archimedean integrand
  `(eᵘ Re A(eᵘ) − E)/sinh u` is at most `E` (V7 §3: `e^{u/2} − 1 ≤ sinh u`);
* `arch_tail_eq_radius`: beyond `2R` it is exactly `−E/sinh u`;
* `diag_radius`: `E · (T(2R) − (log 4π + γ) − 2R) ≤ −Re B(g, g)`, with `T(w) = ∫_w^∞ du/sinh u`;
* `diag_v7`: at `R = 1/4096`, `(13/3 − 1/2048) E ≤ −Re B(g, g)`.

The prime sum vanishes by the width-1/32 lane (`R ≤ 1/64`). Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators

noncomputable section

namespace AEGIS.WeilH64DiagonalV7

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilMixedAlgebraV2

/-- The logarithmic lift of `g` lives in `[a − R, a + R]`. -/
def LogRadiusAt (g : WeilCompactSmoothGV1) (a R : ℝ) : Prop :=
  LogSupportIn g (a - R) (a + R)

/-- The `1/sinh` tail beyond `w`. -/
def sinhTail (w : ℝ) : ℝ := ∫ u in Ioi w, 1 / Real.sinh u

theorem width_of_radius {g : WeilCompactSmoothGV1} {a R : ℝ} (hw : LogRadiusAt g a R)
    (hR : R ≤ 1 / 64) : WidthOneThirtyTwoAt g a := by
  intro t ht
  have h := hw ht
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem logCorrelation_zero_of_radius (g : WeilCompactSmoothGV1) {a R u : ℝ}
    (hw : LogRadiusAt g a R) (hu : 2 * R < u) : logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hv := hw (subset_tsupport _ h0)
      have hvu := hw (subset_tsupport _ h1)
      exfalso
      linarith [hv.1, hv.2, hvu.1, hvu.2]

/-- `e^{u/2} − 1 ≤ sinh u` for `u ≥ 0`. -/
theorem exp_half_sub_one_le_sinh {u : ℝ} (hu : 0 ≤ u) : Real.exp (u / 2) - 1 ≤ Real.sinh u := by
  set s := Real.exp (u / 2)
  set t := Real.exp (-u / 2)
  have hst : s * t = 1 := by
    simp only [s, t, ← Real.exp_add]; rw [show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht0 : 0 < t := Real.exp_pos _
  have hsinh : Real.sinh u = (s ^ 2 - t ^ 2) / 2 := by
    rw [Real.sinh_eq]
    simp only [s, t, ← Real.exp_nat_mul]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hsinh]
  nlinarith [sq_nonneg (s - 1), mul_pos ht0 ht0]

/-- **V7 inner bound**: the transformed Archimedean integrand never exceeds the energy. -/
theorem arch_log_le_energy (g : WeilCompactSmoothGV1) {u : ℝ} (hu : 0 < u) :
    widthArchLogIntegrandV26 g u ≤ energy g.1 := by
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hsinh : 0 < Real.sinh u := AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos hu
  have hnum := autocorrelation_exp_re_le_v26 g u
  have hk := exp_half_sub_one_le_sinh hu.le
  unfold widthArchLogIntegrandV26
  rw [div_le_iff₀ hsinh]
  nlinarith [mul_le_mul_of_nonneg_left hk hE]

theorem arch_tail_eq_radius (g : WeilCompactSmoothGV1) {a R u : ℝ} (hw : LogRadiusAt g a R)
    (hu : 2 * R < u) : widthArchLogIntegrandV26 g u = -energy g.1 / Real.sinh u := by
  have hC := logCorrelation_zero_of_radius g hw hu
  rw [logCorrelation_eq_autocorrelation_v25] at hC
  have he : (Real.exp (u / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hA : WeilAutocorrelationV1 g (Real.exp u) = 0 := (mul_eq_zero.mp hC).resolve_left he
  unfold widthArchLogIntegrandV26
  rw [hA]
  simp

/-- **The Archimedean budget at radius `R`.** -/
theorem arch_budget_radius (g : WeilCompactSmoothGV1) {a R : ℝ} (hR : 0 < R)
    (hw : LogRadiusAt g a R) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (2 * R - sinhTail (2 * R)) := by
  rw [archimedean_real_eq_log_integral_v27]
  have hfull := width_arch_log_integrableOn_v27 g
  set F := widthArchLogIntegrandV26 g with hF
  have hinner : IntegrableOn F (Ioc (0 : ℝ) (2 * R)) :=
    hfull.mono_set fun u hu => hu.1
  have htail : IntegrableOn F (Ioi (2 * R)) :=
    hfull.mono_set fun u hu => by
      change (2 * R) < u at hu; change (0 : ℝ) < u; linarith
  have hsplit : (∫ u in Ioi (0 : ℝ), F u) =
      (∫ u in Ioc (0 : ℝ) (2 * R), F u) + ∫ u in Ioi (2 * R), F u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * R),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hinner htail]
  rw [hsplit]
  have hin : (∫ u in Ioc (0 : ℝ) (2 * R), F u) ≤ 2 * R * energy g.1 := by
    have hconst : IntegrableOn (fun _ : ℝ => energy g.1) (Ioc (0 : ℝ) (2 * R)) :=
      continuous_const.integrableOn_Ioc
    calc (∫ u in Ioc (0 : ℝ) (2 * R), F u)
        ≤ ∫ _u in Ioc (0 : ℝ) (2 * R), energy g.1 :=
          setIntegral_mono_on hinner hconst measurableSet_Ioc fun u hu => arch_log_le_energy g hu.1
      _ = 2 * R * energy g.1 := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith)]
          ring
  have hout : (∫ u in Ioi (2 * R), F u) = -energy g.1 * sinhTail (2 * R) := by
    calc (∫ u in Ioi (2 * R), F u)
        = ∫ u in Ioi (2 * R), (-energy g.1) * (1 / Real.sinh u) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          rw [hF, arch_tail_eq_radius g hw hu]
          ring
      _ = -energy g.1 * sinhTail (2 * R) := by rw [integral_const_mul]; rfl
  rw [hout]
  nlinarith

/-- **Diagonal coercivity at radius `R`.** -/
theorem diag_radius (g : WeilCompactSmoothGV1) {a R : ℝ} (hR : 0 < R) (hR64 : R ≤ 1 / 64)
    (hw : LogRadiusAt g a R) :
    energy g.1 * (sinhTail (2 * R) - diagonalKappaV21 - 2 * R) ≤ -(B g g).re :=
  actual_diagonal_from_arch_budget g (sinhTail (2 * R)) (2 * R)
    (AEGIS.WeilWidthPrimeVanishingV23.diagonal_prime_sum_zero g a (width_of_radius hw hR64))
    (arch_budget_radius g hR hw)

/-- `T(w) ≥ log((2 − w)/w)` for `0 < w < 2`. -/
theorem sinhTail_ge {w : ℝ} (hw : 0 < w) (hw2 : w < 2) : Real.log ((2 - w) / w) ≤ sinhTail w := by
  unfold sinhTail
  rw [AEGIS.WeilArchimedeanCothTailV1.integral_one_div_sinh_Ioi hw]
  have he : Real.exp (-w) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 : 1 - w ≤ Real.exp (-w) := by linarith [Real.add_one_le_exp (-w)]
  have hden : 0 < 1 - Real.exp (-w) := by linarith
  have hle : 1 - Real.exp (-w) ≤ w := by linarith
  apply Real.log_le_log (by apply div_pos <;> linarith)
  rw [div_le_div_iff₀ hw hden]
  nlinarith

/-- **The V7 diagonal**: `(13/3 − 1/2048) E ≤ −Re B(g, g)` at `R = 1/4096`. -/
theorem diag_v7 (g : WeilCompactSmoothGV1) {a : ℝ} (hw : LogRadiusAt g a (1 / 4096)) :
    ((13 : ℝ) / 3 - 1 / 2048) * energy g.1 ≤ -(B g g).re := by
  have hd := diag_radius g (by norm_num) (by norm_num) hw
  have hT := sinhTail_ge (w := 2 * (1 / 4096)) (by norm_num) (by norm_num)
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  -- log((2 − w)/w) = log 4095 ≥ 12 log 2 − 1/4095
  have hlog : 12 * Real.log 2 - 1 / 4095 ≤ Real.log ((2 - 2 * (1 / 4096)) / (2 * (1 / 4096))) := by
    rw [show (2 - 2 * (1 / 4096 : ℝ)) / (2 * (1 / 4096)) = 4096 * (4095 / 4096) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4095 / 4096 by norm_num)
    norm_num at this ⊢
    linarith
  have hpi : Real.log (4 * Real.pi) < 4 * Real.log 2 := by
    have : Real.log (4 * Real.pi) < Real.log 16 :=
      Real.log_lt_log (by positivity) (by linarith [Real.pi_lt_d2])
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    norm_num at this
    linarith
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hl := Real.log_two_gt_d9
  have hconst : (13 : ℝ) / 3 - 1 / 2048 ≤ sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096) := by
    unfold diagonalKappaV21
    linarith
  calc ((13 : ℝ) / 3 - 1 / 2048) * energy g.1
      ≤ (sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096)) * energy g.1 :=
        mul_le_mul_of_nonneg_right hconst hE
    _ = energy g.1 * (sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096)) := by ring
    _ ≤ -(B g g).re := hd

end AEGIS.WeilH64DiagonalV7

#print axioms AEGIS.WeilH64DiagonalV7.arch_log_le_energy
#print axioms AEGIS.WeilH64DiagonalV7.arch_budget_radius
#print axioms AEGIS.WeilH64DiagonalV7.diag_radius
#print axioms AEGIS.WeilH64DiagonalV7.diag_v7
