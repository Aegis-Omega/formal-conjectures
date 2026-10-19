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
import CvSCrossBoundV1

/-!
# Fourier series of a complement on `[0, L_T]` (CvS step 6h, ring tree)

For a bounded integrable `w` supported in `[0, L_T]` with Mathlib's coefficients
`ŵ_k = fourierCoeffOn hLT w k`:

* `coef_eq`: `∫ w · conj e_k = L_T ŵ_k` for the atoms `e_k = trigAtom L_T k`;
* `hasSum_coef` (Parseval, `hasSum_sq_fourierCoeffOn`): `Σ_k |ŵ_k|² = L_T⁻¹ ∫ |w|²`;
* `norm_sub_trigPoly`: `∫ |w − Σ_{k∈S} ŵ_k e_k|² = ∫ |w|² − L_T Σ_{k∈S} |ŵ_k|²`;
* `tendsto_partialSum`: the symmetric partial sums converge to `w` in `L²`.

Not RH.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSFourierIntervalV1

open AEGIS.CvSPrimeBlockV1 AEGIS.CvSMassV1

theorem coef_eq {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hs : Function.support w ⊆ Icc 0 LT)
    (k : ℤ) : ∫ x, w x * conj (trigAtom LT k x) = LT * fourierCoeffOn hLT w k := by
  have hind : (fun x => w x * conj (trigAtom LT k x)) =
      Set.indicator (Icc 0 LT) (fun x : ℝ => w x * cexp (2 * Real.pi * I * (-k : ℤ) * x / LT)) := by
    funext x
    by_cases hx : x ∈ Icc 0 LT
    · simp only [trigAtom, indicator_of_mem hx]
      congr 1
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
      push_cast
      ring
    · have hw0 : w x = 0 := Function.notMem_support.mp fun h => hx (hs h)
      simp [hw0, indicator_of_notMem hx]
  have hLT0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hLT.le, fourierCoeffOn_eq_integral w k hLT]
  simp only [fourier_coe_apply, smul_eq_mul, Complex.real_smul, sub_zero]
  have e : (∫ x in (0 : ℝ)..LT, w x * cexp (2 * Real.pi * I * (-k : ℤ) * x / LT)) =
      ∫ x in (0 : ℝ)..LT, cexp (2 * Real.pi * I * (-k : ℤ) * x / LT) * w x := by
    congr 1
    funext x
    ring
  rw [e]
  push_cast
  field_simp

theorem hasSum_coef {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ}
    (hC : ∀ x, ‖w x‖ ≤ C) (hs : Function.support w ⊆ Icc 0 LT) :
    HasSum (fun k => ‖fourierCoeffOn hLT w k‖ ^ 2) (LT⁻¹ * ∫ x, ‖w x‖ ^ 2) := by
  have hL2 : MemLp w 2 (volume.restrict (Ioc 0 LT)) :=
    MemLp.of_bound hw.1.restrict C (Eventually.of_forall hC)
  have h := hasSum_sq_fourierCoeffOn hLT hL2
  have hint : (∫ x in (0 : ℝ)..LT, ‖w x‖ ^ 2) = ∫ x, ‖w x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hLT.le, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : w x = 0 := Function.notMem_support.mp fun h => hx (hs h)
    simp [this]
  rw [hint, sub_zero, smul_eq_mul] at h
  exact h

theorem norm_trigAtom_le (LT : ℝ) (k : ℤ) (x : ℝ) : ‖trigAtom LT k x‖ ≤ 1 := by
  by_cases hx : x ∈ Icc 0 LT
  · simp only [trigAtom, indicator_of_mem hx]
    rw [Complex.norm_exp]
    have : (2 * Real.pi * I * k * x / LT).re = 0 := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  · simp [trigAtom, indicator_of_notMem hx]

theorem norm_trigPoly_le (LT : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) (x : ℝ) :
    ‖trigPoly LT S v x‖ ≤ ∑ k ∈ S, ‖v k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_trigAtom_le LT k x)

theorem integral_normSq_trigPoly {LT : ℝ} (hLT : 0 < LT) (S : Finset ℤ) (v : ℤ → ℂ) :
    ∫ x, ‖trigPoly LT S v x‖ ^ 2 = LT * ∑ k ∈ S, ‖v k‖ ^ 2 := by
  have h := trigPoly_autocorrelation (L := LT) (y := 0) le_rfl S v
  simp only [add_zero] at h
  have hat : ∀ n m : ℤ, ∫ x, trigAtom LT n x * conj (trigAtom LT m x) =
      if n = m then (LT : ℂ) else 0 := fun n m => by
    have := trigAtom_autocorrelation hLT le_rfl hLT.le n m
    simp only [add_zero, sub_zero] at this
    rw [this]
    split_ifs <;> simp
  simp_rw [hat, mul_ite, mul_zero, Finset.sum_ite_eq] at h
  have e : ∀ x, ((‖trigPoly LT S v x‖ ^ 2 : ℝ) : ℂ) =
      trigPoly LT S v x * conj (trigPoly LT S v x) :=
    fun x => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e]
  rw [h]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [if_pos hk]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- `∫ w · conj(Σ_k u_k e_k) = L_T Σ_k conj(u_k) ŵ_k`. -/
theorem integral_mul_conj_trigPoly {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hw : Integrable w)
    (hs : Function.support w ⊆ Icc 0 LT) (S : Finset ℤ) (u : ℤ → ℂ) :
    ∫ x, w x * conj (trigPoly LT S u x) = LT * ∑ k ∈ S, conj (u k) * fourierCoeffOn hLT w k := by
  have e : ∀ x, w x * conj (trigPoly LT S u x) =
      ∑ k ∈ S, conj (u k) * (w x * conj (trigAtom LT k x)) := fun x => by
    simp only [trigPoly, map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => ?_]
  · simp_rw [integral_const_mul, coef_eq hLT hs]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · refine Integrable.const_mul ?_ _
    have hat : AEStronglyMeasurable (trigAtom LT k) := by
      have e : trigAtom LT k =
          Set.indicator (Icc 0 LT) (fun x : ℝ => cexp (2 * Real.pi * I * k * x / LT)) := rfl
      rw [e]
      exact (by fun_prop : Continuous fun x : ℝ =>
        cexp (2 * Real.pi * I * k * x / LT)).aestronglyMeasurable.indicator measurableSet_Icc
    have := hw.bdd_mul (c := 1) (Complex.continuous_conj.comp_aestronglyMeasurable hat)
      (Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact norm_trigAtom_le LT k x)
    refine this.congr (Eventually.of_forall fun x => ?_)
    ring

/-- **Pythagoras for the Fourier partial sums.** -/
theorem norm_sub_trigPoly {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ}
    (hC : ∀ x, ‖w x‖ ≤ C) (hs : Function.support w ⊆ Icc 0 LT) (S : Finset ℤ) :
    ∫ x, ‖w x - trigPoly LT S (fourierCoeffOn hLT w) x‖ ^ 2 =
      (∫ x, ‖w x‖ ^ 2) - LT * ∑ k ∈ S, ‖fourierCoeffOn hLT w k‖ ^ 2 := by
  set c := fourierCoeffOn hLT w
  set g := trigPoly LT S c
  set B := ∑ k ∈ S, ‖c k‖
  have hg : Integrable g := trigPoly_integrable LT S c
  have hgB : ∀ x, ‖g x‖ ≤ B := norm_trigPoly_le LT S c
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hw2 : Integrable fun x => ‖w x‖ ^ 2 :=
    (hw.norm.const_mul C).mono' (hw.1.norm.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hC x, norm_nonneg (w x)])
  have hg2 : Integrable fun x => ‖g x‖ ^ 2 :=
    (hg.norm.const_mul B).mono' (hg.1.norm.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hgB x, norm_nonneg (g x)])
  have hwg : Integrable fun x => w x * conj (g x) := by
    have := hw.bdd_mul (c := B) (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact hgB x)
    refine this.congr (Eventually.of_forall fun x => ?_)
    ring
  have hre : Integrable fun x => (w x * conj (g x)).re := hwg.re
  have hpt : ∀ x, ‖w x - g x‖ ^ 2 = ‖w x‖ ^ 2 + ‖g x‖ ^ 2 - 2 * (w x * conj (g x)).re :=
    fun x => by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_sub]
  have hcross : ∫ x, w x * conj (g x) = LT * ∑ k ∈ S, ‖c k‖ ^ 2 := by
    rw [integral_mul_conj_trigPoly hLT hw hs]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show fourierCoeffOn hLT w k = c k from rfl, ← Complex.ofReal_pow,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have hcre : ∫ x, (w x * conj (g x)).re = LT * ∑ k ∈ S, ‖c k‖ ^ 2 := by
    have := integral_re hwg
    simp only [RCLike.re_to_complex] at this
    rw [this, hcross]
    norm_cast
  have hsum : Integrable fun x => ‖w x‖ ^ 2 + ‖g x‖ ^ 2 := hw2.add hg2
  simp_rw [hpt]
  rw [integral_sub hsum (hre.const_mul 2), integral_add hw2 hg2, integral_const_mul,
    hcre, integral_normSq_trigPoly hLT]
  ring

/-- The symmetric Fourier partial sum on `[0, L_T]`. -/
def partialSum {LT : ℝ} (hLT : 0 < LT) (w : ℝ → ℂ) (N : ℕ) : ℝ → ℂ :=
  trigPoly LT (Finset.Icc (-(N : ℤ)) N) (fourierCoeffOn hLT w)

/-- **The partial sums converge in `L²`.** -/
theorem tendsto_partialSum {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ}
    (hC : ∀ x, ‖w x‖ ≤ C) (hs : Function.support w ⊆ Icc 0 LT) :
    Tendsto (fun N : ℕ => ∫ x, ‖w x - partialSum hLT w N x‖ ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun s : Finset ℤ => ∑ k ∈ s, ‖fourierCoeffOn hLT w k‖ ^ 2) atTop
      (𝓝 (LT⁻¹ * ∫ x, ‖w x‖ ^ 2)) := hasSum_coef hLT hw hC hs
  have h2 := ((h.comp Finset.tendsto_Icc_neg).const_mul LT).const_sub (∫ x, ‖w x‖ ^ 2)
  have e : (∫ x, ‖w x‖ ^ 2) - LT * (LT⁻¹ * ∫ x, ‖w x‖ ^ 2) = 0 := by
    field_simp
    ring
  rw [e] at h2
  refine h2.congr fun N => ?_
  simp only [Function.comp_apply, partialSum]
  rw [norm_sub_trigPoly hLT hw hC hs]

end AEGIS.CvSFourierIntervalV1

#print axioms AEGIS.CvSFourierIntervalV1.coef_eq
#print axioms AEGIS.CvSFourierIntervalV1.hasSum_coef
#print axioms AEGIS.CvSFourierIntervalV1.integral_normSq_trigPoly
#print axioms AEGIS.CvSFourierIntervalV1.integral_mul_conj_trigPoly
#print axioms AEGIS.CvSFourierIntervalV1.norm_sub_trigPoly
#print axioms AEGIS.CvSFourierIntervalV1.tendsto_partialSum
