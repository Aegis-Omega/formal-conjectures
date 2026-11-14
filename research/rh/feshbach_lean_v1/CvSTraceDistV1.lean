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

import CvSTraceCramerV1
import CvSAtomInversionV1
import CvSTraceV1

/-!
# The explicit trace coefficients and their trial distance (CvS step K3d)

`cfC t = (α_1, …, α_139, γ₀, γ₁)` with `α = alpha 70 (bC t)` (`CvSAtomInversionV1`) and
`γ = gam t` (`CvSTraceCramerV1`), for any family `V : Fin 141 → ℝ → ℂ` whose first 139
members are `momentAtom L (i − 69)` and whose last two are `e^{σ_s x}`:

* `cf_sum_eq`: on `[0, L]`, `Σ_i cfC t i · V i x = P_t − γ₀ p₀ − γ₁ p₁ + γ₀ u₀ + γ₁ u₁`;
* `trialDist_le`: `trialDist ≤ (1+ε) ∫|f_t − P_t|² + (1+1/ε)(|γ₀|²+|γ₁|²)(∫|u₀−p₀|² + ∫|u₁−p₁|²)`;
* `trialDist_continuous`: `t ↦ trialDist` is continuous, hence measurable (needed for `hR`).

Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSTraceDistV1

open AEGIS.CvSPrimeBlockV1 AEGIS.CvSFourierIntervalV1 AEGIS.CvSMomentV1 AEGIS.CvSTraceCoefV1
open AEGIS.CvSTraceCramerV1 AEGIS.CvSAtomInversionV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSTraceV1
open AEGIS.CvSMassV1

variable {LT : ℝ} (hLT : 0 < LT)

/-- The 141 explicit trace coefficients. -/
def cfC (t : ℝ) : Fin 141 → ℂ :=
  Fin.append (fun i : Fin 139 => alpha 70 (bC hLT 70 t) (i + 1)) (fun s : Fin 2 => gam hLT 70 t s)

/-- The admissible trace families: the 139 sinSq atoms, then `e^{σ₀x}`, `e^{σ₁x}`. -/
structure TraceFamily (LT : ℝ) (V : Fin 141 → ℝ → ℂ) : Prop where
  atom : ∀ (i : Fin 139) (x : ℝ), V (Fin.castAdd 2 i) x = momentAtom LT ((i : ℤ) - 69) x
  mom : ∀ (s : Fin 2) (x : ℝ), V (Fin.natAdd 139 s) x = ((Real.exp (sig s * x) : ℝ) : ℂ)

/-! ### The coefficient identity -/

theorem om_sq_sub_ne (k : ℤ) : om LT k ^ 2 - 1 / 4 ≠ 0 := by
  have e : om LT k ^ 2 - 1 / 4 = ((-((2 * Real.pi * k / LT) ^ 2 + 1 / 4) : ℝ) : ℂ) := by
    simp only [om]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [e]
  have : 0 < (2 * Real.pi * k / LT) ^ 2 + 1 / 4 := by positivity
  exact_mod_cast (by linarith : -((2 * Real.pi * k / LT) ^ 2 + 1 / 4) ≠ 0)

theorem atom_part (hdet : detG hLT 70 ≠ 0) (t x : ℝ) :
    ∑ i : Fin 139, alpha 70 (bC hLT 70 t) (i + 1) * momentAtom LT ((i : ℤ) - 69) x =
      ∑ k ∈ K 70, vC hLT 70 t k * cexp (iw LT k * x) := by
  obtain ⟨h0, h1⟩ := moment_conds hLT 70 hdet t
  have hs := atom_sum LT (N := 70) (by norm_num) (bC hLT 70 t) h0 h1 x
  rw [Fin.sum_univ_eq_sum_range (fun i => alpha 70 (bC hLT 70 t) (i + 1) *
    momentAtom LT ((i : ℤ) - 69) x) 139]
  have e1 : ∀ i : ℕ, (((i + 1 : ℕ) : ℤ) - (70 : ℕ)) = (i : ℤ) - 69 := fun i => by push_cast; ring
  simp only [e1] at hs
  rw [show (2 * 70 - 1 : ℕ) = 139 from rfl] at hs
  rw [hs]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [bC, Ez]
  have hne := om_sq_sub_ne (LT := LT) k
  have hom : om LT k = iw LT k := rfl
  rw [← hom, ← sq, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hne]

theorem trigAtom_eq_iw {k : ℤ} {x : ℝ} (hx : x ∈ Icc 0 LT) :
    trigAtom LT k x = cexp (iw LT k * x) := by
  simp only [trigAtom, indicator_of_mem hx, iw]
  congr 1
  ring

/-- **The trace combination on `[0, L]`.** -/
theorem cf_sum_eq (hdet : detG hLT 70 ≠ 0) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily LT V)
    (t : ℝ) {x : ℝ} (hx : x ∈ Icc 0 LT) :
    ∑ i, cfC hLT t i * V i x =
      trigPoly LT (K 70) (cT hLT t) x - gam hLT 70 t 0 * trigPoly LT (K 70) (q hLT 0) x -
        gam hLT 70 t 1 * trigPoly LT (K 70) (q hLT 1) x +
        gam hLT 70 t 0 * uS LT (sig 0) x + gam hLT 70 t 1 * uS LT (sig 1) x := by
  show ∑ i : Fin (139 + 2), cfC hLT t i * V i x = _
  rw [Fin.sum_univ_add]
  simp only [cfC, Fin.append_left, Fin.append_right, hV.atom, hV.mom, Fin.sum_univ_two]
  rw [atom_part hLT hdet t x]
  have hu : ∀ s : Fin 2, uS LT (sig s) x = ((Real.exp (sig s * x) : ℝ) : ℂ) := fun s => by
    simp only [uS, indicator_of_mem hx]
  rw [hu 0, hu 1]
  have hp : ∀ v : ℤ → ℂ, trigPoly LT (K 70) v x = ∑ k ∈ K 70, v k * cexp (iw LT k * x) :=
    fun v => Finset.sum_congr rfl fun k _ => by rw [trigAtom_eq_iw hx]
  rw [hp, hp, hp]
  simp only [vC, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-! ### The pointwise and integrated bounds -/

theorem young_cs (a b0 b1 g0 g1 : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖a - g0 * b0 - g1 * b1‖ ^ 2 ≤
      (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ((‖g0‖ ^ 2 + ‖g1‖ ^ 2) * (‖b0‖ ^ 2 + ‖b1‖ ^ 2)) := by
  set X := ‖a‖
  set Y := ‖g0‖ * ‖b0‖ + ‖g1‖ * ‖b1‖
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := by positivity
  have h1 : ‖a - g0 * b0 - g1 * b1‖ ≤ X + Y := by
    calc ‖a - g0 * b0 - g1 * b1‖ ≤ ‖a - g0 * b0‖ + ‖g1 * b1‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖g0 * b0‖ + ‖g1 * b1‖ := by gcongr; exact norm_sub_le _ _
      _ = X + Y := by rw [norm_mul, norm_mul]; ring
  have h2 : (X + Y) ^ 2 ≤ (1 + ε) * X ^ 2 + (1 + 1 / ε) * Y ^ 2 := by
    have e : (1 + ε) * X ^ 2 + (1 + 1 / ε) * Y ^ 2 - (X + Y) ^ 2 = (ε * X - Y) ^ 2 / ε := by
      field_simp
      ring
    have : 0 ≤ (ε * X - Y) ^ 2 / ε := by positivity
    linarith
  have h3 : Y ^ 2 ≤ (‖g0‖ ^ 2 + ‖g1‖ ^ 2) * (‖b0‖ ^ 2 + ‖b1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖g0‖ * ‖b1‖ - ‖g1‖ * ‖b0‖)]
  have h4 : ‖a - g0 * b0 - g1 * b1‖ ^ 2 ≤ (X + Y) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : (1 + 1 / ε) * Y ^ 2 ≤ (1 + 1 / ε) * ((‖g0‖ ^ 2 + ‖g1‖ ^ 2) * (‖b0‖ ^ 2 + ‖b1‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

theorem sq_integrable {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    Integrable fun x => ‖w x‖ ^ 2 := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact (hw.norm.const_mul C).mono' (hw.1.norm.pow 2) (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hC x, norm_nonneg (w x)])

theorem trigPoly_zero_off {S : Finset ℤ} {v : ℤ → ℂ} {x : ℝ} (hx : x ∉ Icc 0 LT) :
    trigPoly LT S v x = 0 := by
  simp [trigPoly, trigAtom, indicator_of_notMem hx]

theorem setIntegral_eq_of_supp {g : ℝ → ℝ} (h : ∀ x, x ∉ Icc 0 LT → g x = 0) :
    ∫ x in Icc 0 LT, g x = ∫ x, g x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => h x hx

theorem diff_sq_integrable {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    Integrable fun x => ‖w x - trigPoly LT S v x‖ ^ 2 :=
  sq_integrable (hw.sub (trigPoly_integrable LT S v)) (C := C + ∑ k ∈ S, ‖v k‖) fun x =>
    (norm_sub_le _ _).trans (add_le_add (hC x) (norm_trigPoly_le LT S v x))

/-- **The trial distance of the explicit coefficients.** -/
theorem trialDist_le (hdet : detG hLT 70 ≠ 0) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily LT V)
    (hVc : ∀ i, Continuous (V i)) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    trialDist 0 LT V (cfC hLT) t ≤
      (1 + ε) * (∫ x, ‖fT LT t x - trigPoly LT (K 70) (cT hLT t) x‖ ^ 2) +
        (1 + 1 / ε) * ((‖gam hLT 70 t 0‖ ^ 2 + ‖gam hLT 70 t 1‖ ^ 2) *
          ((∫ x, ‖uS LT (sig 0) x - trigPoly LT (K 70) (q hLT 0) x‖ ^ 2) +
            ∫ x, ‖uS LT (sig 1) x - trigPoly LT (K 70) (q hLT 1) x‖ ^ 2)) := by
  set G := ‖gam hLT 70 t 0‖ ^ 2 + ‖gam hLT 70 t 1‖ ^ 2
  set A : ℝ → ℝ := fun x => ‖fT LT t x - trigPoly LT (K 70) (cT hLT t) x‖ ^ 2
  set B0 : ℝ → ℝ := fun x => ‖uS LT (sig 0) x - trigPoly LT (K 70) (q hLT 0) x‖ ^ 2
  set B1 : ℝ → ℝ := fun x => ‖uS LT (sig 1) x - trigPoly LT (K 70) (q hLT 1) x‖ ^ 2
  have iA : Integrable A := diff_sq_integrable (fT_integrable LT t) (fT_norm_le LT t) _ _
  have iB0 : Integrable B0 := diff_sq_integrable (uS_integrable LT _) (uS_norm_le LT _) _ _
  have iB1 : Integrable B1 := diff_sq_integrable (uS_integrable LT _) (uS_norm_le LT _) _ _
  have hcont : Continuous fun x => ‖cexp (↑(x * t) * I) - ∑ i, cfC hLT t i * V i x‖ ^ 2 := by
    have : Continuous fun x => ∑ i, cfC hLT t i * V i x :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (hVc i)
    fun_prop
  have hpt : ∀ x ∈ Icc 0 LT, ‖cexp (↑(x * t) * I) - ∑ i, cfC hLT t i * V i x‖ ^ 2 ≤
      (1 + ε) * A x + (1 + 1 / ε) * (G * (B0 x + B1 x)) := by
    intro x hx
    rw [cf_sum_eq hLT hdet hV t hx]
    have hf : fT LT t x = cexp (↑(x * t) * I) := by simp only [fT, indicator_of_mem hx]
    have key := young_cs (fT LT t x - trigPoly LT (K 70) (cT hLT t) x)
      (uS LT (sig 0) x - trigPoly LT (K 70) (q hLT 0) x)
      (uS LT (sig 1) x - trigPoly LT (K 70) (q hLT 1) x) (gam hLT 70 t 0) (gam hLT 70 t 1) hε
    have e : cexp (↑(x * t) * I) - (trigPoly LT (K 70) (cT hLT t) x -
        gam hLT 70 t 0 * trigPoly LT (K 70) (q hLT 0) x -
        gam hLT 70 t 1 * trigPoly LT (K 70) (q hLT 1) x +
        gam hLT 70 t 0 * uS LT (sig 0) x + gam hLT 70 t 1 * uS LT (sig 1) x) =
        fT LT t x - trigPoly LT (K 70) (cT hLT t) x -
          gam hLT 70 t 0 * (uS LT (sig 0) x - trigPoly LT (K 70) (q hLT 0) x) -
          gam hLT 70 t 1 * (uS LT (sig 1) x - trigPoly LT (K 70) (q hLT 1) x) := by
      rw [hf]
      ring
    rw [e]
    simpa only [A, B0, B1, G, mul_add] using key
  have h1 : Integrable fun x => (1 + ε) * A x := iA.const_mul _
  have h2 : Integrable fun x => (1 + 1 / ε) * (G * (B0 x + B1 x)) :=
    ((iB0.add iB1).const_mul G).const_mul _
  have hint : IntegrableOn (fun x => (1 + ε) * A x + (1 + 1 / ε) * (G * (B0 x + B1 x)))
      (Icc 0 LT) := (h1.add h2).integrableOn
  have hmono := setIntegral_mono_on hcont.integrableOn_Icc hint measurableSet_Icc hpt
  have hrhs : ∫ x in Icc 0 LT, ((1 + ε) * A x + (1 + 1 / ε) * (G * (B0 x + B1 x))) =
      (1 + ε) * (∫ x, A x) + (1 + 1 / ε) * (G * ((∫ x, B0 x) + ∫ x, B1 x)) := by
    rw [setIntegral_eq_of_supp]
    · rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_add iB0 iB1]
    · intro x hx
      have h1 : fT LT t x = 0 := by simp [fT, indicator_of_notMem hx]
      have h2 : ∀ s, uS LT s x = 0 := fun s => by simp [uS, indicator_of_notMem hx]
      simp [A, B0, B1, h1, h2, trigPoly_zero_off hx]
  calc trialDist 0 LT V (cfC hLT) t
      = ∫ x in Icc 0 LT, ‖cexp (↑(x * t) * I) - ∑ i, cfC hLT t i * V i x‖ ^ 2 := rfl
    _ ≤ _ := hmono
    _ = _ := hrhs

/-! ### Continuity in `t` -/

theorem cT_continuous (k : ℤ) : Continuous fun t => cT hLT t k := by
  have h : ∀ t, cT hLT t k = (1 / LT : ℂ) *
      ∫ x in Icc 0 LT, cexp (↑(x * t) * I) * conj (cexp (2 * Real.pi * I * k * x / LT)) := by
    intro t
    have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
    have e := coef_eq hLT (fT_support LT t) k
    have hind : (fun x => fT LT t x * conj (trigAtom LT k x)) = indicator (Icc 0 LT)
        (fun x : ℝ => cexp (↑(x * t) * I) * conj (cexp (2 * Real.pi * I * k * x / LT))) := by
      funext x
      by_cases hx : x ∈ Icc 0 LT
      · simp [fT, trigAtom, indicator_of_mem hx]
      · simp [fT, trigAtom, indicator_of_notMem hx]
    rw [hind, integral_indicator measurableSet_Icc] at e
    simp only [cT]
    rw [e]
    field_simp
  simp_rw [h]
  refine continuous_const.mul ?_
  exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc

theorem gam_continuous (s : Fin 2) : Continuous fun t => gam hLT 70 t s := by
  have hr : ∀ s', Continuous fun t => rhs hLT 70 t s' := fun s' =>
    continuous_const.mul (continuous_finsetSum _ fun k _ => (cT_continuous hLT k).mul continuous_const)
  fin_cases s
  · simp only [gam]
    exact (((continuous_const.mul (hr 0)).sub (continuous_const.mul (hr 1)))).div_const _
  · simp only [gam]
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    exact (((continuous_const.mul (hr 1)).sub (continuous_const.mul (hr 0)))).div_const _

theorem bC_continuous (k : ℤ) : Continuous fun t => bC hLT 70 t k := by
  simp only [bC, vC]
  exact (((cT_continuous hLT k).sub ((gam_continuous hLT 0).mul continuous_const)).sub
    ((gam_continuous hLT 1).mul continuous_const)).div_const _

theorem cfC_continuous (i : Fin 141) : Continuous fun t => cfC hLT t i := by
  refine Fin.addCases (m := 139) (n := 2) (fun j => ?_) (fun s => ?_) i
  · simp only [cfC, Fin.append_left, alpha, dsum]
    exact continuous_const.mul (continuous_finsetSum _ fun j' _ =>
      continuous_const.mul (bC_continuous hLT _))
  · simp only [cfC, Fin.append_right]
    exact gam_continuous hLT s

/-- **The trial distance is continuous in `t`.** -/
theorem trialDist_continuous {V : Fin 141 → ℝ → ℂ} (hVc : ∀ i, Continuous (V i)) :
    Continuous (trialDist 0 LT V (cfC hLT)) := by
  have hc : Continuous fun p : ℝ × ℝ =>
      ‖cexp (↑(p.2 * p.1) * I) - ∑ i, cfC hLT p.1 i * V i p.2‖ ^ 2 := by
    have hs : Continuous fun p : ℝ × ℝ => ∑ i, cfC hLT p.1 i * V i p.2 :=
      continuous_finsetSum _ fun i _ =>
        ((cfC_continuous hLT i).comp continuous_fst).mul ((hVc i).comp continuous_snd)
    have he : Continuous fun p : ℝ × ℝ => cexp (↑(p.2 * p.1) * I) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_snd.mul continuous_fst)).mul continuous_const)
    exact ((he.sub hs).norm).pow 2
  exact continuous_parametric_integral_of_continuous
    (f := fun t x => ‖cexp (↑(x * t) * I) - ∑ i, cfC hLT t i * V i x‖ ^ 2) hc isCompact_Icc

end AEGIS.CvSTraceDistV1

#print axioms AEGIS.CvSTraceDistV1.cf_sum_eq
#print axioms AEGIS.CvSTraceDistV1.young_cs
#print axioms AEGIS.CvSTraceDistV1.trialDist_le
#print axioms AEGIS.CvSTraceDistV1.cfC_continuous
#print axioms AEGIS.CvSTraceDistV1.trialDist_continuous
