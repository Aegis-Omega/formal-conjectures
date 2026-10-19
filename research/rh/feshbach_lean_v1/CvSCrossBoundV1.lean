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
import CvSCrossMatrixV1

/-!
# Growth of the symbol and continuity of the cross term (CvS step 6g, ring tree)

Interpolating `|a_k(r)| ≤ 5/(k+1)` and `|a_k(r)| ≤ (3 + 16r²)/(k+1)²` for the digamma series terms
gives `|a_k(r)| ≤ 5^{7/8} (3 + 16r²)^{1/8} / (k+1)^{9/8}`, hence `|h₊(r)| ≤ C (1 + r²)^{1/8}`
(`hplus_abs_le`) and `|ScertM M t| ≤ C (1 + t²)^{1/8}` (`scertM_abs_le`). For `E ≥ 0` with
`|E| ≤ M₀` and `|t² E| ≤ M₂`, `ScertM² E` is integrable (`scertM_sq_mul_integrable`), and
Cauchy–Schwarz gives the continuity of the cross term in its second argument:

  `(∫ ScertM · Re(𝓕v conj 𝓕d)(t/2π))² ≤ (∫ ScertM² E(v)) · ∫ E(d)`   (`cross_sq_le`).

Not RH.
-/

open MeasureTheory Complex Set Filter
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace AEGIS.CvSCrossBoundV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1
open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSQuadV1 AEGIS.CvSRingBridgeV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem archTerm_abs_le_five (k : ℕ) (r : ℝ) : |archTerm k r| ≤ 5 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : 0 < archWidth k := archWidth_pos k
  have h1 : 0 ≤ 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) := by positivity
  have h2 : 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) ≤ 4 / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold archWidth
    nlinarith [sq_nonneg r, sq_nonneg (k : ℝ)]
  have h3 : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have h4 : (5 : ℝ) / (k + 1) = 1 / (k + 1) + 4 / (k + 1) := by ring
  unfold archTerm
  rw [abs_le]
  constructor <;> linarith

theorem archTerm_abs_le_interp (k : ℕ) (r : ℝ) :
    |archTerm k r| ≤ (5 : ℝ) ^ (7 / 8 : ℝ) * (3 + 16 * r ^ 2) ^ (1 / 8 : ℝ) *
      (1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ)) := by
  set x := |archTerm k r|
  have hx : 0 ≤ x := abs_nonneg _
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hA : x ≤ 5 / ((k : ℝ) + 1) := archTerm_abs_le_five k r
  have hB : x ≤ (3 + 16 * r ^ 2) / ((k : ℝ) + 1) ^ 2 := archTerm_abs_le k r
  have hsplit : x = x ^ (7 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add' hx (by norm_num)]
    norm_num
  have hp : (((k : ℝ) + 1) ^ 2) ^ (1 / 8 : ℝ) = ((k : ℝ) + 1) ^ (2 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk1.le]
    norm_num
  have hq : ((k : ℝ) + 1) ^ (9 / 8 : ℝ) =
      ((k : ℝ) + 1) ^ (7 / 8 : ℝ) * ((k : ℝ) + 1) ^ (2 / 8 : ℝ) := by
    rw [← Real.rpow_add hk1]
    norm_num
  calc x = x ^ (7 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := hsplit
    _ ≤ (5 / ((k : ℝ) + 1)) ^ (7 / 8 : ℝ) * ((3 + 16 * r ^ 2) / ((k : ℝ) + 1) ^ 2) ^ (1 / 8 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow hx hA (by norm_num)) (Real.rpow_le_rpow hx hB (by norm_num))
        (by positivity) (by positivity)
    _ = _ := by
      rw [Real.div_rpow (by norm_num) hk1.le, Real.div_rpow (by positivity) (by positivity), hp, hq]
      field_simp

theorem summable_inv_rpow : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 9 / 8))
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- **Growth of `h₊`.** -/
theorem hplus_abs_le : ∃ C, ∀ r : ℝ, |hplus r| ≤ C * (1 + r ^ 2) ^ (1 / 8 : ℝ) := by
  set Z := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ)
  set c0 := |Real.eulerMascheroniConstant + Real.log Real.pi|
  have hZ : 0 ≤ Z := tsum_nonneg fun k => by positivity
  refine ⟨(5 : ℝ) ^ (7 / 8 : ℝ) * 16 ^ (1 / 8 : ℝ) * Z + c0, fun r => ?_⟩
  have hone : 1 ≤ (1 + r ^ 2) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg r]) (by norm_num)
  set K := (5 : ℝ) ^ (7 / 8 : ℝ) * (3 + 16 * r ^ 2) ^ (1 / 8 : ℝ)
  have hs : Summable fun k : ℕ => K * (1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ)) :=
    summable_inv_rpow.mul_left K
  have hterm : ∀ k : ℕ, ‖archTerm k r‖ ≤ K * (1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ)) := fun k => by
    rw [Real.norm_eq_abs]
    exact archTerm_abs_le_interp k r
  have hsn : Summable fun k : ℕ => ‖archTerm k r‖ :=
    hs.of_nonneg_of_le (fun k => norm_nonneg _) hterm
  have hsum : |∑' k, archTerm k r| ≤ K * Z := by
    rw [← Real.norm_eq_abs]
    calc ‖∑' k, archTerm k r‖ ≤ ∑' k, ‖archTerm k r‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k : ℕ, K * (1 / ((k : ℝ) + 1) ^ (9 / 8 : ℝ)) := hsn.tsum_le_tsum hterm hs
      _ = K * Z := tsum_mul_left
  have h3 : (3 + 16 * r ^ 2) ^ (1 / 8 : ℝ) ≤ 16 ^ (1 / 8 : ℝ) * (1 + r ^ 2) ^ (1 / 8 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
  have h5 : 0 ≤ (5 : ℝ) ^ (7 / 8 : ℝ) := by positivity
  rw [hplus_eq_tsum]
  calc |(∑' k, archTerm k r) - (Real.eulerMascheroniConstant + Real.log Real.pi)|
      ≤ |∑' k, archTerm k r| + c0 := abs_sub _ _
    _ ≤ K * Z + c0 * (1 + r ^ 2) ^ (1 / 8 : ℝ) :=
      add_le_add hsum (le_mul_of_one_le_right (abs_nonneg _) hone)
    _ ≤ (5 : ℝ) ^ (7 / 8 : ℝ) * (16 ^ (1 / 8 : ℝ) * (1 + r ^ 2) ^ (1 / 8 : ℝ)) * Z +
        c0 * (1 + r ^ 2) ^ (1 / 8 : ℝ) := by
      gcongr
      exact mul_le_mul_of_nonneg_left h3 h5
    _ = ((5 : ℝ) ^ (7 / 8 : ℝ) * 16 ^ (1 / 8 : ℝ) * Z + c0) * (1 + r ^ 2) ^ (1 / 8 : ℝ) := by ring

/-- **Growth of the symbol.** -/
theorem scertM_abs_le (M : ℕ) : ∃ C, ∀ t : ℝ, |ScertM M t| ≤ C * (1 + t ^ 2) ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC⟩ := hplus_abs_le
  set P := ∑ j ∈ Finset.range M, |ppw j|
  refine ⟨C + P, fun t => ?_⟩
  have hone : 1 ≤ (1 + t ^ 2) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg t]) (by norm_num)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hP : |∑ j ∈ Finset.range M, ppw j * Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ))| ≤ P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [scertM_eq_qsym]
  unfold qsym
  calc |hplus t - ∑ j ∈ Finset.range M, ppw j * Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ))|
      ≤ |hplus t| + |∑ j ∈ Finset.range M, ppw j * Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ))| :=
        abs_sub _ _
    _ ≤ C * (1 + t ^ 2) ^ (1 / 8 : ℝ) + P * (1 + t ^ 2) ^ (1 / 8 : ℝ) :=
      add_le_add (hC t) (hP.trans (le_mul_of_one_le_right hP0 hone))
    _ = (C + P) * (1 + t ^ 2) ^ (1 / 8 : ℝ) := by ring

theorem scertM_sq_mul_integrable (M : ℕ) {E : ℝ → ℝ} (hE : Continuous E) (hE0 : ∀ t, 0 ≤ E t)
    {M0 M2 : ℝ} (h0 : ∀ t, |E t| ≤ M0) (h2 : ∀ t, |t ^ 2 * E t| ≤ M2) :
    Integrable fun t => ScertM M t ^ 2 * E t := by
  obtain ⟨C, hC⟩ := scertM_abs_le M
  have hI : Integrable fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; norm_num)
  refine (hI.const_mul (C ^ 2 * (M0 + M2))).mono'
    (((scertM_measurable M).pow_const 2).mul hE.measurable).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hS2 : ScertM M t ^ 2 ≤ C ^ 2 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← sq_abs]
    calc |ScertM M t| ^ 2 ≤ (C * (1 + t ^ 2) ^ (1 / 8 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hC t) 2
      _ = C ^ 2 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + t ^ 2) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul ht.le]
          norm_num
  have hEb : E t ≤ (M0 + M2) / (1 + t ^ 2) := by
    rw [le_div_iff₀ ht]
    have a := (le_abs_self _).trans (h0 t)
    have b := (le_abs_self _).trans (h2 t)
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hE0 t)), Real.norm_eq_abs,
    sq_abs]
  calc ScertM M t ^ 2 * E t ≤ C ^ 2 * (1 + t ^ 2) ^ (1 / 4 : ℝ) * ((M0 + M2) / (1 + t ^ 2)) :=
        mul_le_mul hS2 hEb (hE0 t) (by positivity)
    _ = C ^ 2 * (M0 + M2) * (1 + t ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
        rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub ht, Real.rpow_one]
        ring

/-- `ScertM² E(v_c)` is integrable for a low block over a C¹ basis. -/
theorem lowBlock_scertM_sq_integrable (M : ℕ) {p : ℕ} {LT : ℝ} (hLT : 0 ≤ LT)
    {U : Fin p → ℝ → ℂ} (hU : ∀ i, ContDiff ℝ 1 (U i)) (c : Fin p → ℂ) :
    Integrable fun t => ScertM M t ^ 2 * energy (lowBlock LT U c) t := by
  obtain ⟨M0, M2, h0, h2⟩ := lowBlock_energy_bounds hLT hU c
  exact scertM_sq_mul_integrable M
    (energy_continuous (lowBlock_integrable (fun i => (hU i).continuous) c))
    (fun t => Complex.normSq_nonneg _) h0 h2

/-- **Continuity of the cross term** (Cauchy–Schwarz in `L²(dt)`). -/
theorem cross_sq_le (M : ℕ) {v d : ℝ → ℂ} (hv : Integrable v) (hd : Integrable d)
    (hSv : Integrable fun t => ScertM M t ^ 2 * energy v t) (hEd : Integrable (energy d)) :
    (∫ t, ScertM M t * cross v d t) ^ 2 ≤ (∫ t, ScertM M t ^ 2 * energy v t) * ∫ t, energy d t := by
  set f : ℝ → ℂ := fun t => (ScertM M t : ℂ) * 𝓕 v (t / (2 * Real.pi)) with hf
  set g : ℝ → ℂ := fun t => 𝓕 d (t / (2 * Real.pi)) with hg
  have hFv : Continuous fun t : ℝ => 𝓕 v (t / (2 * Real.pi)) :=
    (fourier_continuous hv).comp (continuous_id.div_const _)
  have hFd : Continuous g := (fourier_continuous hd).comp (continuous_id.div_const _)
  have hfm : AEStronglyMeasurable f :=
    ((Complex.measurable_ofReal.comp (scertM_measurable M)).mul hFv.measurable).aestronglyMeasurable
  have hnf : ∀ t, ‖f t‖ ^ 2 = ScertM M t ^ 2 * energy v t := fun t => by
    simp only [hf, energy, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Complex.normSq_eq_norm_sq]
  have hng : ∀ t, ‖g t‖ ^ 2 = energy d t := fun t => by
    simp only [hg, energy, Complex.normSq_eq_norm_sq]
  have hf2 : MemLp f 2 := (memLp_two_iff_integrable_sq_norm hfm).2 (by simp_rw [hnf]; exact hSv)
  have hg2 : MemLp g 2 :=
    (memLp_two_iff_integrable_sq_norm hFd.aestronglyMeasurable).2 (by simp_rw [hng]; exact hEd)
  have hcs := cauchy_schwarz hf2 hg2
  simp_rw [hnf, hng] at hcs
  have hint : Integrable fun t => f t * conj (g t) := by
    refine ((hSv.add hEd).div_const 2).mono'
      (hfm.mul (Complex.continuous_conj.comp hFd).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_conj]
    have e1 := hnf t
    have e2 := hng t
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖f t‖ - ‖g t‖)]
  have hre : ∫ t, ScertM M t * cross v d t = (∫ t, f t * conj (g t)).re := by
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [← hr]
    congr 1
    funext t
    simp only [hf, hg, cross]
    rw [mul_assoc, Complex.re_ofReal_mul]
  rw [hre]
  calc (∫ t, f t * conj (g t)).re ^ 2 ≤ ‖∫ t, f t * conj (g t)‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    _ ≤ _ := hcs

end AEGIS.CvSCrossBoundV1

#print axioms AEGIS.CvSCrossBoundV1.archTerm_abs_le_interp
#print axioms AEGIS.CvSCrossBoundV1.hplus_abs_le
#print axioms AEGIS.CvSCrossBoundV1.scertM_abs_le
#print axioms AEGIS.CvSCrossBoundV1.scertM_sq_mul_integrable
#print axioms AEGIS.CvSCrossBoundV1.lowBlock_scertM_sq_integrable
#print axioms AEGIS.CvSCrossBoundV1.cross_sq_le
