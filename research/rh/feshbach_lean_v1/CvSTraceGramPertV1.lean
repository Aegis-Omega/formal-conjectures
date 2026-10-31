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

import CvSTraceDistV1

/-!
# The truncated Gram matrix and right-hand side as perturbations (CvS step K3e, part 1)

For `w, v` bounded and supported in `[0, L]` with `K`-truncations `P_w, P_v`:

* `pair_trunc`: `L Σ_K ŵ_k conj v̂_k = ∫ w conj v − ∫ (w − P_w) conj (v − P_v)`;
* `gram_eq`, `rhs_eq`: so `gram = Gs − Eg` and `rhs = Ys − ea` with the exact pairings
  `Gs s r = ∫ u_r conj u_s` and `Ys t s = ∫ f_t conj u_s`;
* `Eg_sq_le`, `ea_sq_le`: Cauchy–Schwarz on the truncation errors;
* `Gs_00`, `Gs_11`, `Gs_01`, `Gs_10`, `Ys_eq`: closed forms.

Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSTraceGramPertV1

open AEGIS.CvSPrimeBlockV1 AEGIS.CvSFourierIntervalV1 AEGIS.CvSMomentV1 AEGIS.CvSTraceCoefV1
open AEGIS.CvSTraceCramerV1 AEGIS.CvSTraceV1 AEGIS.CvSMassV1 AEGIS.CvSTraceDistV1

variable {LT : ℝ} (hLT : 0 < LT)

include hLT in
theorem atom_orth (n m : ℤ) :
    ∫ x, trigAtom LT n x * conj (trigAtom LT m x) = if n = m then (LT : ℂ) else 0 := by
  have := trigAtom_autocorrelation hLT le_rfl hLT.le n m
  simp only [add_zero, sub_zero] at this
  rw [this]
  split_ifs <;> simp

theorem trigPoly_support (S : Finset ℤ) (c : ℤ → ℂ) :
    Function.support (trigPoly LT S c) ⊆ Icc 0 LT := fun x hx => by
  by_contra h
  exact hx (trigPoly_zero_off h)

theorem coef_trigPoly (S : Finset ℤ) (c : ℤ → ℂ) {k : ℤ} (hk : k ∈ S) :
    fourierCoeffOn hLT (trigPoly LT S c) k = c k := by
  have e := coef_eq hLT (trigPoly_support S c) k
  have hi : ∀ j ∈ S, Integrable fun x => c j * (trigAtom LT j x * conj (trigAtom LT k x)) :=
    fun j _ => by
      have := trigAtom_mul_conj_integrable (L := LT) le_rfl j k
      simp only [add_zero] at this
      exact this.const_mul _
  have h2 : ∫ x, trigPoly LT S c x * conj (trigAtom LT k x) = c k * LT := by
    have ef : (fun x => trigPoly LT S c x * conj (trigAtom LT k x)) =
        fun x => ∑ j ∈ S, c j * (trigAtom LT j x * conj (trigAtom LT k x)) := by
      funext x
      simp only [trigPoly, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [ef, integral_finsetSum S hi]
    simp_rw [integral_const_mul, atom_orth hLT, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq', hk]
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  rw [h2] at e
  exact mul_left_cancel₀ hL0 (e.symm.trans (mul_comm _ _))

theorem int_mul_conj {F G : ℝ → ℂ} (hF : Integrable F) (hG : AEStronglyMeasurable G) {C : ℝ}
    (hC : ∀ x, ‖G x‖ ≤ C) : Integrable fun x => F x * conj (G x) := by
  have := hF.bdd_mul (c := C) (Complex.continuous_conj.comp_aestronglyMeasurable hG)
    (Filter.Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact hC x)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **Truncated pairing.** -/
theorem pair_trunc {w v : ℝ → ℂ} (hw : Integrable w) (hv : Integrable v) {Cv : ℝ}
    (hCv : ∀ x, ‖v x‖ ≤ Cv)
    (hws : Function.support w ⊆ Icc 0 LT) (hvs : Function.support v ⊆ Icc 0 LT) (S : Finset ℤ) :
    LT * ∑ k ∈ S, fourierCoeffOn hLT w k * conj (fourierCoeffOn hLT v k) =
      (∫ x, w x * conj (v x)) -
        ∫ x, (w x - trigPoly LT S (fourierCoeffOn hLT w) x) *
          conj (v x - trigPoly LT S (fourierCoeffOn hLT v) x) := by
  set Pw := trigPoly LT S (fourierCoeffOn hLT w)
  set Pv := trigPoly LT S (fourierCoeffOn hLT v)
  have iPw : Integrable Pw := trigPoly_integrable LT S _
  have iPv : Integrable Pv := trigPoly_integrable LT S _
  have bPw : ∀ x, ‖Pw x‖ ≤ ∑ k ∈ S, ‖fourierCoeffOn hLT w k‖ := norm_trigPoly_le LT S _
  have bPv : ∀ x, ‖Pv x‖ ≤ ∑ k ∈ S, ‖fourierCoeffOn hLT v k‖ := norm_trigPoly_le LT S _
  have iw' : Integrable fun x => w x - Pw x := hw.sub iPw
  have hw's : Function.support (fun x => w x - Pw x) ⊆ Icc 0 LT := fun x hx => by
    by_contra h
    have h1 : w x = 0 := Function.notMem_support.mp fun h' => h (hws h')
    have h2 : Pw x = 0 := trigPoly_zero_off h
    exact hx (by simp [h1, h2])
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  -- the truncation error of `w` is orthogonal to `P_v`
  have horth : ∫ x, (w x - Pw x) * conj (Pv x) = 0 := by
    rw [integral_mul_conj_trigPoly hLT iw' hw's]
    have hz : ∀ k ∈ S, LT * fourierCoeffOn hLT (fun x => w x - Pw x) k = 0 := fun k hk => by
      rw [← coef_eq hLT hw's k]
      have i1 := int_mul_conj (C := 1) hw (by
        have e : trigAtom LT k = Set.indicator (Icc 0 LT)
            (fun x : ℝ => cexp (2 * Real.pi * I * k * x / LT)) := rfl
        rw [e]
        exact (by fun_prop : Continuous fun x : ℝ =>
          cexp (2 * Real.pi * I * k * x / LT)).aestronglyMeasurable.indicator measurableSet_Icc)
        (norm_trigAtom_le LT k)
      have i2 := int_mul_conj (C := 1) iPw (by
        have e : trigAtom LT k = Set.indicator (Icc 0 LT)
            (fun x : ℝ => cexp (2 * Real.pi * I * k * x / LT)) := rfl
        rw [e]
        exact (by fun_prop : Continuous fun x : ℝ =>
          cexp (2 * Real.pi * I * k * x / LT)).aestronglyMeasurable.indicator measurableSet_Icc)
        (norm_trigAtom_le LT k)
      simp_rw [sub_mul]
      rw [integral_sub i1 i2, coef_eq hLT hws k, coef_eq hLT (trigPoly_support S _) k,
        coef_trigPoly hLT S _ hk, sub_self]
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [mul_left_comm, hz k hk, mul_zero]
  -- `∫ P_w conj v`
  have hPv : ∫ x, Pw x * conj (v x) =
      LT * ∑ k ∈ S, fourierCoeffOn hLT w k * conj (fourierCoeffOn hLT v k) := by
    have h := integral_mul_conj_trigPoly hLT hv hvs S (fourierCoeffOn hLT w)
    have e : (fun x => Pw x * conj (v x)) = fun x => conj (v x * conj (Pw x)) := by
      funext x
      simp [mul_comm]
    rw [e, integral_conj, h]
    simp only [map_mul, Complex.conj_ofReal, map_sum, Complex.conj_conj, mul_comm]
  have i1 : Integrable fun x => (w x - Pw x) * conj (v x) := int_mul_conj iw' hv.1 hCv
  have i2 : Integrable fun x => (w x - Pw x) * conj (Pv x) := int_mul_conj iw' iPv.1 bPv
  have i3 : Integrable fun x => w x * conj (v x) := int_mul_conj hw hv.1 hCv
  have i4 : Integrable fun x => Pw x * conj (v x) := int_mul_conj iPw hv.1 hCv
  have e1 : ∫ x, (w x - Pw x) * conj (v x - Pv x) =
      (∫ x, (w x - Pw x) * conj (v x)) - ∫ x, (w x - Pw x) * conj (Pv x) := by
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    rw [map_sub, mul_sub]
  have e2 : ∫ x, (w x - Pw x) * conj (v x) = (∫ x, w x * conj (v x)) - ∫ x, Pw x * conj (v x) := by
    rw [← integral_sub i3 i4]
    congr 1
    funext x
    ring
  rw [e1, e2, horth, hPv]
  ring

/-- **Cauchy–Schwarz** for functions supported in `[0, L]`. -/
theorem cs_supp {F G : ℝ → ℂ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    {CF CG : ℝ} (hCF : ∀ x, ‖F x‖ ≤ CF) (hCG : ∀ x, ‖G x‖ ≤ CG)
    (hFs : ∀ x, x ∉ Icc 0 LT → F x = 0) (hGs : ∀ x, x ∉ Icc 0 LT → G x = 0) :
    ‖∫ x, F x * conj (G x)‖ ^ 2 ≤ (∫ x, ‖F x‖ ^ 2) * ∫ x, ‖G x‖ ^ 2 := by
  have h := cauchy_schwarz (memLp_of_bound (lo := 0) (hi := LT) hF hCF)
    (memLp_of_bound (lo := 0) (hi := LT) hG hCG)
  have e1 : ∫ x in Icc 0 LT, F x * conj (G x) = ∫ x, F x * conj (G x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hFs x hx]
  have e2 : ∫ x in Icc 0 LT, ‖F x‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hFs x hx]
  have e3 : ∫ x in Icc 0 LT, ‖G x‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hGs x hx]
  rwa [e1, e2, e3] at h

variable (N : ℕ)

/-- The truncation error of the moment function `u_s`. -/
def du (s : Fin 2) (x : ℝ) : ℂ := uS LT (sig s) x - trigPoly LT (K N) (q hLT s) x

/-- The truncation error of `f_t`. -/
def dfT (t x : ℝ) : ℂ := fT LT t x - trigPoly LT (K N) (cT hLT t) x

def Gs (s r : Fin 2) : ℂ := ∫ x, uS LT (sig r) x * conj (uS LT (sig s) x)

def Ys (t : ℝ) (s : Fin 2) : ℂ := ∫ x, fT LT t x * conj (uS LT (sig s) x)

def Eg (s r : Fin 2) : ℂ := ∫ x, du hLT N r x * conj (du hLT N s x)

def ea (t : ℝ) (s : Fin 2) : ℂ := ∫ x, dfT hLT N t x * conj (du hLT N s x)

theorem gram_eq (s r : Fin 2) : gram hLT N s r = Gs (LT := LT) s r - Eg hLT N s r := by
  have h := pair_trunc hLT (uS_integrable LT (sig r)) (uS_integrable LT (sig s))
    (uS_norm_le LT _) (uS_support LT _) (uS_support LT _) (K N)
  exact h

theorem rhs_eq (t : ℝ) (s : Fin 2) : rhs hLT N t s = Ys (LT := LT) t s - ea hLT N t s := by
  have h := pair_trunc hLT (fT_integrable LT t) (uS_integrable LT (sig s))
    (uS_norm_le LT _) (fT_support LT t) (uS_support LT _) (K N)
  exact h

theorem du_off (s : Fin 2) {x : ℝ} (hx : x ∉ Icc 0 LT) : du hLT N s x = 0 := by
  simp [du, uS, indicator_of_notMem hx, trigPoly_zero_off hx]

theorem dfT_off (t : ℝ) {x : ℝ} (hx : x ∉ Icc 0 LT) : dfT hLT N t x = 0 := by
  simp [dfT, fT, indicator_of_notMem hx, trigPoly_zero_off hx]

theorem du_bound (s : Fin 2) (x : ℝ) :
    ‖du hLT N s x‖ ≤ Real.exp (|sig s| * LT) + ∑ k ∈ K N, ‖q hLT s k‖ :=
  (norm_sub_le _ _).trans (add_le_add (uS_norm_le LT _ x) (norm_trigPoly_le LT _ _ x))

theorem dfT_bound (t x : ℝ) : ‖dfT hLT N t x‖ ≤ 1 + ∑ k ∈ K N, ‖cT hLT t k‖ :=
  (norm_sub_le _ _).trans (add_le_add (fT_norm_le LT t x) (norm_trigPoly_le LT _ _ x))

theorem Eg_sq_le (s r : Fin 2) :
    ‖Eg hLT N s r‖ ^ 2 ≤ (∫ x, ‖du hLT N r x‖ ^ 2) * ∫ x, ‖du hLT N s x‖ ^ 2 :=
  cs_supp ((uS_integrable LT _).sub (trigPoly_integrable LT _ _)).1
    ((uS_integrable LT _).sub (trigPoly_integrable LT _ _)).1 (du_bound hLT N r) (du_bound hLT N s)
    (fun _ hx => du_off hLT N r hx) (fun _ hx => du_off hLT N s hx)

theorem ea_sq_le (t : ℝ) (s : Fin 2) :
    ‖ea hLT N t s‖ ^ 2 ≤ (∫ x, ‖dfT hLT N t x‖ ^ 2) * ∫ x, ‖du hLT N s x‖ ^ 2 :=
  cs_supp ((fT_integrable LT t).sub (trigPoly_integrable LT _ _)).1
    ((uS_integrable LT _).sub (trigPoly_integrable LT _ _)).1 (dfT_bound hLT N t) (du_bound hLT N s)
    (fun _ hx => dfT_off hLT N t hx) (fun _ hx => du_off hLT N s hx)

/-! ### Closed forms of the exact pairings -/

include hLT in
theorem integral_cexp {c : ℂ} (hc : c ≠ 0) :
    ∫ x, indicator (Icc 0 LT) (fun x : ℝ => cexp (c * x)) x = (cexp (c * LT) - 1) / c := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hLT.le, integral_exp_mul_complex hc]
  simp

theorem uu_eq (s r : Fin 2) (x : ℝ) : uS LT (sig r) x * conj (uS LT (sig s) x) =
    indicator (Icc 0 LT) (fun x : ℝ => cexp (((sig r + sig s : ℝ) : ℂ) * x)) x := by
  by_cases hx : x ∈ Icc 0 LT
  · simp only [uS, indicator_of_mem hx]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
    push_cast
    ring_nf
  · simp [uS, indicator_of_notMem hx]

include hLT in
theorem Gs_00 : Gs (LT := LT) 0 0 = 1 - Real.exp (-LT) := by
  have h : ((sig 0 + sig 0 : ℝ) : ℂ) = -1 := by norm_num [sig]
  simp only [Gs, uu_eq, h]
  rw [integral_cexp hLT (by norm_num)]
  push_cast
  field_simp
  ring_nf

include hLT in
theorem Gs_11 : Gs (LT := LT) 1 1 = Real.exp LT - 1 := by
  have h : ((sig 1 + sig 1 : ℝ) : ℂ) = 1 := by norm_num [sig]
  simp only [Gs, uu_eq, h]
  rw [integral_cexp hLT (by norm_num)]
  push_cast
  simp

include hLT in
theorem Gs_off {s r : Fin 2} (h : sig r + sig s = 0) : Gs (LT := LT) s r = LT := by
  simp only [Gs, uu_eq, h, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le hLT.le]
  simp

include hLT in
theorem Gs_01 : Gs (LT := LT) 0 1 = LT := Gs_off hLT (by norm_num [sig])

include hLT in
theorem Gs_10 : Gs (LT := LT) 1 0 = LT := Gs_off hLT (by norm_num [sig])

include hLT in
theorem Ys_eq (t : ℝ) (s : Fin 2) :
    Ys (LT := LT) t s = (cexp (((t : ℂ) * I + sig s) * LT) - 1) / ((t : ℂ) * I + sig s) := by
  have hne : (t : ℂ) * I + sig s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact sig_ne_zero s this
  have e : (fun x => fT LT t x * conj (uS LT (sig s) x)) =
      indicator (Icc 0 LT) (fun x : ℝ => cexp (((t : ℂ) * I + sig s) * x)) := by
    funext x
    by_cases hx : x ∈ Icc 0 LT
    · simp only [fT, uS, indicator_of_mem hx]
      rw [Complex.conj_ofReal, Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf
    · simp [fT, uS, indicator_of_notMem hx]
  simp only [Ys]
  rw [e, integral_cexp hLT hne]

end AEGIS.CvSTraceGramPertV1

#print axioms AEGIS.CvSTraceGramPertV1.coef_trigPoly
#print axioms AEGIS.CvSTraceGramPertV1.pair_trunc
#print axioms AEGIS.CvSTraceGramPertV1.cs_supp
#print axioms AEGIS.CvSTraceGramPertV1.gram_eq
#print axioms AEGIS.CvSTraceGramPertV1.rhs_eq
#print axioms AEGIS.CvSTraceGramPertV1.Eg_sq_le
#print axioms AEGIS.CvSTraceGramPertV1.ea_sq_le
#print axioms AEGIS.CvSTraceGramPertV1.Gs_00
#print axioms AEGIS.CvSTraceGramPertV1.Gs_11
#print axioms AEGIS.CvSTraceGramPertV1.Gs_01
#print axioms AEGIS.CvSTraceGramPertV1.Ys_eq
