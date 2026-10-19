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
import CvSFourierIntervalV1

/-!
# The cross bound from the rows of the CvS matrix (CvS step 6i, ring tree)

For the low block `v_c = trigPoly L_T F a_c` and a complement `w`, let `ŵ` be the Fourier
coefficients of `w` on `[0, L_T]` and `y_m = π Σ_{n∈F} a_c(n) (E_nm + E_mn)`, `E = cvsEntry M L_T`
(`crossRow`). Then

* `cross_trigPoly_row`: `X(v, Σ_{m∈G} b_m e_m) = Re Σ_{m∈G} conj(b_m) y_m`;
* `tendsto_cross_partialSum`: `X(v, S_N w) → X(v, w)` (`CvSCrossBoundV1.cross_sq_le` and
  `CvSFourierIntervalV1.tendsto_partialSum`);
* `atom_orth`: orthogonality of `w` to the atoms is `Σ_m conj(ŵ_m) u_i(m) = 0`;
* `cross_sq_le_of_rows`: if `Σ_{|m|≤N} |y_m − Σ_i λ_i u_i(m)|² ≤ B` for every `N`, then
  `X(v_c, w)² ≤ B/(2π L_T) · ∫ E(w)` for every admissible `w` (Bessel and Cauchy–Schwarz).

`window_of_certificate_rows` is `window_of_certificate_matrix` with the cross hypothesis replaced
by this bound on the rows. Not RH.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate FourierTransform ContDiff

noncomputable section

namespace AEGIS.CvSCrossCertV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSCrossMatrixV1 AEGIS.CvSCrossBoundV1
open AEGIS.CvSFourierIntervalV1 AEGIS.CvSPrimeBlockV1 AEGIS.CvSMassV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem cross_sub {v w g : ℝ → ℂ} (hw : Integrable w) (hg : Integrable g) (t : ℝ) :
    cross v (fun x => w x - g x) t = cross v w t - cross v g t := by
  have h := fourier_lin w g hw hg 1 (t / (2 * Real.pi))
  have e : (fun u => w u - (1 : ℂ) * g u) = fun u => w u - g u := by funext u; ring
  rw [e, one_mul] at h
  simp only [cross]
  rw [h, map_sub, mul_sub, Complex.sub_re]

theorem scertM_cross_integrable (M : ℕ) {v w : ℝ → ℂ} (hv : Integrable v) (hw : Integrable w)
    (hSv : Integrable fun t => ScertM M t ^ 2 * energy v t) (hEw : Integrable (energy w)) :
    Integrable fun t => ScertM M t * cross v w t := by
  refine ((hSv.add hEw).div_const 2).mono'
    ((scertM_measurable M).aestronglyMeasurable.mul (cross_continuous hv hw).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  set a := 𝓕 v (t / (2 * Real.pi))
  set b := 𝓕 w (t / (2 * Real.pi))
  have hc : |cross v w t| ≤ ‖a‖ * ‖b‖ := by
    calc |cross v w t| = |(a * conj b).re| := rfl
      _ ≤ ‖a * conj b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
  have hEv : energy v t = ‖a‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hEw' : energy w t = ‖b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
  rw [hEv, hEw']
  have hS := abs_nonneg (ScertM M t)
  have h1 : |ScertM M t| * |cross v w t| ≤ |ScertM M t| * (‖a‖ * ‖b‖) :=
    mul_le_mul_of_nonneg_left hc hS
  have hsq : ScertM M t ^ 2 = |ScertM M t| ^ 2 := (sq_abs _).symm
  rw [hsq]
  nlinarith [sq_nonneg (|ScertM M t| * ‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem trigPoly_energy_integrable {LT : ℝ} (hLT : 0 ≤ LT) (H : Finset ℤ) (a : ℤ → ℂ) :
    Integrable (energy (trigPoly LT H a)) := by
  rw [trigPoly_eq_lowBlock]
  exact lowBlock_energy_integrable hLT (fun j =>
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)) _

/-- **The cross term along the Fourier partial sums.** -/
theorem tendsto_cross_partialSum (M : ℕ) {LT : ℝ} (hLT : 0 < LT) {v w : ℝ → ℂ}
    (hv : Integrable v) (hSv : Integrable fun t => ScertM M t ^ 2 * energy v t)
    (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) (hs : Function.support w ⊆ Icc 0 LT)
    (hEw : Integrable (energy w)) :
    Tendsto (fun N : ℕ => ∫ t, ScertM M t * cross v (partialSum hLT w N) t) atTop
      (𝓝 (∫ t, ScertM M t * cross v w t)) := by
  set A := ∫ t, ScertM M t ^ 2 * energy v t
  have hA : 0 ≤ A := integral_nonneg fun t => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hg : ∀ N, Integrable (partialSum hLT w N) := fun N => trigPoly_integrable LT _ _
  have hEg : ∀ N, Integrable (energy (partialSum hLT w N)) := fun N =>
    trigPoly_energy_integrable hLT.le _ _
  set d : ℕ → ℝ → ℂ := fun N x => w x - partialSum hLT w N x with hd
  have hdi : ∀ N, Integrable (d N) := fun N => hw.sub (hg N)
  have hEd : ∀ N, Integrable (energy (d N)) := fun N => by
    refine ((hEw.const_mul 2).add ((hEg N).const_mul 2)).mono'
      (energy_continuous (hdi N)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    show ‖energy (d N) t‖ ≤ 2 * energy w t + 2 * energy (partialSum hLT w N) t
    rw [Real.norm_of_nonneg (show 0 ≤ energy (d N) t from Complex.normSq_nonneg _)]
    exact energy_sub_le hw (hg N) t
  have hdC : ∀ N, ∀ x, ‖d N x‖ ≤ C + ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖fourierCoeffOn hLT w k‖ :=
    fun N x => (norm_sub_le _ _).trans (add_le_add (hC x) (norm_trigPoly_le LT _ _ x))
  have hX : ∀ N, (∫ t, ScertM M t * cross v (d N) t) ^ 2 ≤
      A * (2 * Real.pi * ∫ x, ‖d N x‖ ^ 2) := fun N => by
    have h1 := cross_sq_le M hv (hdi N) hSv (hEd N)
    rw [energy_eq_two_pi_L2 (hdi N) (hdC N) (hEd N)] at h1
    simp_rw [Complex.normSq_eq_norm_sq] at h1
    exact h1
  have hsplit : ∀ N, ∫ t, ScertM M t * cross v (partialSum hLT w N) t =
      (∫ t, ScertM M t * cross v w t) - ∫ t, ScertM M t * cross v (d N) t := fun N => by
    have e : (fun t => ScertM M t * cross v (d N) t) = fun t =>
        ScertM M t * cross v w t - ScertM M t * cross v (partialSum hLT w N) t := by
      funext t
      rw [hd, cross_sub hw (hg N), mul_sub]
    rw [e, integral_sub (scertM_cross_integrable M hv hw hSv hEw)
      (scertM_cross_integrable M hv (hg N) hSv (hEg N))]
    ring
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (A * (2 * Real.pi * ∫ x, ‖d N x‖ ^ 2))) atTop
      (𝓝 0) := by
    have h0 := tendsto_partialSum hLT hw hC hs
    have h1 := ((h0.const_mul (2 * Real.pi)).const_mul A).sqrt
    simpa using h1
  have hsmall : Tendsto (fun N : ℕ => ∫ t, ScertM M t * cross v (d N) t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hX N)
  have h := hsmall.const_sub (∫ t, ScertM M t * cross v w t)
  rw [sub_zero] at h
  exact h.congr fun N => (hsplit N).symm

/-- The row of the cross block: `y_m = π Σ_{n∈F} a_n (E_nm + E_mn)`. -/
def crossRow (M : ℕ) (L : ℝ) (F : Finset ℤ) (a : ℤ → ℂ) (m : ℤ) : ℂ :=
  Real.pi * ∑ n ∈ F, a n * ((cvsEntry M L n m : ℂ) + (cvsEntry M L m n : ℂ))

theorem trigPoly_restrict (L : ℝ) {F H : Finset ℤ} (hFH : F ⊆ H) (a : ℤ → ℂ) :
    trigPoly L F a = trigPoly L H (fun k => if k ∈ F then a k else 0) := by
  funext x
  simp only [trigPoly, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFH]

/-- **The cross term of two trigonometric polynomials as a row pairing.** -/
theorem cross_trigPoly_row (M : ℕ) {L : ℝ} (hL : 0 < L) (F G : Finset ℤ) (a b : ℤ → ℂ) :
    ∫ t, ScertM M t * cross (trigPoly L F a) (trigPoly L G b) t =
      (∑ m ∈ G, conj (b m) * crossRow M L F a m).re := by
  set H := F ∪ G
  set a' : ℤ → ℂ := fun k => if k ∈ F then a k else 0
  set b' : ℤ → ℂ := fun k => if k ∈ G then b k else 0
  rw [trigPoly_restrict L Finset.subset_union_left a,
    trigPoly_restrict L Finset.subset_union_right b,
    cross_trigPoly M hL H a' b']
  set E : ℤ → ℤ → ℂ := fun n m => (cvsEntry M L n m : ℂ)
  have hE : ∀ n m, conj (E n m) = E n m := fun n m => Complex.conj_ofReal _
  have hsplit : ∑ n ∈ H, ∑ m ∈ H, (a' n * conj (b' m) + b' n * conj (a' m)) * E n m =
      (∑ n ∈ H, ∑ m ∈ H, a' n * conj (b' m) * E n m) +
        ∑ n ∈ H, ∑ m ∈ H, b' n * conj (a' m) * E n m := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [← Finset.sum_add_distrib]; simp only [add_mul]
  have hconj : (∑ n ∈ H, ∑ m ∈ H, b' n * conj (a' m) * E n m).re =
      (∑ m ∈ H, ∑ n ∈ H, conj (b' m) * a' n * E m n).re := by
    rw [← Complex.conj_re]
    simp only [map_sum, map_mul, Complex.conj_conj, hE]
  have hrowH : ∀ m, crossRow M L H a' m = crossRow M L F a m := fun m => by
    simp only [crossRow, a', ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  have hG : (∑ m ∈ H, conj (b' m) * crossRow M L H a' m) =
      ∑ m ∈ G, conj (b m) * crossRow M L F a m := by
    simp only [hrowH, b', apply_ite conj, map_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
  have htot : (∑ m ∈ H, conj (b' m) * crossRow M L H a' m) = (Real.pi : ℂ) *
      ((∑ n ∈ H, ∑ m ∈ H, a' n * conj (b' m) * E n m) +
        ∑ m ∈ H, ∑ n ∈ H, conj (b' m) * a' n * E m n) := by
    rw [Finset.sum_comm (f := fun n m => a' n * conj (b' m) * E n m), ← Finset.sum_add_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [crossRow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [E]
    ring
  rw [hsplit, Complex.add_re, hconj, ← Complex.add_re, ← hG, htot, Complex.re_ofReal_mul]

/-- The coefficients of the atom `U_i` in the basis `e_k`. -/
def atomRow {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ) (i : Fin p) (k : ℤ) : ℂ :=
  lowCoeff L S β (Pi.single i 1) k

theorem lowCoeff_eq_zero {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ)
    (c : Fin p → ℂ) {k : ℤ} (hk : k ∉ lowFreq S) : lowCoeff L S β c k = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have : k ∉ S i := fun h => hk (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  simp [this]

theorem indicator_atom {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ) (i : Fin p) :
    Set.indicator (Icc 0 L) (basisFun L (S i) (β i)) =
      trigPoly L (lowFreq S) (atomRow L S β i) := by
  show _ = trigPoly L (lowFreq S) (lowCoeff L S β (Pi.single i 1))
  rw [← lowBlock_eq_trigPoly]
  funext x
  simp only [lowBlock, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- **Orthogonality to the atoms in Fourier coefficients.** -/
theorem atom_orth {p : ℕ} {LT : ℝ} (hLT : 0 < LT) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ)
    {w : ℝ → ℂ} (hw : Integrable w) (hs : Function.support w ⊆ Icc 0 LT) (i : Fin p)
    (horth : ∫ x in Icc 0 LT, w x * conj (basisFun LT (S i) (β i) x) = 0) :
    ∑ m ∈ lowFreq S, conj (fourierCoeffOn hLT w m) * atomRow LT S β i m = 0 := by
  have e : (∫ x in Icc 0 LT, w x * conj (basisFun LT (S i) (β i) x)) =
      ∫ x, w x * conj (trigPoly LT (lowFreq S) (atomRow LT S β i) x) := by
    rw [← indicator_atom, ← integral_indicator measurableSet_Icc]
    congr 1
    funext x
    by_cases hx : x ∈ Icc 0 LT
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  rw [e, integral_mul_conj_trigPoly hLT hw hs] at horth
  have hLT0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have h0 : ∑ k ∈ lowFreq S, conj (atomRow LT S β i k) * fourierCoeffOn hLT w k = 0 :=
    (mul_eq_zero.mp horth).resolve_left hLT0
  have h1 := congrArg conj h0
  rw [map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem exists_Icc_superset (F : Finset ℤ) : ∃ N0 : ℕ, F ⊆ Finset.Icc (-(N0 : ℤ)) N0 := by
  refine ⟨F.sup Int.natAbs, fun k hk => ?_⟩
  have h1 : k.natAbs ≤ F.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hk
  have h2 : ((k.natAbs : ℕ) : ℤ) ≤ ((F.sup Int.natAbs : ℕ) : ℤ) := by exact_mod_cast h1
  rw [Int.natCast_natAbs] at h2
  rw [Finset.mem_Icc]
  constructor <;> linarith [neg_abs_le k, le_abs_self k]

/-- **The cross bound from the rows.** If the rows `y_m` of the cross block, corrected by any
combination `Σ λ_i u_i` of the atom rows, have `Σ_{|m|≤N} |y_m − Σ λ_i u_i(m)|² ≤ B` for all `N`,
then `X(v_c, w)² ≤ B/(2π L_T) · ∫ E(w)` for every admissible complement `w`. -/
theorem cross_sq_le_of_rows (M : ℕ) {LT : ℝ} (hLT : 0 < LT) {p : ℕ} (S : Fin p → Finset ℤ)
    (β : Fin p → ℤ → ℂ) (c lam : Fin p → ℂ) (B : ℝ)
    (hB : ∀ N : ℕ, ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      ‖crossRow M LT (lowFreq S) (lowCoeff LT S β c) m - ∑ i, lam i * atomRow LT S β i m‖ ^ 2 ≤ B)
    {w : ℝ → ℂ} (hw : Admissible LT (fun i => basisFun LT (S i) (β i)) w) :
    (∫ t, ScertM M t * cross (lowBlock LT (fun i => basisFun LT (S i) (β i)) c) w t) ^ 2 ≤
      B / (2 * Real.pi * LT) * ∫ t, energy w t := by
  obtain ⟨hwi, ⟨C, hC⟩, hs, _, horth, hEw⟩ := hw
  have hU1 : ∀ i, ContDiff ℝ 1 (basisFun LT (S i) (β i)) := fun i =>
    (basisFun_contDiff _ _ _).of_le (by norm_cast)
  set v := lowBlock LT (fun i => basisFun LT (S i) (β i)) c
  have hvi : Integrable v := lowBlock_integrable (fun i => (hU1 i).continuous) c
  have hSv := lowBlock_scertM_sq_integrable M hLT.le hU1 c
  have hlim := (tendsto_cross_partialSum M hLT hvi hSv hwi hC hs hEw).pow 2
  set F := lowFreq S
  set a := lowCoeff LT S β c
  set y := crossRow M LT F a
  set z : ℤ → ℂ := fun m => ∑ i, lam i * atomRow LT S β i m
  set W := LT⁻¹ * ∫ x, ‖w x‖ ^ 2
  obtain ⟨N0, hN0⟩ := exists_Icc_superset F
  have hbound : ∀ N ≥ N0,
      (∫ t, ScertM M t * cross v (partialSum hLT w N) t) ^ 2 ≤ W * B := by
    intro N hN
    set G := Finset.Icc (-(N : ℤ)) N
    have hFG : F ⊆ G := hN0.trans (Finset.Icc_subset_Icc (by simp; omega) (by simp; omega))
    have hv : v = trigPoly LT F a := lowBlock_eq_trigPoly LT S β c
    rw [hv, partialSum, cross_trigPoly_row M hLT F G a]
    have hz : ∑ m ∈ G, conj (fourierCoeffOn hLT w m) * z m = 0 := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hF : ∑ m ∈ G, conj (fourierCoeffOn hLT w m) * (lam i * atomRow LT S β i m) =
          ∑ m ∈ F, conj (fourierCoeffOn hLT w m) * (lam i * atomRow LT S β i m) := by
        refine (Finset.sum_subset hFG fun m _ hm => ?_).symm
        rw [atomRow, lowCoeff_eq_zero LT S β _ hm, mul_zero, mul_zero]
      rw [hF]
      have h0 := atom_orth hLT S β hwi hs i (horth i)
      calc ∑ m ∈ F, conj (fourierCoeffOn hLT w m) * (lam i * atomRow LT S β i m)
          = lam i * ∑ m ∈ F, conj (fourierCoeffOn hLT w m) * atomRow LT S β i m := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun m _ => by ring
        _ = 0 := by rw [h0, mul_zero]
    have hyz : ∑ m ∈ G, conj (fourierCoeffOn hLT w m) * y m =
        ∑ m ∈ G, conj (fourierCoeffOn hLT w m) * (y m - z m) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hz, sub_zero]
    rw [hyz]
    have hbes : ∑ m ∈ G, ‖fourierCoeffOn hLT w m‖ ^ 2 ≤ W :=
      sum_le_hasSum G (fun _ _ => sq_nonneg _) (hasSum_coef hLT hwi hC hs)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq G (fun m => ‖fourierCoeffOn hLT w m‖)
      (fun m => ‖y m - z m‖)
    have hn : ‖∑ m ∈ G, conj (fourierCoeffOn hLT w m) * (y m - z m)‖ ≤
        ∑ m ∈ G, ‖fourierCoeffOn hLT w m‖ * ‖y m - z m‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_))
      rw [norm_mul, Complex.norm_conj]
    have hn0 : 0 ≤ ∑ m ∈ G, ‖fourierCoeffOn hLT w m‖ * ‖y m - z m‖ :=
      Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hB' := hB N
    calc (∑ m ∈ G, conj (fourierCoeffOn hLT w m) * (y m - z m)).re ^ 2
        ≤ ‖∑ m ∈ G, conj (fourierCoeffOn hLT w m) * (y m - z m)‖ ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      _ ≤ (∑ m ∈ G, ‖fourierCoeffOn hLT w m‖ * ‖y m - z m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (∑ m ∈ G, ‖fourierCoeffOn hLT w m‖ ^ 2) * ∑ m ∈ G, ‖y m - z m‖ ^ 2 := hcs
      _ ≤ W * B := mul_le_mul hbes hB' (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          ((Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hbes)
  have hfin : (∫ t, ScertM M t * cross v w t) ^ 2 ≤ W * B :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨N0, hbound⟩)
  have hE := energy_eq_two_pi_L2 hwi hC hEw
  simp_rw [Complex.normSq_eq_norm_sq] at hE
  have hπ : 0 < 2 * Real.pi := by positivity
  have hW : W = (∫ t, energy w t) / (2 * Real.pi * LT) := by
    simp only [W, hE]
    field_simp
  rw [hW] at hfin
  calc _ ≤ (∫ t, energy w t) / (2 * Real.pi * LT) * B := hfin
    _ = B / (2 * Real.pi * LT) * ∫ t, energy w t := by ring

/-- **`window_of_certificate_matrix` with the cross bound on the rows of the CvS matrix.** -/
theorem window_of_certificate_rows (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin p → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hrows : ∀ c (N : ℕ), ∑ a ∈ Finset.Icc (-(N : ℤ)) N,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2 ≤
          Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hBrow : ∀ c, 0 ≤ Brow c := fun c =>
    (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hrows c 0)
  refine window_of_certificate_matrix M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos (fun c => Brow c / (2 * Real.pi * LT))
    (fun c => div_nonneg (hBrow c) (by positivity)) (fun c w hw => ?_) hlow g hm r a hw h2r
  exact cross_sq_le_of_rows M hLT0 (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c
    (lam c) (Brow c) (hrows c) hw

end AEGIS.CvSCrossCertV1

#print axioms AEGIS.CvSCrossCertV1.cross_sub
#print axioms AEGIS.CvSCrossCertV1.tendsto_cross_partialSum
#print axioms AEGIS.CvSCrossCertV1.cross_trigPoly_row
#print axioms AEGIS.CvSCrossCertV1.atom_orth
#print axioms AEGIS.CvSCrossCertV1.cross_sq_le_of_rows
#print axioms AEGIS.CvSCrossCertV1.window_of_certificate_rows
