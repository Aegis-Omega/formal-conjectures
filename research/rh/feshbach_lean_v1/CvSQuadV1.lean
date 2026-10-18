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
import CvSDigammaSeriesV1
import CvSMassV1
import CvSPrimePairV1

/-!
# The critical-line form of a trigonometric polynomial is the CvS matrix (CvS step 5.5)

For `G = ∑_{n ∈ F} v_n e_n` (`e_n = 𝟙_[0,L] e^{2πint/L}`) and the symbol
`S(t) = h₊(t) − ∑_{j < M} w_j cos(t log(j+1))`,

`(1/4π) ∫ S(t) (|𝓕G(t/2π)|² + |𝓕G(−t/2π)|²) dt = ∑_{n,m} v_n conj(v_m) M_nm`,

with, for `ω_n = 2πn/L`, `c_k = 2k + 1/2` and `ℓ_j = min(log(j+1), L)`,

* `M_nn = L h₊(ω_n) + 2 ∑' k (1 − e^{−c_k L})(c_k² − ω_n²)/(c_k² + ω_n²)² − ½ ∑_j w_j B_nn(ℓ_j)`,
* `M_nm = L (S_n − S_m)/(π(n − m)) − ½ ∑_j w_j B_nm(ℓ_j)`, `S_n = ½ Im ψ(1/4 + iπn/L) − ω_n g_s(n)`.

In the basis `e_n/√L` this is the matrix `pole − wr − wp` of `feshbach_blocks_arb.py` without the
pole part (which vanishes on the moment-zero space), and with `w_j = Λ(j+1)·2(j+1)^{-1/2}` the symbol
is the `ScertM` of `RHKreinZetaBridgeV3`.
-/

open MeasureTheory Complex Set Real
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace AEGIS.CvSQuadV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1 AEGIS.CvSDigammaSeriesV1
open AEGIS.CvSPrimeBlockV1 AEGIS.CvSMassV1 AEGIS.CvSPrimePairV1

/-- `cosB L n m t = ∫₀ᴸ B_nm(y) cos(ty) dy`. -/
abbrev cosB (L : ℝ) (n m : ℤ) (t : ℝ) : ℝ := cosT (blockFn L n m) L t

theorem blockFn_diag {L : ℝ} (hL : 0 < L) (n : ℤ) :
    blockFn L n n = fun y => L * diagProfile L n y := by
  funext y
  rw [blockFn, if_pos rfl, diagProfile,
    show 2 * Real.pi * n * y / L = 2 * Real.pi * n / L * y by ring]
  have : (L : ℝ) ≠ 0 := hL.ne'
  field_simp

theorem blockFn_off {L : ℝ} (_hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    blockFn L n m = fun y => L / (Real.pi * (n - m)) *
      (Real.sin (2 * Real.pi * n * (1 - y / L)) - Real.sin (2 * Real.pi * m * (1 - y / L))) := by
  funext y
  simp only [blockFn, if_neg hnm]
  rw [sin_node, sin_node, show 2 * Real.pi * m * y / L = 2 * Real.pi * m / L * y by ring,
    show 2 * Real.pi * n * y / L = 2 * Real.pi * n / L * y by ring]
  ring

theorem cosB_diag {L : ℝ} (hL : 0 < L) (n : ℤ) (t : ℝ) : cosB L n n t = L * diagD L t n := by
  simp only [cosB, cosT, diagD, blockFn_diag hL n, ← intervalIntegral.integral_const_mul]
  congr 1; funext y; ring

theorem cosB_off {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) (t : ℝ) :
    cosB L n m t = L / (Real.pi * (n - m)) * (sourceS L t n - sourceS L t m) := by
  simp only [cosB, cosT, sourceS, blockFn_off hL hnm]
  rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), ← intervalIntegral.integral_const_mul]
  congr 1; funext y; ring

theorem blockFn_at_L {L : ℝ} (hL : 0 < L) (n m : ℤ) : blockFn L n m L = 0 := by
  by_cases h : n = m
  · subst h; simp [blockFn]
  · rw [blockFn_off hL h]
    simp only [div_self hL.ne', sub_self, mul_zero, Real.sin_zero]

theorem cosB_bounds {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    ∃ M0 M2 : ℝ, (∀ t, |cosB L n m t| ≤ M0) ∧ ∀ t, |t ^ 2 * cosB L n m t| ≤ M2 := by
  by_cases h : n = m
  · subst h
    refine ⟨L * (2 * L), L * (2 * L * (2 * Real.pi * n / L) ^ 2 + 4 / L + 4 * |2 * Real.pi * n / L|),
      fun t => ?_, fun t => ?_⟩
    · rw [cosB_diag hL, abs_mul, abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left (diagD_abs_le hL n t) hL.le
    · rw [cosB_diag hL, show t ^ 2 * (L * diagD L t n) = L * (t ^ 2 * diagD L t n) by ring,
        abs_mul, abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left (sq_mul_diagD_abs_le hL n t) hL.le
  · set c := L / (Real.pi * (n - m))
    refine ⟨|c| * (L + L), |c| * (((2 * Real.pi * n / L) ^ 2 * L + 2 * |2 * Real.pi * n / L|) +
      ((2 * Real.pi * m / L) ^ 2 * L + 2 * |2 * Real.pi * m / L|)), fun t => ?_, fun t => ?_⟩
    · rw [cosB_off hL h, abs_mul]
      gcongr
      exact (abs_sub _ _).trans (add_le_add (sourceS_abs_le hL n t) (sourceS_abs_le hL m t))
    · rw [cosB_off hL h, show t ^ 2 * (c * (sourceS L t n - sourceS L t m)) =
        c * (t ^ 2 * sourceS L t n - t ^ 2 * sourceS L t m) by ring, abs_mul]
      gcongr
      exact (abs_sub _ _).trans
        (add_le_add (sq_mul_sourceS_abs_le hL n t) (sq_mul_sourceS_abs_le hL m t))

theorem cosB_continuous (L : ℝ) (n m : ℤ) : Continuous fun t => cosB L n m t :=
  cosT_continuous (blockFn_continuous L n m) L

theorem cosB_integrable {L : ℝ} (hL : 0 < L) (n m : ℤ) : Integrable fun t => cosB L n m t := by
  obtain ⟨M0, M2, h0, h2⟩ := cosB_bounds hL n m
  exact integrable_of_bounds (cosB_continuous L n m) h0 h2

/-- **Prime pairing of a block.** -/
theorem cos_cosB {L : ℝ} (hL : 0 < L) (n m : ℤ) (a : ℝ) :
    ∫ t : ℝ, Real.cos (t * a) * cosB L n m t = Real.pi * blockFn L n m (min |a| L) := by
  obtain ⟨M0, M2, h0, h2⟩ := cosB_bounds hL n m
  exact cos_pairing (blockFn_continuous L n m) hL.le (blockFn_at_L hL n m) h0 h2 a

theorem hplus_cosB_integrable {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable fun t => hplus t * cosB L n m t := by
  by_cases h : n = m
  · subst h
    refine ((hplus_mul_diagD_integrable hL n).const_mul L).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [cosB_diag hL]; ring
  · refine (((hplus_mul_sourceS_integrable hL n).sub (hplus_mul_sourceS_integrable hL m)).const_mul
      (L / (Real.pi * (n - m)))).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, cosB_off hL h]; ring

/-- **Archimedean diagonal entry.** -/
theorem hplus_cosB_diag {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∫ t, hplus t * cosB L n n t =
      L * (2 * Real.pi * hplus (2 * Real.pi * n / L) +
        4 * Real.pi / L * ∑' k, (1 - Real.exp (-archWidth k * L)) *
          (archWidth k ^ 2 - (2 * Real.pi * n / L) ^ 2) /
            (archWidth k ^ 2 + (2 * Real.pi * n / L) ^ 2) ^ 2) := by
  simp_rw [cosB_diag hL, show ∀ t, hplus t * (L * diagD L t n) = L * (hplus t * diagD L t n) from
    fun t => by ring]
  rw [integral_const_mul, hplus_diag_integral hL n]

/-- **Archimedean off-diagonal entry.** -/
theorem hplus_cosB_off {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    ∫ t, hplus t * cosB L n m t =
      L / (Real.pi * (n - m)) * ((∫ t, hplus t * sourceS L t n) - ∫ t, hplus t * sourceS L t m) := by
  simp_rw [cosB_off hL hnm, show ∀ t, hplus t * (L / (Real.pi * (n - m)) *
      (sourceS L t n - sourceS L t m)) = L / (Real.pi * (n - m)) *
        (hplus t * sourceS L t n - hplus t * sourceS L t m) from fun t => by ring]
  rw [integral_const_mul, integral_sub (hplus_mul_sourceS_integrable hL n)
    (hplus_mul_sourceS_integrable hL m)]

/-- The symbol `h₊(t) − ∑_{j<M} w_j cos(t log(j+1))`. -/
def qsym (M : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  hplus t - ∑ j ∈ Finset.range M, w j * Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ))

theorem cos_cosB_integrable {L : ℝ} (hL : 0 < L) (n m : ℤ) (a : ℝ) :
    Integrable fun t => Real.cos (t * a) * cosB L n m t :=
  (cosB_integrable hL n m).bdd_mul (c := 1) (by fun_prop : Continuous fun t : ℝ =>
    Real.cos (t * a)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

theorem qsym_cosB_integrable {L : ℝ} (hL : 0 < L) (M : ℕ) (w : ℕ → ℝ) (n m : ℤ) :
    Integrable fun t => qsym M w t * cosB L n m t := by
  have hP : Integrable fun t => ∑ j ∈ Finset.range M,
      w j * (Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ)) * cosB L n m t) :=
    integrable_finsetSum _ fun j _ => (cos_cosB_integrable hL n m _).const_mul _
  refine ((hplus_cosB_integrable hL n m).sub hP).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, qsym, sub_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The symbol against a block.** -/
theorem qsym_cosB_integral {L : ℝ} (hL : 0 < L) (M : ℕ) (w : ℕ → ℝ) (n m : ℤ) :
    ∫ t, qsym M w t * cosB L n m t =
      (∫ t, hplus t * cosB L n m t) - ∑ j ∈ Finset.range M,
        w j * (Real.pi * blockFn L n m (min |Real.log ((j + 1 : ℕ) : ℝ)| L)) := by
  have h : (fun t => qsym M w t * cosB L n m t) = fun t => hplus t * cosB L n m t -
      ∑ j ∈ Finset.range M, w j * (Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ)) * cosB L n m t) := by
    funext t
    simp only [qsym, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h, integral_sub (hplus_cosB_integrable hL n m)
    (integrable_finsetSum _ fun j _ => (cos_cosB_integrable hL n m _).const_mul _),
    integral_finsetSum _ fun j _ => (cos_cosB_integrable hL n m _).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, cos_cosB hL]

/-- **The critical-line form of a trigonometric polynomial is a Hermitian matrix form**, for any
symbol `S` integrable against every block. -/
theorem quad_trigPoly {L : ℝ} (hL : 0 < L) (F : Finset ℤ) (v : ℤ → ℂ) (S : ℝ → ℝ)
    (hS : ∀ n m : ℤ, Integrable fun t => S t * cosB L n m t) :
    (((1 / (4 * Real.pi)) * ∫ t, S t * (Complex.normSq (𝓕 (trigPoly L F v) (t / (2 * Real.pi))) +
        Complex.normSq (𝓕 (trigPoly L F v) (-t / (2 * Real.pi))))) : ℝ) =
      ∑ n ∈ F, ∑ m ∈ F, v n * conj (v m) *
        (((1 / (2 * Real.pi)) * ∫ t, S t * cosB L n m t : ℝ) : ℂ) := by
  have hpt : ∀ t, ((S t * (Complex.normSq (𝓕 (trigPoly L F v) (t / (2 * Real.pi))) +
      Complex.normSq (𝓕 (trigPoly L F v) (-t / (2 * Real.pi)))) : ℝ) : ℂ) =
      ∑ n ∈ F, ∑ m ∈ F, v n * conj (v m) * ((2 * (S t * cosB L n m t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_mul, mass_trigPoly hL F v t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [cosB, cosT]
    push_cast
    ring
  have hint : ∀ n m : ℤ, Integrable fun t => v n * conj (v m) *
      ((2 * (S t * cosB L n m t) : ℝ) : ℂ) := fun n m =>
    (((hS n m).const_mul 2).ofReal (𝕜 := ℂ)).const_mul _
  push_cast
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, integral_const_mul]
  push_cast
  ring

end AEGIS.CvSQuadV1

#print axioms AEGIS.CvSQuadV1.blockFn_diag
#print axioms AEGIS.CvSQuadV1.blockFn_off
#print axioms AEGIS.CvSQuadV1.cosB_diag
#print axioms AEGIS.CvSQuadV1.cosB_off
#print axioms AEGIS.CvSQuadV1.blockFn_at_L
#print axioms AEGIS.CvSQuadV1.cosB_bounds
#print axioms AEGIS.CvSQuadV1.cosB_integrable
#print axioms AEGIS.CvSQuadV1.cos_cosB
#print axioms AEGIS.CvSQuadV1.hplus_cosB_integrable
#print axioms AEGIS.CvSQuadV1.hplus_cosB_diag
#print axioms AEGIS.CvSQuadV1.hplus_cosB_off
#print axioms AEGIS.CvSQuadV1.qsym_cosB_integrable
#print axioms AEGIS.CvSQuadV1.qsym_cosB_integral
#print axioms AEGIS.CvSQuadV1.quad_trigPoly
