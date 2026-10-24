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
import CvSMomentV1

/-!
# Fourier tails of `e^{ixt}` and `e^{σx}` on `[0, L]` (CvS step K3a)

For `f_t = 𝟙_[0,L] e^{ixt}` and `u_σ = 𝟙_[0,L] e^{σx}`, with `h = 2π/L` and `K = [−N, N]`:

* `coef_fT`, `coef_uS`: closed forms of `L · f̂_t(k)` and `L · û_σ(k)` (via `trigAtom_moment`);
* `tail_sum_le`: `Σ_{k ∈ F} (t − hk)⁻² ≤ 1/(h(hN − t)) + 1/(h(hN + t))` for every finite `F`
  disjoint from `K`, when `|t| < hN` (telescoping);
* `norm_sub_trigPoly_le`: Parseval turns a bound on every finite tail of `|ŵ_k|²` into
  `∫ |w − Σ_K ŵ_k e_k|² ≤ L · B`;
* `fT_tail`: `∫ |f_t − P_t|² ≤ (|e^{itL} − 1|²/L) (1/(h(hN − t)) + 1/(h(hN + t)))`;
* `uS_tail`: `∫ |u_σ − p_σ|² ≤ ((e^{σL} − 1)²/L) · 2/(h²N)`.

Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSTraceCoefV1

open AEGIS.CvSPrimeBlockV1 AEGIS.CvSFourierIntervalV1 AEGIS.CvSMomentV1

/-- `f_t = 𝟙_[0,L] e^{ixt}`. -/
def fT (LT t : ℝ) : ℝ → ℂ := indicator (Icc 0 LT) (fun x : ℝ => cexp (↑(x * t) * I))

/-- `u_σ = 𝟙_[0,L] e^{σx}`. -/
def uS (LT σ : ℝ) : ℝ → ℂ := indicator (Icc 0 LT) (fun x : ℝ => ((Real.exp (σ * x) : ℝ) : ℂ))

theorem fT_support (LT t : ℝ) : Function.support (fT LT t) ⊆ Icc 0 LT :=
  support_indicator_subset

theorem uS_support (LT σ : ℝ) : Function.support (uS LT σ) ⊆ Icc 0 LT :=
  support_indicator_subset

theorem fT_norm_le (LT t x : ℝ) : ‖fT LT t x‖ ≤ 1 := by
  unfold fT
  by_cases hx : x ∈ Icc 0 LT
  · rw [indicator_of_mem hx, Complex.norm_exp_ofReal_mul_I]
  · rw [indicator_of_notMem hx, norm_zero]
    exact zero_le_one

theorem uS_norm_le (LT σ x : ℝ) : ‖uS LT σ x‖ ≤ Real.exp (|σ| * LT) := by
  unfold uS
  by_cases hx : x ∈ Icc 0 LT
  · rw [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : σ * x ≤ |σ| * x := mul_le_mul_of_nonneg_right (le_abs_self σ) hx.1
    have h2 : |σ| * x ≤ |σ| * LT := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg σ)
    linarith
  · rw [indicator_of_notMem hx, norm_zero]
    exact (Real.exp_pos _).le

theorem fT_integrable (LT t : ℝ) : Integrable (fT LT t) := by
  unfold fT
  rw [integrable_indicator_iff measurableSet_Icc]
  exact Continuous.integrableOn_Icc (by fun_prop)

theorem uS_integrable (LT σ : ℝ) : Integrable (uS LT σ) := by
  unfold uS
  rw [integrable_indicator_iff measurableSet_Icc]
  exact Continuous.integrableOn_Icc (by fun_prop)

theorem conj_trigAtom (LT : ℝ) (k : ℤ) (x : ℝ) : conj (trigAtom LT k x) = trigAtom LT (-k) x := by
  by_cases hx : x ∈ Icc 0 LT
  · simp only [trigAtom, indicator_of_mem hx]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
    push_cast
    ring
  · simp [trigAtom, indicator_of_notMem hx]

/-! ### Closed forms -/

theorem coef_fT {LT : ℝ} (hLT : 0 < LT) (t : ℝ) (k : ℤ)
    (hk : (t : ℂ) * I + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT ≠ 0) :
    (LT : ℂ) * fourierCoeffOn hLT (fT LT t) k =
      (cexp ((t : ℂ) * I * LT) - 1) / ((t : ℂ) * I + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT) := by
  rw [← coef_eq hLT (fT_support LT t) k]
  have e : (fun x => fT LT t x * conj (trigAtom LT k x)) =
      fun x => trigAtom LT (-k) x * cexp ((t : ℂ) * I * x) := by
    funext x
    rw [conj_trigAtom]
    by_cases hx : x ∈ Icc 0 LT
    · simp only [fT, trigAtom, indicator_of_mem hx]
      rw [mul_comm, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [fT, trigAtom, indicator_of_notMem hx]
  rw [e, trigAtom_moment hLT (-k) hk]

theorem coef_uS {LT : ℝ} (hLT : 0 < LT) {σ : ℝ} (hσ : σ ≠ 0) (k : ℤ) :
    (LT : ℂ) * fourierCoeffOn hLT (uS LT σ) k =
      (cexp ((σ : ℂ) * LT) - 1) / ((σ : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT) := by
  rw [← coef_eq hLT (uS_support LT σ) k]
  have e : (fun x => uS LT σ x * conj (trigAtom LT k x)) =
      fun x => trigAtom LT (-k) x * cexp ((σ : ℂ) * x) := by
    funext x
    rw [conj_trigAtom]
    by_cases hx : x ∈ Icc 0 LT
    · simp only [uS, trigAtom, indicator_of_mem hx]
      rw [mul_comm]
      congr 1
      push_cast
      ring_nf
    · simp [uS, trigAtom, indicator_of_notMem hx]
  rw [e, trigAtom_moment hLT (-k) (half_add_ne_zero LT (-k) hσ)]

theorem normSq_coef_fT {LT : ℝ} (hLT : 0 < LT) (t : ℝ) (k : ℤ)
    (hk : t ≠ 2 * Real.pi * k / LT) :
    ‖fourierCoeffOn hLT (fT LT t) k‖ ^ 2 =
      ‖cexp ((t : ℂ) * I * LT) - 1‖ ^ 2 / LT ^ 2 * (1 / (t - 2 * Real.pi / LT * k) ^ 2) := by
  have hne : t - 2 * Real.pi / LT * k ≠ 0 := by
    intro h0
    apply hk
    have : 2 * Real.pi / LT * k = 2 * Real.pi * k / LT := by ring
    linarith
  have hd : (t : ℂ) * I + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT =
      ((t - 2 * Real.pi / LT * k : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hd0 : (t : ℂ) * I + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (by exact_mod_cast hne) I_ne_zero
  have h := coef_fT hLT t k hd0
  rw [hd] at h
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have hc : fourierCoeffOn hLT (fT LT t) k =
      (cexp ((t : ℂ) * I * LT) - 1) / (((t - 2 * Real.pi / LT * k : ℝ) : ℂ) * I) / LT := by
    rw [← h]
    field_simp
  rw [hc, norm_div, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLT, div_pow, div_pow,
    sq_abs]
  field_simp

theorem normSq_coef_uS_le {LT : ℝ} (hLT : 0 < LT) {σ : ℝ} (hσ : σ ≠ 0) {k : ℤ} (hk : k ≠ 0) :
    ‖fourierCoeffOn hLT (uS LT σ) k‖ ^ 2 ≤
      (Real.exp (σ * LT) - 1) ^ 2 / LT ^ 2 * (1 / (0 - 2 * Real.pi / LT * k) ^ 2) := by
  have hd : (σ : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT =
      (σ : ℂ) + ((-(2 * Real.pi / LT * k) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hd0 := half_add_ne_zero LT (-k) hσ
  have h := coef_uS hLT hσ k
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have hc : fourierCoeffOn hLT (uS LT σ) k =
      (cexp ((σ : ℂ) * LT) - 1) / ((σ : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT) / LT := by
    rw [← h]
    field_simp
  have hn : ‖(σ : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT‖ ^ 2 =
      σ ^ 2 + (2 * Real.pi / LT * k) ^ 2 := by
    rw [hd, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring
  have he : ‖cexp ((σ : ℂ) * LT) - 1‖ = |Real.exp (σ * LT) - 1| := by
    rw [show cexp ((σ : ℂ) * LT) - 1 = ((Real.exp (σ * LT) - 1 : ℝ) : ℂ) by push_cast; ring_nf,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hc, norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLT, div_pow,
    div_pow, he, sq_abs]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hw : 0 < (2 * Real.pi / LT * k) ^ 2 := by positivity
  rw [hn, zero_sub, neg_sq]
  rw [div_div, one_div, ← div_eq_mul_inv, div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [sq_nonneg σ, sq_nonneg LT]

/-! ### The telescoping tail -/

theorem tail_one_side {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (a + h * ((j : ℝ) + 1)) ^ 2 ≤ 1 / (h * a) := by
  set f : ℕ → ℝ := fun j => 1 / (a + h * j) with hf
  have key : ∀ j : ℕ, 1 / (a + h * ((j : ℝ) + 1)) ^ 2 ≤ (1 / h) * (f j - f (j + 1)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : 0 < a + h * j := by positivity
    have e : (1 / h) * (f j - f (j + 1)) = 1 / ((a + h * j) * (a + h * ((j : ℝ) + 1))) := by
      simp only [hf]
      push_cast
      field_simp
      ring
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  calc ∑ j ∈ Finset.range J, 1 / (a + h * ((j : ℝ) + 1)) ^ 2
      ≤ ∑ j ∈ Finset.range J, (1 / h) * (f j - f (j + 1)) := Finset.sum_le_sum fun j _ => key j
    _ = (1 / h) * (f 0 - f J) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 1 / (h * a) := by
      have h0 : f 0 = 1 / a := by simp [hf]
      have hJ : 0 ≤ f J := by simp only [hf]; positivity
      rw [h0]
      have : (1 / h) * (1 / a) = 1 / (h * a) := by field_simp
      nlinarith [one_div_pos.mpr hh]

theorem tail_sum_le {h t : ℝ} (hh : 0 < h) {N : ℕ} (ht : |t| < h * N) (F : Finset ℤ)
    (hF : Disjoint F (Finset.Icc (-(N : ℤ)) N)) :
    ∑ k ∈ F, 1 / (t - h * k) ^ 2 ≤ 1 / (h * (h * N - t)) + 1 / (h * (h * N + t)) := by
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  set J : ℕ := ∑ k ∈ F, k.natAbs with hJdef
  have hmem : ∀ k ∈ F, (N : ℤ) < k ∨ k < -(N : ℤ) := by
    intro k hk
    have : k ∉ Finset.Icc (-(N : ℤ)) N := Finset.disjoint_left.mp hF hk
    rw [Finset.mem_Icc] at this
    omega
  have hJ : ∀ k ∈ F, k.natAbs ≤ J := fun k hk =>
    Finset.single_le_sum (f := fun k : ℤ => k.natAbs) (fun _ _ => Nat.zero_le _) hk
  have hpos : F.filter (fun k => 0 < k) ⊆
      (Finset.range J).image (fun j : ℕ => (N : ℤ) + 1 + j) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_image]
    have h1 := hmem k hk.1
    have h2 := hJ k hk.1
    refine ⟨(k - N - 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hneg : F.filter (fun k => ¬ 0 < k) ⊆
      (Finset.range J).image (fun j : ℕ => -((N : ℤ) + 1 + j)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_image]
    have h1 := hmem k hk.1
    have h2 := hJ k hk.1
    refine ⟨(-k - N - 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hg : ∀ k : ℤ, 0 ≤ 1 / (t - h * k) ^ 2 := fun k => by positivity
  have inj1 : Set.InjOn (fun j : ℕ => (N : ℤ) + 1 + j) (Finset.range J) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have inj2 : Set.InjOn (fun j : ℕ => -((N : ℤ) + 1 + j)) (Finset.range J) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have s1 : ∑ k ∈ F.filter (fun k => 0 < k), 1 / (t - h * k) ^ 2 ≤
      ∑ j ∈ Finset.range J, 1 / ((h * N - t) + h * ((j : ℝ) + 1)) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hpos (fun k _ _ => hg k)).trans (le_of_eq ?_)
    rw [Finset.sum_image inj1]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring
  have s2 : ∑ k ∈ F.filter (fun k => ¬ 0 < k), 1 / (t - h * k) ^ 2 ≤
      ∑ j ∈ Finset.range J, 1 / ((h * N + t) + h * ((j : ℝ) + 1)) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hneg (fun k _ _ => hg k)).trans (le_of_eq ?_)
    rw [Finset.sum_image inj2]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring
  have t1 := tail_one_side hh (show 0 < h * N - t by linarith) J
  have t2 := tail_one_side hh (show 0 < h * N + t by linarith) J
  rw [← Finset.sum_filter_add_sum_filter_not F (fun k => 0 < k)]
  linarith

/-! ### Parseval tails -/

theorem norm_sub_trigPoly_le {LT : ℝ} (hLT : 0 < LT) {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ}
    (hC : ∀ x, ‖w x‖ ≤ C) (hs : Function.support w ⊆ Icc 0 LT) (S : Finset ℤ) {B : ℝ}
    (hB : ∀ F : Finset ℤ, Disjoint F S → ∑ k ∈ F, ‖fourierCoeffOn hLT w k‖ ^ 2 ≤ B) :
    ∫ x, ‖w x - trigPoly LT S (fourierCoeffOn hLT w) x‖ ^ 2 ≤ LT * B := by
  rw [norm_sub_trigPoly hLT hw hC hs S]
  have h1 : LT⁻¹ * ∫ x, ‖w x‖ ^ 2 ≤ ∑ k ∈ S, ‖fourierCoeffOn hLT w k‖ ^ 2 + B := by
    refine hasSum_le_of_sum_le (hasSum_coef hLT hw hC hs) fun F => ?_
    rw [← Finset.sum_inter_add_sum_sdiff F S]
    have a : ∑ k ∈ F ∩ S, ‖fourierCoeffOn hLT w k‖ ^ 2 ≤ ∑ k ∈ S, ‖fourierCoeffOn hLT w k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => by positivity)
    have b := hB (F \ S) Finset.sdiff_disjoint
    linarith
  have h2 : ∫ x, ‖w x‖ ^ 2 ≤ LT * (∑ k ∈ S, ‖fourierCoeffOn hLT w k‖ ^ 2 + B) := by
    have := mul_le_mul_of_nonneg_left h1 hLT.le
    rwa [← mul_assoc, mul_inv_cancel₀ hLT.ne', one_mul] at this
  linarith

theorem natAbs_gt_of_disjoint {N : ℕ} {F : Finset ℤ} (hF : Disjoint F (Finset.Icc (-(N : ℤ)) N))
    {k : ℤ} (hk : k ∈ F) : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
  have : k ∉ Finset.Icc (-(N : ℤ)) N := Finset.disjoint_left.mp hF hk
  rw [Finset.mem_Icc] at this
  have h : (N : ℤ) + 1 ≤ |k| := by
    rcases le_or_gt 0 k with h0 | h0
    · rw [abs_of_nonneg h0]; omega
    · rw [abs_of_neg h0]; omega
  have : ((N : ℤ) + 1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at this
  exact this

/-- **The tail of `f_t`.** -/
theorem fT_tail {LT : ℝ} (hLT : 0 < LT) {t : ℝ} {N : ℕ} (ht : |t| < 2 * Real.pi / LT * N) :
    ∫ x, ‖fT LT t x - trigPoly LT (Finset.Icc (-(N : ℤ)) N) (fourierCoeffOn hLT (fT LT t)) x‖ ^ 2 ≤
      ‖cexp ((t : ℂ) * I * LT) - 1‖ ^ 2 / LT *
        (1 / (2 * Real.pi / LT * (2 * Real.pi / LT * N - t)) +
          1 / (2 * Real.pi / LT * (2 * Real.pi / LT * N + t))) := by
  set h := 2 * Real.pi / LT with hh
  have hh0 : 0 < h := by positivity
  have key := norm_sub_trigPoly_le hLT (fT_integrable LT t) (fT_norm_le LT t) (fT_support LT t)
    (Finset.Icc (-(N : ℤ)) N)
    (B := ‖cexp ((t : ℂ) * I * LT) - 1‖ ^ 2 / LT ^ 2 *
      (1 / (h * (h * N - t)) + 1 / (h * (h * N + t)))) ?_
  · calc _ ≤ LT * (‖cexp ((t : ℂ) * I * LT) - 1‖ ^ 2 / LT ^ 2 *
          (1 / (h * (h * N - t)) + 1 / (h * (h * N + t)))) := key
      _ = _ := by field_simp
  · intro F hF
    have hne : ∀ k ∈ F, t ≠ 2 * Real.pi * k / LT := by
      intro k hk heq
      have h1 := natAbs_gt_of_disjoint hF hk
      have h2 : |t| = h * |(k : ℝ)| := by
        rw [heq, hh, show 2 * Real.pi * (k : ℝ) / LT = 2 * Real.pi / LT * k by ring, abs_mul,
          abs_of_pos hh0]
      have h3 : h * ((N : ℝ) + 1) ≤ h * |(k : ℝ)| := mul_le_mul_of_nonneg_left h1 hh0.le
      nlinarith
    rw [Finset.sum_congr rfl (fun k hk => normSq_coef_fT hLT t k (hne k hk)), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (tail_sum_le hh0 ht F hF) (by positivity)

/-- **The tail of `u_σ`.** -/
theorem uS_tail {LT : ℝ} (hLT : 0 < LT) {σ : ℝ} (hσ : σ ≠ 0) {N : ℕ} (hN : 0 < N) :
    ∫ x, ‖uS LT σ x - trigPoly LT (Finset.Icc (-(N : ℤ)) N) (fourierCoeffOn hLT (uS LT σ)) x‖ ^ 2 ≤
      (Real.exp (σ * LT) - 1) ^ 2 / LT *
        (1 / (2 * Real.pi / LT * (2 * Real.pi / LT * N - 0)) +
          1 / (2 * Real.pi / LT * (2 * Real.pi / LT * N + 0))) := by
  set h := 2 * Real.pi / LT with hh
  have hh0 : 0 < h := by positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : |(0 : ℝ)| < h * N := by rw [abs_zero]; positivity
  have key := norm_sub_trigPoly_le hLT (uS_integrable LT σ) (uS_norm_le LT σ) (uS_support LT σ)
    (Finset.Icc (-(N : ℤ)) N)
    (B := (Real.exp (σ * LT) - 1) ^ 2 / LT ^ 2 *
      (1 / (h * (h * N - 0)) + 1 / (h * (h * N + 0)))) ?_
  · calc _ ≤ LT * ((Real.exp (σ * LT) - 1) ^ 2 / LT ^ 2 *
          (1 / (h * (h * N - 0)) + 1 / (h * (h * N + 0)))) := key
      _ = _ := by field_simp
  · intro F hF
    have h0 : ∀ k ∈ F, k ≠ 0 := by
      intro k hk h0
      subst h0
      have := Finset.disjoint_left.mp hF hk
      simp at this
    refine (Finset.sum_le_sum fun k hk => normSq_coef_uS_le hLT hσ (h0 k hk)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (tail_sum_le hh0 ht F hF) (by positivity)

end AEGIS.CvSTraceCoefV1

#print axioms AEGIS.CvSTraceCoefV1.coef_fT
#print axioms AEGIS.CvSTraceCoefV1.coef_uS
#print axioms AEGIS.CvSTraceCoefV1.normSq_coef_fT
#print axioms AEGIS.CvSTraceCoefV1.normSq_coef_uS_le
#print axioms AEGIS.CvSTraceCoefV1.tail_sum_le
#print axioms AEGIS.CvSTraceCoefV1.norm_sub_trigPoly_le
#print axioms AEGIS.CvSTraceCoefV1.fT_tail
#print axioms AEGIS.CvSTraceCoefV1.uS_tail
