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
import CvSCrossCertV1
import CvSResidualCertificateV1

/-!
# The tail of the rows of the cross block (CvS step 6j, ring tree)

With `τ_k = ∫ h₊ S_k + π Σ_{j<M} ppw_j sin(2πk ℓ_j/L)` (`tau`, `ℓ_j = min(log(j+1), L)`),

  `cvsEntry M L n m = L/(2π²) · (τ_n − τ_m)/(n − m)`   for `n ≠ m`   (`cvsEntry_off`),

so the matrix is symmetric (`cvsEntry_symm`). `|Σ_k ω/(c_k² + ω²)| ≤ 1 + π/4` by comparison
with `arctan` (`tsum_abs_width_le`), hence `|∫ h₊ S_k| ≤ 4π(1 + π/4)` (`source_integral_abs_le`)
and `|τ_k| ≤ tauBound M` (`tau_abs_le`).

Off the low frequencies `F ⊆ [−R, R]` a row is `y_m = (L/π) Σ_n a_n (τ_n − τ_m)/(n − m)`
(`crossRow_off`); the order-`K` expansion of `1/(n − m)` (`inv_sub_expand`) bounds it by the
functionals `P_j = Σ a_n τ_n n^j`, `Q_j = Σ a_n n^j` over `|m|^{j+1}` plus a remainder
`O(R^K/(|m|^K (|m| − R)))` (`crossRow_tail_le`). Summing over `NP < |m| ≤ N` with
`Σ_{k>NP} k^{-(q+2)} ≤ NP^{-(q+1)}` and its shifted version gives the explicit tail `rowTail`
(`rows_tail_le`), and `window_of_certificate_tail` is `CvSCrossCertV1.window_of_certificate_rows`
with the row hypothesis replaced by finitely many rows `|m| ≤ NP` plus `rowTail`. Not RH.
-/

open MeasureTheory Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSRowTailV1

open AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSQuadV1
open AEGIS.CvSMassV1 AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1
open AEGIS.CvSMomentBasisV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- The prime-power nodes `ℓ_j = min(log(j+1), L)`. -/
abbrev node (L : ℝ) (j : ℕ) : ℝ := min |Real.log ((j + 1 : ℕ) : ℝ)| L

/-- `τ_k = ∫ h₊ S_k + π Σ_{j<M} ppw_j sin(2πk ℓ_j/L)`. -/
def tau (M : ℕ) (L : ℝ) (k : ℤ) : ℝ :=
  (∫ r, hplus r * sourceS L r k) +
    Real.pi * ∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * k * node L j / L)

/-- **The off-diagonal entries are divided differences of `τ`.** -/
theorem cvsEntry_off (M : ℕ) {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    cvsEntry M L n m = L / (2 * Real.pi ^ 2) * ((tau M L n - tau M L m) / (n - m)) := by
  have hnm' : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : ∑ j ∈ Finset.range M, ppw j * (Real.pi * blockFn L n m (node L j)) =
      L / (n - m) * ((∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * m * node L j / L)) -
        ∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * n * node L j / L)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [blockFn, if_neg hnm]
    field_simp
  rw [cvsEntry, hplus_cosB_off hL hnm, hs, tau, tau]
  field_simp
  ring

theorem cvsEntry_symm (M : ℕ) {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    cvsEntry M L n m = cvsEntry M L m n := by
  by_cases h : n = m
  · rw [h]
  have h1 : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have h2 : ((m : ℝ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm h)
  rw [cvsEntry_off M hL h, cvsEntry_off M hL (Ne.symm h)]
  field_simp
  ring

theorem arctan_sub_ge {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b) / (1 + a ^ 2) ≤ Real.arctan a - Real.arctan b := by
  rw [← integral_one_div_one_add_sq]
  have h := intervalIntegral.integral_mono_on hab (f := fun _ => 1 / (1 + a ^ 2))
    (g := fun x : ℝ => 1 / (1 + x ^ 2)) (intervalIntegrable_const (μ := volume))
    ((continuous_const.div (by fun_prop) fun x => by positivity :
      Continuous fun x : ℝ => 1 / (1 + x ^ 2)).intervalIntegrable _ _)
    (fun x hx => one_div_le_one_div_of_le (by positivity) (by nlinarith [hx.1, hx.2]))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  calc (a - b) / (1 + a ^ 2) = (a - b) * (1 / (1 + a ^ 2)) := by ring
    _ ≤ _ := h

theorem sum_width_le {ω : ℝ} (hω : 0 < ω) (K : ℕ) :
    ∑ k ∈ Finset.range K, ω / (archWidth k ^ 2 + ω ^ 2) ≤ 1 + Real.pi / 4 := by
  have h0 : ω / (archWidth 0 ^ 2 + ω ^ 2) ≤ 1 := by
    rw [div_le_one (by have := archWidth_pos 0; positivity)]
    unfold archWidth
    nlinarith [sq_nonneg (ω - 1 / 2)]
  have hstep : ∀ k : ℕ, ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤
      (Real.arctan (2 * ((k : ℝ) + 1) / ω) - Real.arctan (2 * k / ω)) / 2 := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have ha := arctan_sub_ge (a := 2 * ((k : ℝ) + 1) / ω) (b := 2 * k / ω) (by positivity)
      (by gcongr; linarith)
    have e : (2 * ((k : ℝ) + 1) / ω - 2 * k / ω) / (1 + (2 * ((k : ℝ) + 1) / ω) ^ 2) =
        2 * ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    rw [e] at ha
    have hc : archWidth (k + 1) ^ 2 + ω ^ 2 ≥ ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2 := by
      unfold archWidth
      push_cast
      nlinarith
    calc ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤ ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_left hω.le (by positivity) hc
      _ = (2 * ω / (ω ^ 2 + 4 * ((k : ℝ) + 1) ^ 2)) / 2 := by ring
      _ ≤ _ := by linarith
  rcases K with _ | K
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  rw [Finset.sum_range_succ']
  have htel : ∑ k ∈ Finset.range K, ω / (archWidth (k + 1) ^ 2 + ω ^ 2) ≤
      (Real.arctan (2 * (K : ℝ) / ω) - Real.arctan (2 * ((0 : ℕ) : ℝ) / ω)) / 2 := by
    calc ∑ k ∈ Finset.range K, ω / (archWidth (k + 1) ^ 2 + ω ^ 2)
        ≤ ∑ k ∈ Finset.range K,
            (Real.arctan (2 * ((k : ℝ) + 1) / ω) - Real.arctan (2 * k / ω)) / 2 :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = (Real.arctan (2 * (K : ℝ) / ω) - Real.arctan (2 * ((0 : ℕ) : ℝ) / ω)) / 2 := by
          rw [← Finset.sum_div]
          have := Finset.sum_range_sub (fun k : ℕ => Real.arctan (2 * (k : ℝ) / ω)) K
          simp only [Nat.cast_add, Nat.cast_one] at this
          rw [this]
  have hpi := Real.arctan_lt_pi_div_two (2 * (K : ℝ) / ω)
  simp only [Nat.cast_zero, mul_zero, zero_div, Real.arctan_zero, sub_zero] at htel
  linarith

/-- **The digamma imaginary-part series is bounded.** -/
theorem tsum_abs_width_le (ω : ℝ) :
    ∑' k, |ω| / (archWidth k ^ 2 + ω ^ 2) ≤ 1 + Real.pi / 4 := by
  refine Real.tsum_le_of_sum_range_le (fun k => by have := archWidth_pos k; positivity)
    fun K => ?_
  rcases eq_or_ne ω 0 with h | h
  · simp only [h, abs_zero, zero_div, Finset.sum_const_zero]
    positivity
  have e : ∀ k, |ω| / (archWidth k ^ 2 + ω ^ 2) = |ω| / (archWidth k ^ 2 + |ω| ^ 2) := fun k => by
    rw [sq_abs]
  simp_rw [e]
  exact sum_width_le (abs_pos.mpr h) K

theorem abs_tsum_width_le (ω : ℝ) {f : ℕ → ℝ} (hf : ∀ k, |f k| ≤ |ω| / (archWidth k ^ 2 + ω ^ 2)) :
    |∑' k, f k| ≤ 1 + Real.pi / 4 := by
  have hs : Summable fun k => |ω| / (archWidth k ^ 2 + ω ^ 2) := by
    refine ((summable_inv_width ω).mul_left |ω|).congr fun k => ?_
    ring
  have hsn : Summable fun k => ‖f k‖ :=
    hs.of_nonneg_of_le (fun k => norm_nonneg _) fun k => by rw [Real.norm_eq_abs]; exact hf k
  rw [← Real.norm_eq_abs]
  calc ‖∑' k, f k‖ ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k, |ω| / (archWidth k ^ 2 + ω ^ 2) :=
      hsn.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hf k) hs
    _ ≤ 1 + Real.pi / 4 := tsum_abs_width_le ω

/-- **The archimedean source integrals are bounded.** -/
theorem source_integral_abs_le {L : ℝ} (hL : 0 < L) (n : ℤ) :
    |∫ r, hplus r * sourceS L r n| ≤ 4 * Real.pi * (1 + Real.pi / 4) := by
  rw [hplus_source_integral hL n]
  set ω := 2 * Real.pi * n / L with hω
  have hhalf : Real.pi * n / L = ω / 2 := by rw [hω]; ring
  rw [hhalf, half_im_digamma]
  clear_value ω
  have h1 : |∑' k, ω / (archWidth k ^ 2 + ω ^ 2)| ≤ 1 + Real.pi / 4 :=
    abs_tsum_width_le ω fun k => by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < archWidth k ^ 2 + ω ^ 2 by
        have := archWidth_pos k; positivity)]
  have h2 : |ω * ∑' k, Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2)| ≤
      1 + Real.pi / 4 := by
    have hs : Summable fun k => Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => by have := archWidth_pos k; positivity)
        (fun k => ?_) (summable_inv_width ω)
      have hc := archWidth_pos k
      gcongr
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    rw [← tsum_mul_left]
    refine abs_tsum_width_le ω fun k => ?_
    have hc := archWidth_pos k
    have he : Real.exp (-archWidth k * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_mul, abs_div, abs_of_pos (Real.exp_pos _),
      abs_of_pos (show (0 : ℝ) < archWidth k ^ 2 + ω ^ 2 by positivity)]
    calc |ω| * (Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2))
        ≤ |ω| * (1 / (archWidth k ^ 2 + ω ^ 2)) := by gcongr
      _ = |ω| / (archWidth k ^ 2 + ω ^ 2) := by ring
  have hπ : 0 < Real.pi := Real.pi_pos
  calc |2 * Real.pi * (∑' k, ω / (archWidth k ^ 2 + ω ^ 2) -
        ω * ∑' k, Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2))|
      = 2 * Real.pi * |∑' k, ω / (archWidth k ^ 2 + ω ^ 2) -
        ω * ∑' k, Real.exp (-archWidth k * L) / (archWidth k ^ 2 + ω ^ 2)| := by
        rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ 2 * Real.pi * ((1 + Real.pi / 4) + (1 + Real.pi / 4)) := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add h1 h2)
    _ = 4 * Real.pi * (1 + Real.pi / 4) := by ring

/-- **`τ` is bounded.** -/
theorem tau_abs_le (M : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    |tau M L k| ≤ 4 * Real.pi * (1 + Real.pi / 4) +
      Real.pi * ∑ j ∈ Finset.range M, |ppw j| := by
  have hP : |∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * k * node L j / L)| ≤
      ∑ j ∈ Finset.range M, |ppw j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  rw [tau]
  calc |(∫ r, hplus r * sourceS L r k) +
        Real.pi * ∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * k * node L j / L)|
      ≤ |∫ r, hplus r * sourceS L r k| +
        |Real.pi * ∑ j ∈ Finset.range M, ppw j * Real.sin (2 * Real.pi * k * node L j / L)| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        exact add_le_add (source_integral_abs_le hL k)
          (mul_le_mul_of_nonneg_left hP Real.pi_pos.le)

open AEGIS.CvSCrossCertV1 in
/-- Off the low frequencies the rows are divided differences of `τ`. -/
theorem crossRow_off (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} (a : ℤ → ℂ) {m : ℤ}
    (hm : m ∉ F) :
    crossRow M L F a m = ((L / Real.pi : ℝ) : ℂ) *
      ∑ n ∈ F, a n * (((tau M L n - tau M L m) / (n - m) : ℝ) : ℂ) := by
  rw [crossRow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnm : n ≠ m := fun h => hm (h ▸ hn)
  have hnm' : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [cvsEntry_symm M hL m n, cvsEntry_off M hL hnm]
  push_cast
  field_simp
  ring

/-- `1/(n − m) = −Σ_{j<K} n^j/m^{j+1} + n^K/(m^K (n − m))`. -/
theorem inv_sub_expand (K : ℕ) {n m : ℝ} (hm : m ≠ 0) (hnm : n - m ≠ 0) :
    1 / (n - m) = -∑ j ∈ Finset.range K, n ^ j / m ^ (j + 1) + n ^ K / (m ^ K * (n - m)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

open AEGIS.CvSCrossCertV1 in
/-- **Pointwise bound on a row off the low frequencies**, from the order-`K` expansion of
`1/(n − m)`: the `j`-th term involves the functionals `P_j = Σ a_n τ_n n^j`, `Q_j = Σ a_n n^j`, and
the remainder is `O(R^K / (|m|^K (|m| − R)))`. -/
theorem crossRow_tail_le (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} {R : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (a : ℤ → ℂ) (K : ℕ) {T : ℝ}
    (hT : ∀ k, |tau M L k| ≤ T) {m : ℤ} (hm : (R : ℝ) < |(m : ℝ)|) :
    ‖crossRow M L F a m‖ ≤ L / Real.pi *
      (∑ j ∈ Finset.range K, (‖∑ n ∈ F, a n * ((tau M L n * (n : ℝ) ^ j : ℝ) : ℂ)‖ +
          T * ‖∑ n ∈ F, a n * (((n : ℝ) ^ j : ℝ) : ℂ)‖) / |(m : ℝ)| ^ (j + 1) +
        2 * T * R ^ K * (∑ n ∈ F, ‖a n‖) / (|(m : ℝ)| ^ K * (|(m : ℝ)| - R))) := by
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hmF : m ∉ F := fun h => by have := hF m h; linarith
  have hmpos : 0 < |(m : ℝ)| := lt_of_le_of_lt hR0 hm
  have hm0 : (m : ℝ) ≠ 0 := abs_pos.mp hmpos
  have hgap : 0 < |(m : ℝ)| - R := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
  set τm := tau M L m with hτm
  have hnm : ∀ n ∈ F, ((n : ℝ) - m) ≠ 0 := fun n hn h => by
    have := hF n hn
    rw [show (n : ℝ) = m by linarith] at this
    linarith
  -- the remainder of the expansion
  set r : ℤ → ℝ := fun n => (tau M L n - τm) * (n : ℝ) ^ K / ((m : ℝ) ^ K * ((n : ℝ) - m))
  have hr : ∀ n ∈ F, |r n| ≤ 2 * T * R ^ K / (|(m : ℝ)| ^ K * (|(m : ℝ)| - R)) := fun n hnF => by
    have hn := hF n hnF
    have hdist : |(m : ℝ)| - R ≤ |(n : ℝ) - m| := by
      have := abs_sub_abs_le_abs_sub (m : ℝ) n
      rw [abs_sub_comm] at this
      linarith
    have hτ : |tau M L n - τm| ≤ 2 * T := (abs_sub _ _).trans (by linarith [hT n, hT m])
    simp only [r]
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_pow]
    have hden : 0 < |(m : ℝ)| ^ K * (|(m : ℝ)| - R) := by positivity
    rw [div_le_div_iff₀ (mul_pos (pow_pos hmpos K) (abs_pos.mpr (hnm n hnF))) hden]
    calc |tau M L n - τm| * |(n : ℝ)| ^ K * (|(m : ℝ)| ^ K * (|(m : ℝ)| - R))
        ≤ 2 * T * R ^ K * (|(m : ℝ)| ^ K * (|(m : ℝ)| - R)) := by
          gcongr
      _ ≤ 2 * T * R ^ K * (|(m : ℝ)| ^ K * |(n : ℝ) - m|) := by gcongr
  -- expansion of each divided difference
  have hd : ∀ n ∈ F, ((tau M L n - τm) / (n - m) : ℝ) =
      -∑ j ∈ Finset.range K, (1 / (m : ℝ) ^ (j + 1)) * ((tau M L n - τm) * (n : ℝ) ^ j) + r n :=
    fun n hn => by
      rw [div_eq_mul_one_div, inv_sub_expand K hm0 (hnm n hn), mul_add, mul_neg, Finset.mul_sum]
      simp only [r]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      · ring
  have hsum : ∑ n ∈ F, a n * (((tau M L n - τm) / (n - m) : ℝ) : ℂ) =
      -∑ j ∈ Finset.range K, ((1 / (m : ℝ) ^ (j + 1) : ℝ) : ℂ) *
        ((∑ n ∈ F, a n * ((tau M L n * (n : ℝ) ^ j : ℝ) : ℂ)) -
          (τm : ℂ) * ∑ n ∈ F, a n * (((n : ℝ) ^ j : ℝ) : ℂ)) +
        ∑ n ∈ F, a n * ((r n : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun n hn => by rw [hd n hn]]
    simp only [Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul,
      mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [crossRow_off M hL a hmF, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_pos hL Real.pi_pos).le, hsum]
  refine mul_le_mul_of_nonneg_left ?_ (div_pos hL Real.pi_pos).le
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_one, abs_pow,
      div_mul_eq_mul_div, one_mul]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hT m
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ F, ‖a n * ((r n : ℝ) : ℂ)‖
        ≤ ∑ n ∈ F, ‖a n‖ * (2 * T * R ^ K / (|(m : ℝ)| ^ K * (|(m : ℝ)| - R))) :=
          Finset.sum_le_sum fun n hn => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hr n hn) (norm_nonneg _)
      _ = 2 * T * R ^ K * (∑ n ∈ F, ‖a n‖) / (|(m : ℝ)| ^ K * (|(m : ℝ)| - R)) := by
          rw [← Finset.sum_mul]
          ring

theorem sum_Ioc_telescope {f g : ℕ → ℝ} {NP N : ℕ} (hNP : NP ≤ N)
    (h : ∀ k, NP < k → f k ≤ g (k - 1) - g k) : ∑ k ∈ Finset.Ioc NP N, f k ≤ g NP - g N := by
  induction N, hNP using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN]
    have := h (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linarith

/-- `Σ_{NP<k≤N} k^{-(q+2)} ≤ NP^{-(q+1)}`. -/
theorem sum_Ioc_inv_pow_le (q : ℕ) {NP : ℕ} (hNP : 1 ≤ NP) (N : ℕ) :
    ∑ k ∈ Finset.Ioc NP N, 1 / (k : ℝ) ^ (q + 2) ≤ 1 / (NP : ℝ) ^ (q + 1) := by
  have hNP' : (1 : ℝ) ≤ NP := by exact_mod_cast hNP
  rcases le_or_gt NP N with hN | hN
  · set g : ℕ → ℝ := fun k => 1 / ((NP : ℝ) ^ q * k)
    have h := sum_Ioc_telescope (f := fun k => 1 / (k : ℝ) ^ (q + 2)) (g := g) hN fun k hk => by
      have hk1 : (1 : ℝ) ≤ k - 1 := by
        have : NP + 1 ≤ k := hk
        have : ((NP + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
        push_cast at this
        linarith
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      simp only [g, hcast]
      have hk0 : (0 : ℝ) < k := by linarith
      have hpow : (NP : ℝ) ^ q ≤ (k : ℝ) ^ q := pow_le_pow_left₀ (by positivity) (by
        have : NP ≤ k := by omega
        exact_mod_cast this) q
      have hq : 0 < (NP : ℝ) ^ q := by positivity
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      have e : (1 * ((NP : ℝ) ^ q * k) - (NP : ℝ) ^ q * (k - 1) * 1) = (NP : ℝ) ^ q := by ring
      rw [e, pow_add]
      have h3 : (NP : ℝ) ^ q * (k * (k - 1)) ≤ (k : ℝ) ^ q * (k : ℝ) ^ 2 :=
        mul_le_mul hpow (by nlinarith) (by nlinarith) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left h3 hq.le]
    have hgN : 0 ≤ g N := by
      simp only [g]
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      positivity
    have hg : g NP = 1 / (NP : ℝ) ^ (q + 1) := by
      simp only [g]
      rw [pow_succ]
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- `Σ_{NP<k≤N} 1/(k^{2K} (k − R)²) ≤ 1/(NP^{2K} (NP − R))` for `R < NP`. -/
theorem sum_Ioc_shift_le {R NP : ℕ} (hRNP : R < NP) (K N : ℕ) :
    ∑ k ∈ Finset.Ioc NP N, 1 / ((k : ℝ) ^ (2 * K) * ((k : ℝ) - R) ^ 2) ≤
      1 / ((NP : ℝ) ^ (2 * K) * ((NP : ℝ) - R)) := by
  have hR : (R : ℝ) + 1 ≤ NP := by exact_mod_cast hRNP
  have hNP0 : (0 : ℝ) < NP := by have : (0 : ℝ) ≤ R := Nat.cast_nonneg R; linarith
  rcases le_or_gt NP N with hN | hN
  · set g : ℕ → ℝ := fun k => 1 / ((NP : ℝ) ^ (2 * K) * ((k : ℝ) - R))
    have h := sum_Ioc_telescope (f := fun k => 1 / ((k : ℝ) ^ (2 * K) * ((k : ℝ) - R) ^ 2))
        (g := g) hN fun k hk => by
      have hk1 : (NP : ℝ) + 1 ≤ k := by
        have : NP + 1 ≤ k := hk
        exact_mod_cast this
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      simp only [g, hcast]
      have ha : (0 : ℝ) < k - 1 - R := by linarith
      have hb : (0 : ℝ) < k - R := by linarith
      have hpow : (NP : ℝ) ^ (2 * K) ≤ (k : ℝ) ^ (2 * K) :=
        pow_le_pow_left₀ hNP0.le (by linarith) _
      have hq : 0 < (NP : ℝ) ^ (2 * K) := by positivity
      have hk0 : (0 : ℝ) < k := by linarith
      rw [div_sub_div _ _ (mul_pos hq ha).ne' (mul_pos hq hb).ne',
        div_le_div_iff₀ (mul_pos (pow_pos hk0 _) (pow_pos hb 2))
          (mul_pos (mul_pos hq ha) (mul_pos hq hb))]
      have e : (1 * ((NP : ℝ) ^ (2 * K) * (k - R)) - (NP : ℝ) ^ (2 * K) * (k - 1 - R) * 1) =
          (NP : ℝ) ^ (2 * K) := by ring
      rw [e]
      have h1 : (k - 1 - (R : ℝ)) * (k - R) ≤ (k - R) ^ 2 := by nlinarith
      have h2 := mul_le_mul hpow h1 (by positivity) (by positivity)
      nlinarith [h2]
    have hgN : 0 ≤ g N := by
      simp only [g]
      have : (NP : ℝ) ≤ N := by exact_mod_cast hN
      have : (0 : ℝ) ≤ N - R := by linarith
      positivity
    have hg : g NP = 1 / ((NP : ℝ) ^ (2 * K) * ((NP : ℝ) - R)) := rfl
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have : (0 : ℝ) < NP - R := by linarith
    positivity

/-- A sum over `|m| > NP` in `[−N, N]` of a function of `|m|` is twice a sum over `(NP, N]`. -/
theorem sum_int_tail_le {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (NP N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), φ m.natAbs ≤
      2 * ∑ k ∈ Finset.Ioc NP N, φ k := by
  set A := (Finset.Ioc NP N).image (fun k : ℕ => (k : ℤ))
  set B := (Finset.Ioc NP N).image (fun k : ℕ => -(k : ℤ))
  have hsub : (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs) ⊆ A ∪ B := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hk : m.natAbs ∈ Finset.Ioc NP N := by
      rw [Finset.mem_Ioc]
      omega
    rcases Int.natAbs_eq m with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hk, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hk, h.symm⟩)
  have hA : ∑ m ∈ A, φ m.natAbs = ∑ k ∈ Finset.Ioc NP N, φ k := by
    rw [Finset.sum_image fun x _ y _ h => by exact_mod_cast h]
    simp
  have hB : ∑ m ∈ B, φ m.natAbs = ∑ k ∈ Finset.Ioc NP N, φ k := by
    rw [Finset.sum_image fun x _ y _ h => by simpa using h]
    simp
  calc ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), φ m.natAbs
      ≤ ∑ m ∈ A ∪ B, φ m.natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hφ _
    _ ≤ ∑ m ∈ A ∪ B, φ m.natAbs + ∑ m ∈ A ∩ B, φ m.natAbs :=
        le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => hφ _)
    _ = 2 * ∑ k ∈ Finset.Ioc NP N, φ k := by
        rw [Finset.sum_union_inter, hA, hB]
        ring

/-- The explicit tail bound for the rows `|m| > NP` (order-`K` expansion, `|τ| ≤ T`,
`F ⊆ [−R, R]`). -/
def rowTail (M : ℕ) (L : ℝ) (F : Finset ℤ) (a : ℤ → ℂ) (K : ℕ) (T : ℝ) (R NP : ℕ) : ℝ :=
  (L / Real.pi) ^ 2 * (2 * K * ∑ j ∈ Finset.range K,
      (‖∑ n ∈ F, a n * ((tau M L n * (n : ℝ) ^ j : ℝ) : ℂ)‖ +
        T * ‖∑ n ∈ F, a n * (((n : ℝ) ^ j : ℝ) : ℂ)‖) ^ 2 * (2 / (NP : ℝ) ^ (2 * j + 1)) +
    2 * (2 * T * R ^ K * ∑ n ∈ F, ‖a n‖) ^ 2 * (2 / ((NP : ℝ) ^ (2 * K) * ((NP : ℝ) - R))))

open AEGIS.CvSCrossCertV1 in
/-- **The tail of the rows.** -/
theorem rows_tail_le (M : ℕ) {L : ℝ} (hL : 0 < L) {F : Finset ℤ} {R NP : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP) (a : ℤ → ℂ) (K : ℕ) {T : ℝ}
    (hT : ∀ k, |tau M L k| ≤ T) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
        ‖crossRow M L F a m‖ ^ 2 ≤ rowTail M L F a K T R NP := by
  set c : ℕ → ℝ := fun j => ‖∑ n ∈ F, a n * ((tau M L n * (n : ℝ) ^ j : ℝ) : ℂ)‖ +
    T * ‖∑ n ∈ F, a n * (((n : ℝ) ^ j : ℝ) : ℂ)‖ with hc
  set D := 2 * T * R ^ K * ∑ n ∈ F, ‖a n‖ with hD
  set φ : ℕ → ℕ → ℝ := fun j k => 1 / (k : ℝ) ^ (2 * j + 2)
  set ψ : ℕ → ℝ := fun k => 1 / ((k : ℝ) ^ (2 * K) * ((k : ℝ) - R) ^ 2)
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hNP1 : 1 ≤ NP := by omega
  have hpt : ∀ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs),
      ‖crossRow M L F a m‖ ^ 2 ≤ (L / Real.pi) ^ 2 *
        (2 * K * ∑ j ∈ Finset.range K, c j ^ 2 * φ j m.natAbs + 2 * D ^ 2 * ψ m.natAbs) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hx : |(m : ℝ)| = (m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hxR : (R : ℝ) < |(m : ℝ)| := by
      rw [hx]
      have : R < m.natAbs := by omega
      exact_mod_cast this
    have hx0 : 0 < |(m : ℝ)| := lt_of_le_of_lt hR0 hxR
    have h := crossRow_tail_le M hL hF a K hT hxR
    set X := ∑ j ∈ Finset.range K, c j / |(m : ℝ)| ^ (j + 1)
    set Y := D / (|(m : ℝ)| ^ K * (|(m : ℝ)| - R))
    have hXY : ‖crossRow M L F a m‖ ≤ L / Real.pi * (X + Y) := h
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => by
      have : 0 ≤ c j := by simp only [c]; positivity
      positivity
    have hY0 : 0 ≤ Y := by
      have : 0 ≤ D := by simp only [D]; positivity
      have : 0 < |(m : ℝ)| - R := by linarith
      positivity
    have hX2 : X ^ 2 ≤ K * ∑ j ∈ Finset.range K, c j ^ 2 * φ j m.natAbs := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range K)
        (f := fun j => c j / |(m : ℝ)| ^ (j + 1))
      rw [Finset.card_range] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [φ, ← hx]
      rw [div_pow, ← pow_mul]
      ring
    have hY2 : Y ^ 2 = D ^ 2 * ψ m.natAbs := by
      have hg : ∀ d x r : ℝ,
          (d / (x ^ K * (x - r))) ^ 2 = d ^ 2 * (1 / (x ^ (2 * K) * (x - r) ^ 2)) :=
        fun d x r => by rw [div_pow, mul_pow, ← pow_mul, mul_comm K 2, mul_one_div]
      simp only [Y, ψ, ← hx]
      exact hg _ _ _
    calc ‖crossRow M L F a m‖ ^ 2 ≤ (L / Real.pi * (X + Y)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hXY 2
      _ = (L / Real.pi) ^ 2 * (X + Y) ^ 2 := by ring
      _ ≤ (L / Real.pi) ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) := by
          gcongr
          nlinarith [sq_nonneg (X - Y)]
      _ ≤ (L / Real.pi) ^ 2 *
          (2 * (K * ∑ j ∈ Finset.range K, c j ^ 2 * φ j m.natAbs) + 2 * (D ^ 2 * ψ m.natAbs)) := by
          rw [← hY2]
          gcongr
      _ = _ := by ring
  have hφ0 : ∀ j k, 0 ≤ φ j k := fun j k => by simp only [φ]; positivity
  have hψ0 : ∀ k, 0 ≤ ψ k := fun k => by simp only [ψ]; positivity
  have hsφ : ∀ j, ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), φ j m.natAbs ≤
      2 / (NP : ℝ) ^ (2 * j + 1) := fun j => by
    refine (sum_int_tail_le (hφ0 j) NP N).trans ?_
    have := sum_Ioc_inv_pow_le (2 * j) hNP1 N
    simp only [φ]
    rw [div_eq_mul_one_div (2 : ℝ)]
    linarith
  have hsψ : ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), ψ m.natAbs ≤
      2 / ((NP : ℝ) ^ (2 * K) * ((NP : ℝ) - R)) := by
    refine (sum_int_tail_le hψ0 NP N).trans ?_
    have := sum_Ioc_shift_le hRNP K N
    simp only [ψ]
    rw [div_eq_mul_one_div (2 : ℝ)]
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, rowTail]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity))
    (mul_le_mul_of_nonneg_left hsψ (by positivity))
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hsφ j) (sq_nonneg _)

/-- **Splitting the rows**: the rows with `|m| ≤ NP` plus the tail, where the atoms vanish. -/
theorem rows_split {y z : ℤ → ℂ} {NP : ℕ} (hz : ∀ m : ℤ, NP < m.natAbs → z m = 0) (N : ℕ) :
    ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ‖y m - z m‖ ^ 2 ≤
      ∑ m ∈ Finset.Icc (-(NP : ℤ)) NP, ‖y m - z m‖ ^ 2 +
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => NP < m.natAbs), ‖y m‖ ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(N : ℤ)) N) (fun m => NP < m.natAbs),
    add_comm]
  refine add_le_add ?_ (le_of_eq (Finset.sum_congr rfl fun m hm => ?_))
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ => sq_nonneg _
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt] at hm
    simp only [Finset.mem_Icc]
    omega
  · rw [hz m (Finset.mem_filter.mp hm).2, sub_zero]

/-- The explicit bound on `τ`. -/
def tauBound (M : ℕ) : ℝ :=
  4 * Real.pi * (1 + Real.pi / 4) + Real.pi * ∑ j ∈ Finset.range M, |ppw j|

/-- At order zero the actual row-tail budget is an inverse-gap bound. -/
theorem rowTail_zero (M : ℕ) (L : ℝ) (F : Finset ℤ) (a : ℤ → ℂ)
    (T : ℝ) (R NP : ℕ) :
    rowTail M L F a 0 T R NP =
      16 * (L / Real.pi) ^ 2 * T ^ 2 * (∑ n ∈ F, ‖a n‖) ^ 2 /
        ((NP : ℝ) - R) := by
  simp only [rowTail, Nat.cast_zero, Finset.range_zero, Finset.sum_empty,
    mul_zero, pow_zero, mul_one, one_mul, zero_add]
  ring

open AEGIS.CvSCrossCertV1 in
/-- A single cutoff bounds every later actual cross-row tail for all coefficient
vectors on the fixed frequency range. The bound is relative to squared `l1`
mass, and the cutoff may depend on `M`, `L`, `R`, and `ε`. -/
theorem exists_uniform_rows_tail_cutoff (M : ℕ) {L : ℝ} (hL : 0 < L)
    (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ NP : ℕ, R < NP ∧ ∀ P : ℕ, NP ≤ P →
      ∀ (F : Finset ℤ), (∀ n ∈ F, |(n : ℝ)| ≤ R) →
      ∀ (a : ℤ → ℂ) (N : ℕ),
        (∑ m ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun m => P < m.natAbs),
          ‖crossRow M L F a m‖ ^ 2) ≤ ε * (∑ n ∈ F, ‖a n‖) ^ 2 := by
  have hC : 0 ≤ 16 * (L / Real.pi) ^ 2 * tauBound M ^ 2 := by positivity
  obtain ⟨NP, hNP, hcut⟩ :=
    AEGIS.CvSResidualCertificateV1.exists_uniform_shifted_cutoff
      (16 * (L / Real.pi) ^ 2 * tauBound M ^ 2) hC R ε hε
  refine ⟨NP, hNP, fun P hP F hF a N => ?_⟩
  have hRP : R < P := lt_of_lt_of_le hNP hP
  calc
    _ ≤ rowTail M L F a 0 (tauBound M) R P :=
      rows_tail_le M hL hF hRP a 0 (fun k => tau_abs_le M hL k) N
    _ = (16 * (L / Real.pi) ^ 2 * tauBound M ^ 2 / ((P : ℝ) - R)) *
        (∑ n ∈ F, ‖a n‖) ^ 2 := by rw [rowTail_zero]; ring
    _ ≤ ε * (∑ n ∈ F, ‖a n‖) ^ 2 :=
      mul_le_mul_of_nonneg_right (hcut P hP).le (sq_nonneg _)

open AEGIS.CvSCrossCertV1 in
/-- **`window_of_certificate_rows` with finitely many rows and the explicit tail.** The rows
`|m| ≤ NP` and the tail `rowTail` (order-`K` expansion, `|τ| ≤ tauBound M`) bound the cross block,
where `R ≥ |ι_i| + 1` bounds the low frequencies and `R < NP`. -/
theorem window_of_certificate_tail (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
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
    (R NP K : ℕ) (hRι : ∀ i, |ι i| + 1 ≤ (R : ℤ)) (hRNP : R < NP)
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2) +
      rowTail M LT (lowFreq fun i => sinSqSupport (ι i))
        (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) K
        (tauBound M) R NP ≤ Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  set S : Fin p → Finset ℤ := fun i => sinSqSupport (ι i)
  set β : Fin p → ℤ → ℂ := fun i => sinSqWeight (ι i)
  have hF : ∀ n ∈ lowFreq S, |(n : ℝ)| ≤ R := by
    intro n hn
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hn
    have hn' : n = ι i - 1 ∨ n = ι i ∨ n = ι i + 1 := by
      simpa [S, sinSqSupport] using hi
    have h1 := hRι i
    have h2 := neg_abs_le (ι i)
    have h3 := le_abs_self (ι i)
    have hz : |n| ≤ (R : ℤ) := by
      rw [abs_le]
      rcases hn' with h | h | h <;> subst h <;> constructor <;> linarith
    have := (Int.cast_le (R := ℝ)).mpr hz
    rwa [Int.cast_abs, Int.cast_natCast] at this
  have hτ : ∀ k, |tau M LT k| ≤ tauBound M := fun k => tau_abs_le M hLT0 k
  refine window_of_certificate_rows M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos lam Brow (fun c N => ?_) hlow g hm r a hw h2r
  have hz : ∀ x : ℤ, NP < x.natAbs → ∑ i, lam c i * atomRow LT S β i x = 0 := by
    intro x hx
    have hxF : x ∉ lowFreq S := fun h => by
      have h1 := hF x h
      have h2 : |(x : ℝ)| = (x.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      have h3 : (NP : ℝ) < x.natAbs := by exact_mod_cast hx
      have h4 : (R : ℝ) < NP := by exact_mod_cast hRNP
      linarith
    exact Finset.sum_eq_zero fun i _ => by rw [atomRow, lowCoeff_eq_zero LT S β _ hxF, mul_zero]
  refine (rows_split hz N).trans ?_
  refine le_trans (add_le_add le_rfl ?_) (hfin c)
  exact rows_tail_le M hLT0 hF hRNP _ K hτ N

end AEGIS.CvSRowTailV1

#print axioms AEGIS.CvSRowTailV1.cvsEntry_off
#print axioms AEGIS.CvSRowTailV1.cvsEntry_symm
#print axioms AEGIS.CvSRowTailV1.tsum_abs_width_le
#print axioms AEGIS.CvSRowTailV1.source_integral_abs_le
#print axioms AEGIS.CvSRowTailV1.tau_abs_le
#print axioms AEGIS.CvSRowTailV1.crossRow_off
#print axioms AEGIS.CvSRowTailV1.inv_sub_expand
#print axioms AEGIS.CvSRowTailV1.crossRow_tail_le
#print axioms AEGIS.CvSRowTailV1.sum_Ioc_inv_pow_le
#print axioms AEGIS.CvSRowTailV1.sum_Ioc_shift_le
#print axioms AEGIS.CvSRowTailV1.sum_int_tail_le
#print axioms AEGIS.CvSRowTailV1.rows_tail_le
#print axioms AEGIS.CvSRowTailV1.rows_split
#print axioms AEGIS.CvSRowTailV1.window_of_certificate_tail
#check @AEGIS.CvSRowTailV1.rowTail_zero
#check @AEGIS.CvSRowTailV1.exists_uniform_rows_tail_cutoff
#print axioms AEGIS.CvSRowTailV1.rowTail_zero
#print axioms AEGIS.CvSRowTailV1.exists_uniform_rows_tail_cutoff
