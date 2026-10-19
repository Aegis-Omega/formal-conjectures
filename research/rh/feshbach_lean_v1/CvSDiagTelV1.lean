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

/-!
# Telescoped tails of the digamma and trigamma series (CvS step 7f)

With `z_k = c_k + ir`, `c_k = 2k + 1/2`:

* `log_step_bound`: `log‖z+1‖ − log‖z−1‖ = Re(2/z + (2/3)/z³) + O(‖z‖⁻⁵)` from the Taylor series of
  `log(1 ± 1/z)`; `cube_tel`, `sq_tel`: exact second-order telescoping identities for `z⁻³`, `z⁻²`.
* `tail_limit`: if `|x_k − (g_k − g_{k+1})| ≤ h_k − h_{k+1}` for `k ≥ K`, `g → 0` and the partial sums
  of `x_{K+i}` converge to `ℓ`, then `|ℓ − g_K| ≤ h_K`.
* `hplus_limit`: `h₊(r) + log π = lim_N (log N − Σ_{k<N} 2c_k/(c_k² + r²))` (no Euler constant left).
* `hplus_tel`: for `K ≥ 10`, `a = c_K − 1`,
  `h₊(r) + log π = −Σ_{k<K} 2c_k/(c_k²+r²) + log(a²+r²)/2 − log 2 + (a²−r²)/(6(a²+r²)²) ± 1/(4a⁴)`.
* `diagSeries_tel`: `Σ_k (1 − e^{−c_k L})(c_k² − r²)/(c_k² + r²)²` equals its head over `k < K` plus
  `a/(2(a²+r²)) − (a³ − 3ar²)/(6(a²+r²)³)` up to `1/(4a⁵) + e^{−c_K L}/(2a)`.

These give the archimedean part of the diagonal entries `cvsEntry M L n n`
(`CvSQuadV1.hplus_cosB_diag`) for any window. Not RH.
-/

open Finset Filter Topology Complex

namespace AEGIS.CvSDiagTelV1

open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1

/-- **One logarithmic step.** For `‖z‖ > 1`,
`|log‖z+1‖ − log‖z−1‖ − Re(2/z + (2/3)/z³)| ≤ (2/5)‖1/z‖⁵/(1 − ‖1/z‖)`. -/
theorem log_step_bound {z : ℂ} (hz : 1 < ‖z‖) :
    |Real.log ‖z + 1‖ - Real.log ‖z - 1‖ - (2 * z⁻¹ + 2 / 3 * z⁻¹ ^ 3).re| ≤
      2 / 5 * ‖z⁻¹‖ ^ 5 / (1 - ‖z⁻¹‖) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  set w := z⁻¹ with hw
  have hwn : ‖w‖ < 1 := by rw [hw, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have h := (Complex.hasSum_taylorSeries_log hwn).add (Complex.hasSum_taylorSeries_neg_log hwn)
  have hs := (hasSum_nat_add_iff' 5).mpr h
  have hhead : ∑ i ∈ range 5, ((-1 : ℂ) ^ (i + 1) * w ^ i / (i : ℂ) + w ^ i / (i : ℂ)) =
      2 * w + 2 / 3 * w ^ 3 := by
    simp only [sum_range_succ, sum_range_zero]
    push_cast
    ring
  rw [hhead] at hs
  have hg := (hasSum_geometric_of_lt_one (norm_nonneg w) hwn).mul_left (2 / 5 * ‖w‖ ^ 5)
  have hb := hs.norm_le_of_bounded hg fun n => by
    have hn : (5 : ℝ) ≤ ((n + 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ n + 5)
    have hn0 : (0 : ℝ) < ((n + 5 : ℕ) : ℝ) := by linarith
    calc ‖(-1 : ℂ) ^ (n + 5 + 1) * w ^ (n + 5) / ((n + 5 : ℕ) : ℂ) + w ^ (n + 5) / ((n + 5 : ℕ) : ℂ)‖
        ≤ ‖(-1 : ℂ) ^ (n + 5 + 1) * w ^ (n + 5) / ((n + 5 : ℕ) : ℂ)‖ +
          ‖w ^ (n + 5) / ((n + 5 : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = 2 * (‖w‖ ^ (n + 5) / ((n + 5 : ℕ) : ℝ)) := by
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          ring
      _ ≤ 2 * (‖w‖ ^ (n + 5) / 5) := by
          gcongr
      _ = 2 / 5 * ‖w‖ ^ 5 * ‖w‖ ^ n := by ring
  have hre : (Complex.log (1 + w) + -Complex.log (1 - w)).re =
      Real.log ‖z + 1‖ - Real.log ‖z - 1‖ := by
    have e1 : 1 + w = (z + 1) / z := by rw [hw]; field_simp
    have e2 : 1 - w = (z - 1) / z := by rw [hw]; field_simp
    have hp : z + 1 ≠ 0 := by
      intro h0
      have : ‖z‖ = 1 := by rw [show z = -1 by linear_combination h0]; simp
      linarith
    have hm : z - 1 ≠ 0 := by
      intro h0
      have : ‖z‖ = 1 := by rw [show z = 1 by linear_combination h0]; simp
      linarith
    rw [Complex.add_re, Complex.neg_re, Complex.log_re, Complex.log_re, e1, e2, norm_div, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hz0),
      Real.log_div (norm_ne_zero_iff.mpr hm) (norm_ne_zero_iff.mpr hz0)]
    ring
  calc |Real.log ‖z + 1‖ - Real.log ‖z - 1‖ - (2 * w + 2 / 3 * w ^ 3).re|
      = |(Complex.log (1 + w) + -Complex.log (1 - w) - (2 * w + 2 / 3 * w ^ 3)).re| := by
        rw [Complex.sub_re, hre]
    _ ≤ ‖Complex.log (1 + w) + -Complex.log (1 - w) - (2 * w + 2 / 3 * w ^ 3)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 2 / 5 * ‖w‖ ^ 5 * (1 - ‖w‖)⁻¹ := hb
    _ = 2 / 5 * ‖w‖ ^ 5 / (1 - ‖w‖) := by ring

theorem ne_of_one_lt {z : ℂ} (hz : 1 < ‖z‖) : z ≠ 0 ∧ z - 1 ≠ 0 ∧ z + 1 ≠ 0 ∧ z ^ 2 - 1 ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, norm_zero] at hz; linarith
  · rw [show z = 1 by linear_combination h, norm_one] at hz; linarith
  · rw [show z = -1 by linear_combination h, norm_neg, norm_one] at hz; linarith
  · have : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, show z ^ 2 = 1 by linear_combination h, norm_one]
    nlinarith

/-- The second-order telescoping identity for `z⁻³`. -/
theorem cube_tel {z : ℂ} (hz : 1 < ‖z‖) :
    2 / 3 * z⁻¹ ^ 3 = 1 / 6 * ((z - 1)⁻¹ ^ 2 - (z + 1)⁻¹ ^ 2) -
      2 / 3 * ((2 * z ^ 2 - 1) / (z ^ 3 * (z ^ 2 - 1) ^ 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := ne_of_one_lt hz
  field_simp
  ring

/-- The telescoping identity for `z⁻²`. -/
theorem sq_tel {z : ℂ} (hz : 1 < ‖z‖) :
    z⁻¹ ^ 2 = 1 / 2 * ((z - 1)⁻¹ - (z + 1)⁻¹) - 1 / 6 * ((z - 1)⁻¹ ^ 3 - (z + 1)⁻¹ ^ 3) -
      (6 - 14 * z ^ 2) / (6 * z ^ 2 * (z ^ 2 - 1) ^ 3) := by
  obtain ⟨h0, h1, h2, h3⟩ := ne_of_one_lt hz
  field_simp
  ring

theorem norm_sq_sub_one_ge (z : ℂ) : ‖z‖ ^ 2 - 1 ≤ ‖z ^ 2 - 1‖ := by
  have := norm_sub_norm_le (z ^ 2) 1
  rwa [norm_pow, norm_one] at this

theorem cube_rem_le {z : ℂ} (hz : 20 ≤ ‖z‖) :
    ‖2 / 3 * ((2 * z ^ 2 - 1) / (z ^ 3 * (z ^ 2 - 1) ^ 2))‖ ≤ 3 / 2 / ‖z‖ ^ 5 := by
  have ht : 0 < ‖z‖ := by linarith
  have hd := norm_sq_sub_one_ge z
  have hd0 : 0 < ‖z‖ ^ 2 - 1 := by nlinarith
  have hn : ‖2 * z ^ 2 - 1‖ ≤ 2 * ‖z‖ ^ 2 + 1 := by
    calc ‖2 * z ^ 2 - 1‖ ≤ ‖2 * z ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖z‖ ^ 2 + 1 := by simp [norm_pow]
  rw [norm_mul, show ‖(2 / 3 : ℂ)‖ = 2 / 3 by norm_num, norm_div, norm_mul, norm_pow, norm_pow]
  have hpos : 0 < ‖z‖ ^ 3 * (‖z‖ ^ 2 - 1) ^ 2 := by positivity
  calc 2 / 3 * (‖2 * z ^ 2 - 1‖ / (‖z‖ ^ 3 * ‖z ^ 2 - 1‖ ^ 2))
      ≤ 2 / 3 * ((2 * ‖z‖ ^ 2 + 1) / (‖z‖ ^ 3 * (‖z‖ ^ 2 - 1) ^ 2)) := by gcongr
    _ ≤ 3 / 2 / ‖z‖ ^ 5 := by
        rw [mul_div_assoc', div_le_div_iff₀ hpos (by positivity)]
        nlinarith [sq_nonneg (‖z‖ ^ 2 - 22), pow_pos ht 3, pow_pos ht 5]

theorem sq_rem_le {z : ℂ} (hz : 20 ≤ ‖z‖) :
    ‖(6 - 14 * z ^ 2) / (6 * z ^ 2 * (z ^ 2 - 1) ^ 3)‖ ≤ 5 / 2 / ‖z‖ ^ 6 := by
  have ht : 0 < ‖z‖ := by linarith
  have hd := norm_sq_sub_one_ge z
  have hd0 : 0 < ‖z‖ ^ 2 - 1 := by nlinarith
  have hn : ‖6 - 14 * z ^ 2‖ ≤ 14 * ‖z‖ ^ 2 + 6 := by
    calc ‖6 - 14 * z ^ 2‖ ≤ ‖(6 : ℂ)‖ + ‖14 * z ^ 2‖ := norm_sub_le _ _
      _ = 14 * ‖z‖ ^ 2 + 6 := by simp [norm_pow]; ring
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, show ‖(6 : ℂ)‖ = 6 by norm_num]
  have hpos : 0 < 6 * ‖z‖ ^ 2 * (‖z‖ ^ 2 - 1) ^ 3 := by positivity
  calc ‖6 - 14 * z ^ 2‖ / (6 * ‖z‖ ^ 2 * ‖z ^ 2 - 1‖ ^ 3)
      ≤ (14 * ‖z‖ ^ 2 + 6) / (6 * ‖z‖ ^ 2 * (‖z‖ ^ 2 - 1) ^ 3) := by gcongr
    _ ≤ 5 / 2 / ‖z‖ ^ 6 := by
        rw [div_le_div_iff₀ hpos (by positivity)]
        have h51 : (0 : ℝ) < ‖z‖ ^ 2 - 51 := by nlinarith
        nlinarith [pow_pos ht 2, pow_pos ht 4, pow_pos ht 6, pow_pos ht 8,
          mul_pos (pow_pos ht 4) h51]

/-! ### A telescoping tail with a limit -/

theorem tail_limit {x g h : ℕ → ℝ} {K : ℕ} {ℓ : ℝ}
    (hx : ∀ k, K ≤ k → |x k - (g k - g (k + 1))| ≤ h k - h (k + 1))
    (hg : Tendsto g atTop (𝓝 0)) (hh : ∀ k, K ≤ k → 0 ≤ h k)
    (hP : Tendsto (fun m => ∑ i ∈ range m, x (K + i)) atTop (𝓝 ℓ)) :
    |ℓ - g K| ≤ h K := by
  have hm : ∀ m, |(∑ i ∈ range m, x (K + i)) - (g K - g (K + m))| ≤ h K := by
    intro m
    have eg : ∑ i ∈ range m, (g (K + i) - g (K + i + 1)) = g K - g (K + m) := by
      simpa [add_assoc] using sum_range_sub' (fun i => g (K + i)) m
    have e1 : (∑ i ∈ range m, x (K + i)) - (g K - g (K + m)) =
        ∑ i ∈ range m, (x (K + i) - (g (K + i) - g (K + i + 1))) := by
      rw [sum_sub_distrib, eg]
    have e2 : ∑ i ∈ range m, (h (K + i) - h (K + i + 1)) = h K - h (K + m) := by
      simpa [add_assoc] using sum_range_sub' (fun i => h (K + i)) m
    rw [e1]
    calc |∑ i ∈ range m, (x (K + i) - (g (K + i) - g (K + i + 1)))|
        ≤ ∑ i ∈ range m, |x (K + i) - (g (K + i) - g (K + i + 1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range m, (h (K + i) - h (K + i + 1)) :=
          sum_le_sum fun i _ => hx (K + i) (by omega)
      _ = h K - h (K + m) := e2
      _ ≤ h K := by linarith [hh (K + m) (by omega)]
  have hg' : Tendsto (fun m => g (K + m)) atTop (𝓝 0) :=
    (hg.comp (tendsto_add_atTop_nat K)).congr fun m => by simp [Function.comp, add_comm]
  have hlim : Tendsto (fun m => |(∑ i ∈ range m, x (K + i)) - (g K - g (K + m))|) atTop
      (𝓝 |ℓ - (g K - 0)|) := (hP.sub ((tendsto_const_nhds (x := g K)).sub hg')).abs
  rw [sub_zero] at hlim
  exact le_of_tendsto' hlim hm

/-! ### Real parts on the line `a + i r` -/

theorem normSq_line (a r : ℝ) : Complex.normSq ((a : ℂ) + r * I) = a ^ 2 + r ^ 2 := by
  rw [Complex.normSq_add_mul_I]

theorem re_inv_line (a r : ℝ) :
    (((a : ℂ) + r * I)⁻¹).re = a / (a ^ 2 + r ^ 2) := by
  rw [Complex.inv_re, normSq_line]; simp

theorem re_inv_sq_line {a r : ℝ} (ha : 0 < a) :
    ((((a : ℂ) + r * I)⁻¹) ^ 2).re = (a ^ 2 - r ^ 2) / (a ^ 2 + r ^ 2) ^ 2 := by
  have hs : 0 < a ^ 2 + r ^ 2 := by positivity
  rw [pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im, normSq_line]
  simp
  field_simp

theorem re_inv_cube_line {a r : ℝ} (ha : 0 < a) :
    ((((a : ℂ) + r * I)⁻¹) ^ 3).re = (a ^ 3 - 3 * a * r ^ 2) / (a ^ 2 + r ^ 2) ^ 3 := by
  have hs : 0 < a ^ 2 + r ^ 2 := by positivity
  rw [pow_succ, pow_two, Complex.mul_re, Complex.mul_re, Complex.mul_im, Complex.inv_re,
    Complex.inv_im, normSq_line]
  simp
  field_simp
  ring

theorem norm_line_ge {a r : ℝ} (ha : 0 ≤ a) : a ≤ ‖(a : ℂ) + r * I‖ := by
  have := Complex.abs_re_le_norm ((a : ℂ) + r * I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] at this
  rwa [abs_of_nonneg ha] at this

theorem log_norm_line (a r : ℝ) : Real.log ‖(a : ℂ) + r * I‖ = Real.log (a ^ 2 + r ^ 2) / 2 := by
  rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]

/-! ### Elementary telescoping comparisons -/

theorem inv_pow5_le {c : ℝ} (hc : 2 ≤ c) :
    2 / c ^ 5 ≤ 1 / (4 * (c - 1) ^ 4) - 1 / (4 * (c + 1) ^ 4) := by
  have h1 : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : ((c - 1) * (c + 1)) ^ 4 ≤ (c ^ 2) ^ 4 := by
    apply pow_le_pow_left₀ (by nlinarith); nlinarith
  have hexp : 1 * (4 * (c + 1) ^ 4) - 4 * (c - 1) ^ 4 * 1 = 32 * c ^ 3 + 32 * c := by ring
  rw [hexp]
  have : 2 * (4 * (c - 1) ^ 4 * (4 * (c + 1) ^ 4)) = 32 * ((c - 1) * (c + 1)) ^ 4 := by ring
  rw [this]
  have h8 : (c ^ 2) ^ 4 = c ^ 3 * c ^ 5 := by ring
  nlinarith [pow_pos hc0 3, pow_pos hc0 5, mul_pos (pow_pos hc0 5) hc0]

theorem inv_pow6_le {c : ℝ} (hc : 2 ≤ c) :
    5 / 2 / c ^ 6 ≤ 1 / (4 * (c - 1) ^ 5) - 1 / (4 * (c + 1) ^ 5) := by
  have h1 : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : ((c - 1) * (c + 1)) ^ 5 ≤ (c ^ 2) ^ 5 := by
    apply pow_le_pow_left₀ (by nlinarith); nlinarith
  have hexp : 1 * (4 * (c + 1) ^ 5) - 4 * (c - 1) ^ 5 * 1 = 40 * c ^ 4 + 80 * c ^ 2 + 8 := by ring
  rw [hexp]
  have : 5 / 2 * (4 * (c - 1) ^ 5 * (4 * (c + 1) ^ 5)) = 40 * ((c - 1) * (c + 1)) ^ 5 := by ring
  rw [this]
  have h8 : (c ^ 2) ^ 5 = c ^ 4 * c ^ 6 := by ring
  nlinarith [pow_pos hc0 4, pow_pos hc0 6, pow_pos hc0 2]

theorem inv_sq_le {c : ℝ} (hc : 2 ≤ c) : 1 / c ^ 2 ≤ 1 / (2 * (c - 1)) - 1 / (2 * (c + 1)) := by
  have h1 : 0 < c - 1 := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### `h₊` as a limit and its telescoped tail -/

theorem hplus_limit (r : ℝ) :
    Tendsto (fun N : ℕ => Real.log N - ∑ k ∈ range N, 2 * archWidth k / (archWidth k ^ 2 + r ^ 2))
      atTop (𝓝 (hplus r + Real.log Real.pi)) := by
  have h3 := ((archTerm_summable r).hasSum.tendsto_sum_nat).sub Real.tendsto_harmonic_sub_log
  have heq : (∑' k, archTerm k r) - Real.eulerMascheroniConstant = hplus r + Real.log Real.pi := by
    rw [hplus_eq_tsum]; ring
  rw [heq] at h3
  refine h3.congr fun N => ?_
  simp only [archTerm, sum_sub_distrib, harmonic]
  push_cast
  simp only [one_div]
  ring

theorem logG_limit (r : ℝ) :
    Tendsto (fun N : ℕ => Real.log N - Real.log ((archWidth N - 1) ^ 2 + r ^ 2) / 2) atTop
      (𝓝 (-Real.log 2)) := by
  set E : ℝ → ℝ := fun u => (2 - u / 2) ^ 2 + r ^ 2 * u ^ 2 with hE
  have hEc : Continuous E := by fun_prop
  have hE0 : E 0 = 4 := by simp [hE]; norm_num
  have h1 : Tendsto (fun N : ℕ => E (1 / (N : ℝ))) atTop (𝓝 4) := by
    rw [← hE0]; exact (hEc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  have h2 := ((Real.continuousAt_log (by norm_num : (4 : ℝ) ≠ 0)).tendsto.comp h1).const_mul (-1 / 2)
  have h4 : -1 / 2 * Real.log 4 = -Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4] at h2
  refine h2.congr' (Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hEp : 0 < E (1 / (N : ℝ)) := by
    simp only [hE]; nlinarith [sq_nonneg (2 - 1 / (N : ℝ) / 2), sq_nonneg (r * (1 / (N : ℝ))),
      show 1 / (N : ℝ) ≤ 1 from by rw [div_le_one hN0]; exact_mod_cast hN]
  have hid : (archWidth N - 1) ^ 2 + r ^ 2 = (N : ℝ) ^ 2 * E (1 / (N : ℝ)) := by
    simp only [hE, archWidth]; field_simp; ring
  simp only [Function.comp]
  rw [hid, Real.log_mul (by positivity) hEp.ne', Real.log_pow]
  push_cast
  ring

theorem abs_g1_le {a r : ℝ} (ha : 0 < a) :
    |(a ^ 2 - r ^ 2) / (a ^ 2 + r ^ 2) ^ 2 / 6| ≤ 1 / (6 * a ^ 2) := by
  have hs : 0 < a ^ 2 + r ^ 2 := by positivity
  rw [div_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (a ^ 2 + r ^ 2) ^ 2 * 6),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : |a ^ 2 - r ^ 2| ≤ a ^ 2 + r ^ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r]⟩
  nlinarith [sq_nonneg a, sq_nonneg r, mul_nonneg (sq_nonneg a) (sq_nonneg r)]

theorem tendsto_inv_width_sub_one : Tendsto (fun k : ℕ => 1 / (archWidth k - 1)) atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
    (Filter.eventually_atTop.2 ⟨1, fun k hk => ?_⟩) tendsto_one_div_atTop_nhds_zero_nat
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg zero_le_one (by simp [archWidth]; linarith)
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by simp [archWidth]; linarith) (by linarith)]
    simp [archWidth]; linarith

/-- One telescoping step for `h₊` (`log‖z+1‖ − log‖z−1‖` against `2 Re(1/z)`). -/
theorem step_bound (r : ℝ) {k : ℕ} (hk : 10 ≤ k) :
    |(Real.log ((archWidth (k + 1) - 1) ^ 2 + r ^ 2) / 2 -
        Real.log ((archWidth k - 1) ^ 2 + r ^ 2) / 2 - 2 * archWidth k / (archWidth k ^ 2 + r ^ 2)) -
      (((archWidth k - 1) ^ 2 - r ^ 2) / ((archWidth k - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
        ((archWidth (k + 1) - 1) ^ 2 - r ^ 2) / ((archWidth (k + 1) - 1) ^ 2 + r ^ 2) ^ 2 / 6)| ≤
      1 / (4 * (archWidth k - 1) ^ 4) - 1 / (4 * (archWidth (k + 1) - 1) ^ 4) := by
  set c := archWidth k with hc
  have hc20 : 20 ≤ c := by
    simp only [hc, archWidth]; have : (10 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk1 : archWidth (k + 1) - 1 = c + 1 := by simp only [hc, archWidth]; push_cast; ring
  rw [hk1]
  set z : ℂ := (c : ℂ) + r * I with hz
  have ht : c ≤ ‖z‖ := norm_line_ge (by linarith)
  have hz1 : 1 < ‖z‖ := by linarith
  have hzp : z + 1 = ((c + 1 : ℝ) : ℂ) + r * I := by rw [hz]; push_cast; ring
  have hzm : z - 1 = ((c - 1 : ℝ) : ℂ) + r * I := by rw [hz]; push_cast; ring
  have hA := log_step_bound hz1
  have hct := congrArg Complex.re (cube_tel hz1)
  have hB := cube_rem_le (show 20 ≤ ‖z‖ by linarith)
  rw [hzp, hzm, log_norm_line, log_norm_line] at hA
  rw [hzp, hzm] at hct
  have e1 : (2 * z⁻¹ + 2 / 3 * z⁻¹ ^ 3).re = 2 * c / (c ^ 2 + r ^ 2) + (2 / 3 * z⁻¹ ^ 3).re := by
    rw [Complex.add_re, hz, show (2 * ((c : ℂ) + r * I)⁻¹).re = 2 * (((c : ℂ) + r * I)⁻¹).re by
      simp, re_inv_line]; ring
  have e2 : (2 / 3 * z⁻¹ ^ 3).re = ((c - 1) ^ 2 - r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
      ((c + 1) ^ 2 - r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 2 / 6 -
      (2 / 3 * ((2 * z ^ 2 - 1) / (z ^ 3 * (z ^ 2 - 1) ^ 2))).re := by
    rw [hct, Complex.sub_re]
    have e3 : ((1 / 6 : ℂ) * ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 2 -
        (((c + 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 2)).re =
        ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 2).re / 6 - ((((c + 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 2).re / 6 := by
      simp [Complex.sub_re]; ring
    rw [e3, re_inv_sq_line (by linarith), re_inv_sq_line (by linarith)]
  rw [e1, e2] at hA
  set R := (2 / 3 * ((2 * z ^ 2 - 1) / (z ^ 3 * (z ^ 2 - 1) ^ 2))).re
  have hR : |R| ≤ 3 / 2 / ‖z‖ ^ 5 := (Complex.abs_re_le_norm _).trans hB
  have hw : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
  have hzpos : 0 < ‖z‖ := by linarith
  have hA' : 2 / 5 * ‖z⁻¹‖ ^ 5 / (1 - ‖z⁻¹‖) ≤ 1 / 2 / ‖z‖ ^ 5 := by
    rw [hw, inv_pow, div_le_div_iff₀ (by
      have : ‖z‖⁻¹ ≤ 1 / 20 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith) (by positivity)]
    have : ‖z‖⁻¹ ≤ 1 / 20 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h5 : (‖z‖ ^ 5)⁻¹ * ‖z‖ ^ 5 = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith [inv_pos.mpr hzpos, pow_pos hzpos 5]
  have hcz : 2 / ‖z‖ ^ 5 ≤ 2 / c ^ 5 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) ht 5)
  have hfin := inv_pow5_le (show 2 ≤ c by linarith)
  have hsum : |(Real.log ((c + 1) ^ 2 + r ^ 2) / 2 - Real.log ((c - 1) ^ 2 + r ^ 2) / 2 -
      2 * c / (c ^ 2 + r ^ 2)) - (((c - 1) ^ 2 - r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
        ((c + 1) ^ 2 - r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 2 / 6)| ≤ 2 / ‖z‖ ^ 5 := by
    have hrw : (Real.log ((c + 1) ^ 2 + r ^ 2) / 2 - Real.log ((c - 1) ^ 2 + r ^ 2) / 2 -
        2 * c / (c ^ 2 + r ^ 2)) - (((c - 1) ^ 2 - r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
          ((c + 1) ^ 2 - r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 2 / 6) =
        (Real.log ((c + 1) ^ 2 + r ^ 2) / 2 - Real.log ((c - 1) ^ 2 + r ^ 2) / 2 -
          (2 * c / (c ^ 2 + r ^ 2) + (((c - 1) ^ 2 - r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
            ((c + 1) ^ 2 - r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 2 / 6 - R))) - R := by ring
    rw [hrw]
    calc _ ≤ |Real.log ((c + 1) ^ 2 + r ^ 2) / 2 - Real.log ((c - 1) ^ 2 + r ^ 2) / 2 -
          (2 * c / (c ^ 2 + r ^ 2) + (((c - 1) ^ 2 - r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 2 / 6 -
            ((c + 1) ^ 2 - r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 2 / 6 - R))| + |R| := abs_sub _ _
      _ ≤ 1 / 2 / ‖z‖ ^ 5 + 3 / 2 / ‖z‖ ^ 5 := add_le_add (hA.trans hA') hR
      _ = 2 / ‖z‖ ^ 5 := by ring
  exact hsum.trans (hcz.trans hfin)

/-- **`h₊` with an explicit telescoped tail.** For `K ≥ 10` and `a = c_K − 1`,
`h₊(r) + log π = −Σ_{k<K} 2c_k/(c_k² + r²) + log(a² + r²)/2 − log 2 + (a² − r²)/(6(a² + r²)²)`
up to `1/(4a⁴)`. -/
theorem hplus_tel (r : ℝ) {K : ℕ} (hK : 10 ≤ K) :
    |hplus r + Real.log Real.pi -
      (-(∑ k ∈ range K, 2 * archWidth k / (archWidth k ^ 2 + r ^ 2)) +
        Real.log ((archWidth K - 1) ^ 2 + r ^ 2) / 2 - Real.log 2 +
        ((archWidth K - 1) ^ 2 - r ^ 2) / ((archWidth K - 1) ^ 2 + r ^ 2) ^ 2 / 6)| ≤
      1 / (4 * (archWidth K - 1) ^ 4) := by
  set S : ℕ → ℝ := fun N => ∑ k ∈ range N, 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) with hS
  set G : ℕ → ℝ := fun k => Real.log ((archWidth k - 1) ^ 2 + r ^ 2) / 2 with hG
  set g : ℕ → ℝ := fun k =>
    ((archWidth k - 1) ^ 2 - r ^ 2) / ((archWidth k - 1) ^ 2 + r ^ 2) ^ 2 / 6 with hg
  set h : ℕ → ℝ := fun k => 1 / (4 * (archWidth k - 1) ^ 4) with hh
  set x : ℕ → ℝ := fun k => G (k + 1) - G k - 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) with hx
  have hxb : ∀ k, K ≤ k → |x k - (g k - g (k + 1))| ≤ h k - h (k + 1) := fun k hk =>
    step_bound r (by omega)
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hlim := tendsto_inv_width_sub_one.const_mul (1 / 6)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨1, fun k hk => ?_⟩) hlim
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ha : 1 ≤ archWidth k - 1 := by simp [archWidth]; linarith
    rw [Real.norm_eq_abs]
    refine (abs_g1_le (by linarith)).trans ?_
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hsplit : ∀ m, ∑ i ∈ range m, x (K + i) =
      (Real.log ((K + m : ℕ) : ℝ) - S (K + m)) - (Real.log ((K + m : ℕ) : ℝ) - G (K + m)) +
        S K - G K := by
    intro m
    have e1 : ∑ i ∈ range m, (G (K + i + 1) - G (K + i)) = G (K + m) - G K := by
      simpa [add_assoc] using sum_range_sub (fun i => G (K + i)) m
    have e2 : S (K + m) = S K + ∑ i ∈ range m, 2 * archWidth (K + i) / (archWidth (K + i) ^ 2 + r ^ 2) := by
      simp only [hS]; rw [sum_range_add]
    simp only [hx]
    rw [sum_sub_distrib, e1, e2]
    ring
  have hl1 : Tendsto (fun m => Real.log ((K + m : ℕ) : ℝ) - S (K + m)) atTop
      (𝓝 (hplus r + Real.log Real.pi)) := by
    refine ((hplus_limit r).comp (tendsto_add_atTop_nat K)).congr fun m => ?_
    simp only [Function.comp, hS]; rw [Nat.add_comm m K]
  have hl2 : Tendsto (fun m => Real.log ((K + m : ℕ) : ℝ) - G (K + m)) atTop (𝓝 (-Real.log 2)) := by
    refine ((logG_limit r).comp (tendsto_add_atTop_nat K)).congr fun m => ?_
    simp only [Function.comp, hG]; rw [Nat.add_comm m K]
  have hP : Tendsto (fun m => ∑ i ∈ range m, x (K + i)) atTop
      (𝓝 (hplus r + Real.log Real.pi - -Real.log 2 + S K - G K)) :=
    (((hl1.sub hl2).add_const (S K)).sub_const (G K)).congr fun m => (hsplit m).symm
  have key := tail_limit hxb hg0 (fun k _ => by simp only [hh]; positivity) hP
  have e : hplus r + Real.log Real.pi - (-S K + G K - Real.log 2 + g K) =
      hplus r + Real.log Real.pi - -Real.log 2 + S K - G K - g K := by ring
  simp only [hS, hG, hg, hh] at e key
  rw [e]
  exact key

/-! ### The archimedean diagonal series -/

/-- The telescoping profile `Re(1/(2w) − 1/(6w³))` at `w = (c_k − 1) + ir`. -/
noncomputable def gD (r : ℝ) (k : ℕ) : ℝ :=
  (archWidth k - 1) / ((archWidth k - 1) ^ 2 + r ^ 2) / 2 -
    ((archWidth k - 1) ^ 3 - 3 * (archWidth k - 1) * r ^ 2) / ((archWidth k - 1) ^ 2 + r ^ 2) ^ 3 / 6

/-- The tail budget `1/(4(c_k − 1)⁵) + e^{−c_K L}/(2(c_k − 1))`. -/
noncomputable def hD (L : ℝ) (K k : ℕ) : ℝ :=
  1 / (4 * (archWidth k - 1) ^ 5) + Real.exp (-archWidth K * L) / (2 * (archWidth k - 1))

theorem abs_frac_sq_le {c r : ℝ} (hc : 0 < c) :
    |(c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2| ≤ 1 / c ^ 2 := by
  have hs : 0 < c ^ 2 + r ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (c ^ 2 + r ^ 2) ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : |c ^ 2 - r ^ 2| ≤ c ^ 2 + r ^ 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r]⟩
  nlinarith [sq_nonneg c, sq_nonneg r, mul_nonneg (sq_nonneg c) (sq_nonneg r)]

theorem stepD_bound (r : ℝ) {L : ℝ} (hL : 0 < L) {K k : ℕ} (hK : 10 ≤ K) (hk : K ≤ k) :
    |(1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2 -
      (gD r k - gD r (k + 1))| ≤ hD L K k - hD L K (k + 1) := by
  simp only [gD, hD]
  set c := archWidth k with hc
  have hc20 : 20 ≤ c := by
    simp only [hc, archWidth]; have : (10 : ℝ) ≤ k := by exact_mod_cast (show 10 ≤ k by omega)
    linarith
  have hk1 : archWidth (k + 1) - 1 = c + 1 := by simp only [hc, archWidth]; push_cast; ring
  rw [hk1]
  set z : ℂ := (c : ℂ) + r * I with hz
  have ht : c ≤ ‖z‖ := norm_line_ge (by linarith)
  have hz1 : 1 < ‖z‖ := by linarith
  have hzp : z + 1 = ((c + 1 : ℝ) : ℂ) + r * I := by rw [hz]; push_cast; ring
  have hzm : z - 1 = ((c - 1 : ℝ) : ℂ) + r * I := by rw [hz]; push_cast; ring
  have hsq := congrArg Complex.re (sq_tel hz1)
  rw [hzp, hzm] at hsq
  have hB := sq_rem_le (show 20 ≤ ‖z‖ by linarith)
  set R := ((6 - 14 * z ^ 2) / (6 * z ^ 2 * (z ^ 2 - 1) ^ 3)).re
  have hR : |R| ≤ 5 / 2 / ‖z‖ ^ 6 := (Complex.abs_re_le_norm _).trans hB
  have hf : (c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2 =
      ((c - 1) / ((c - 1) ^ 2 + r ^ 2) / 2 -
        ((c - 1) ^ 3 - 3 * (c - 1) * r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 3 / 6) -
      ((c + 1) / ((c + 1) ^ 2 + r ^ 2) / 2 -
        ((c + 1) ^ 3 - 3 * (c + 1) * r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 3 / 6) - R := by
    rw [hz, re_inv_sq_line (by linarith)] at hsq
    rw [hsq, Complex.sub_re, Complex.sub_re]
    have e3 : ((1 / 2 : ℂ) * ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹ - (((c + 1 : ℝ) : ℂ) + r * I)⁻¹)).re =
        ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹).re / 2 - ((((c + 1 : ℝ) : ℂ) + r * I)⁻¹).re / 2 := by
      simp [Complex.sub_re]; ring
    have e4 : ((1 / 6 : ℂ) * ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 3 -
        (((c + 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 3)).re =
        ((((c - 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 3).re / 6 - ((((c + 1 : ℝ) : ℂ) + r * I)⁻¹ ^ 3).re / 6 := by
      simp [Complex.sub_re]; ring
    rw [e3, e4, re_inv_line, re_inv_line, re_inv_cube_line (by linarith),
      re_inv_cube_line (by linarith)]
    ring
  set E := Real.exp (-archWidth K * L)
  set e := Real.exp (-c * L)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have heE : e ≤ E := by
    apply Real.exp_le_exp.mpr
    have : archWidth K ≤ c := by
      simp only [hc, archWidth]; have : (K : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    nlinarith
  have hfa := abs_frac_sq_le (r := r) (show 0 < c by linarith)
  have hcz : 5 / 2 / ‖z‖ ^ 6 ≤ 5 / 2 / c ^ 6 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) ht 6)
  have h6 := inv_pow6_le (show 2 ≤ c by linarith)
  have h2 := inv_sq_le (show 2 ≤ c by linarith)
  have hef : |e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2)| ≤ E * (1 / (2 * (c - 1)) - 1 / (2 * (c + 1))) := by
    rw [abs_mul, abs_of_nonneg he0]
    calc e * |(c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2| ≤ E * (1 / c ^ 2) :=
          mul_le_mul heE hfa (abs_nonneg _) hE0
      _ ≤ E * (1 / (2 * (c - 1)) - 1 / (2 * (c + 1))) := mul_le_mul_of_nonneg_left h2 hE0
  have hterm : (1 - e) * (c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2 =
      (c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2 - e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2) := by ring
  rw [hterm]
  have hfin : |-R - e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2)| ≤
      (1 / (4 * (c - 1) ^ 5) - 1 / (4 * (c + 1) ^ 5)) +
        E * (1 / (2 * (c - 1)) - 1 / (2 * (c + 1))) := by
    calc |-R - e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2)|
        ≤ |-R| + |e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2)| := abs_sub _ _
      _ ≤ _ := by rw [abs_neg]; exact add_le_add (hR.trans (hcz.trans h6)) hef
  have e5 : (c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2 - e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2) -
      (((c - 1) / ((c - 1) ^ 2 + r ^ 2) / 2 -
        ((c - 1) ^ 3 - 3 * (c - 1) * r ^ 2) / ((c - 1) ^ 2 + r ^ 2) ^ 3 / 6) -
      ((c + 1) / ((c + 1) ^ 2 + r ^ 2) / 2 -
        ((c + 1) ^ 3 - 3 * (c + 1) * r ^ 2) / ((c + 1) ^ 2 + r ^ 2) ^ 3 / 6)) =
      -R - e * ((c ^ 2 - r ^ 2) / (c ^ 2 + r ^ 2) ^ 2) := by rw [hf]; ring
  rw [e5]
  exact hfin.trans (le_of_eq (by ring))

/-- **The archimedean diagonal series with an explicit telescoped tail.** -/
theorem diagSeries_tel (r : ℝ) {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 10 ≤ K) :
    |(∑' k, (1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - r ^ 2) /
        (archWidth k ^ 2 + r ^ 2) ^ 2) -
      (∑ k ∈ range K, (1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - r ^ 2) /
        (archWidth k ^ 2 + r ^ 2) ^ 2) - gD r K| ≤ hD L K K := by
  set x : ℕ → ℝ := fun k => (1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - r ^ 2) /
    (archWidth k ^ 2 + r ^ 2) ^ 2 with hx
  have hsum : Summable x := by
    refine Summable.of_norm_bounded (summable_inv_width r) fun k => ?_
    have hc := archWidth_pos k
    have he1 : Real.exp (-archWidth k * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 := Real.exp_pos (-archWidth k * L)
    have hs : 0 < archWidth k ^ 2 + r ^ 2 := by positivity
    rw [Real.norm_eq_abs]
    simp only [hx]
    rw [mul_div_assoc, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - _)]
    have hfa : |(archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2| ≤
        1 / (archWidth k ^ 2 + r ^ 2) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (archWidth k ^ 2 + r ^ 2) ^ 2),
        div_le_div_iff₀ (by positivity) hs]
      have : |archWidth k ^ 2 - r ^ 2| ≤ archWidth k ^ 2 + r ^ 2 :=
        abs_le.mpr ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r]⟩
      nlinarith
    calc (1 - Real.exp (-archWidth k * L)) * |(archWidth k ^ 2 - r ^ 2) / (archWidth k ^ 2 + r ^ 2) ^ 2|
        ≤ 1 * (1 / (archWidth k ^ 2 + r ^ 2)) :=
          mul_le_mul (by linarith) hfa (abs_nonneg _) zero_le_one
      _ = 1 / (archWidth k ^ 2 + r ^ 2) := one_mul _
  have hT := hsum.hasSum.tendsto_sum_nat
  have hP : Tendsto (fun m => ∑ i ∈ range m, x (K + i)) atTop
      (𝓝 ((∑' k, x k) - ∑ k ∈ range K, x k)) := by
    refine ((hT.comp (tendsto_add_atTop_nat K)).sub_const (∑ k ∈ range K, x k)).congr fun m => ?_
    simp only [Function.comp]
    rw [Nat.add_comm m K, sum_range_add]
    ring
  have hg0 : Tendsto (gD r) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨1, fun k hk => ?_⟩) tendsto_inv_width_sub_one
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    set a := archWidth k - 1 with ha
    have ha1 : 1 ≤ a := by simp [ha, archWidth]; linarith
    have hs : a ^ 2 ≤ a ^ 2 + r ^ 2 := by nlinarith [sq_nonneg r]
    have hs0 : 0 < a ^ 2 + r ^ 2 := by positivity
    rw [Real.norm_eq_abs, gD, ← ha]
    have t1 : |a / (a ^ 2 + r ^ 2) / 2| ≤ 1 / (2 * a) := by
      rw [abs_of_nonneg (by positivity), div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have t2 : |(a ^ 3 - 3 * a * r ^ 2) / (a ^ 2 + r ^ 2) ^ 3 / 6| ≤ 1 / (2 * a) := by
      rw [div_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (a ^ 2 + r ^ 2) ^ 3 * 6),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hn : |a ^ 3 - 3 * a * r ^ 2| ≤ 3 * a * (a ^ 2 + r ^ 2) :=
        abs_le.mpr ⟨by nlinarith [sq_nonneg r, mul_nonneg (by linarith : (0 : ℝ) ≤ a) (sq_nonneg r)],
          by nlinarith [sq_nonneg r, mul_nonneg (by linarith : (0 : ℝ) ≤ a) (sq_nonneg r),
            pow_pos (by linarith : (0 : ℝ) < a) 3]⟩
      have h3 : 3 * a * (a ^ 2 + r ^ 2) * (2 * a) ≤ 1 * ((a ^ 2 + r ^ 2) ^ 3 * 6) := by
        have h1 : 1 ≤ a ^ 2 + r ^ 2 := by nlinarith
        have : a ^ 2 * 1 ≤ (a ^ 2 + r ^ 2) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ a ^ 2 + r ^ 2)]
      nlinarith [abs_nonneg (a ^ 3 - 3 * a * r ^ 2)]
    calc |a / (a ^ 2 + r ^ 2) / 2 - (a ^ 3 - 3 * a * r ^ 2) / (a ^ 2 + r ^ 2) ^ 3 / 6|
        ≤ |a / (a ^ 2 + r ^ 2) / 2| + |(a ^ 3 - 3 * a * r ^ 2) / (a ^ 2 + r ^ 2) ^ 3 / 6| :=
          abs_sub _ _
      _ ≤ 1 / (2 * a) + 1 / (2 * a) := add_le_add t1 t2
      _ = 1 / a := by field_simp; ring
  have hh : ∀ k, K ≤ k → 0 ≤ hD L K k := fun k hk => by
    have : (10 : ℝ) ≤ k := by exact_mod_cast (show 10 ≤ k by omega)
    have ha : 0 < archWidth k - 1 := by simp [archWidth]; linarith
    simp only [hD]; positivity
  have key := tail_limit (x := x) (g := gD r) (h := hD L K) (fun k hk => stepD_bound r hL hK hk)
    hg0 hh hP
  simpa only [hx] using key

end AEGIS.CvSDiagTelV1

#print axioms AEGIS.CvSDiagTelV1.log_step_bound
#print axioms AEGIS.CvSDiagTelV1.cube_tel
#print axioms AEGIS.CvSDiagTelV1.sq_tel
#print axioms AEGIS.CvSDiagTelV1.tail_limit
#print axioms AEGIS.CvSDiagTelV1.hplus_limit
#print axioms AEGIS.CvSDiagTelV1.logG_limit
#print axioms AEGIS.CvSDiagTelV1.step_bound
#print axioms AEGIS.CvSDiagTelV1.hplus_tel
#print axioms AEGIS.CvSDiagTelV1.stepD_bound
#print axioms AEGIS.CvSDiagTelV1.diagSeries_tel
