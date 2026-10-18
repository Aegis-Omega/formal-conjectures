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
import CvSArchSourceV1

/-!
# The diagonal archimedean entry (CvS step 5.2d)

The diagonal prime-block profile is `f(y) = 2(1 − y/L) cos(ωy)`, `ω = 2πn/L`
(`CvSPrimeBlockV1.trigAtom_hermitian_block`). For its cosine transform `D(r)`:

* `(r² − ω²) D(r) = (2/L)(1 − cos(rL)) + (4ω/L) S(r, n, L)`, so `D` decays like `r⁻²`;
* `∫ 2c/(c² + r²) D(r) dr = 4π (c/(c² + ω²) − (1 − e^{−cL})(c² − ω²)/(L (c² + ω²)²))`;
* `∫ D = 2π` (here the constants of `h₊` do not drop out);
* for every constant `C`, with `a_k` the digamma series terms,
  `∫ (∑' k, a_k(r) − C) D(r) dr
     = 2π (∑' k, a_k(ω) − C) + (4π/L) ∑' k, (1 − e^{−c_k L})(c_k² − ω²)/(c_k² + ω²)²`.
-/

open MeasureTheory Set Real

noncomputable section

namespace AEGIS.CvSArchDiagV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1

/-! ### Cosine transforms of profiles on `[0, L]` -/

/-- Cosine transform of a profile on `[0, L]`. -/
def cosT (f : ℝ → ℝ) (L r : ℝ) : ℝ := ∫ y in (0 : ℝ)..L, f y * Real.cos (r * y)

theorem cosT_continuous {f : ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    Continuous fun r => cosT f L r := by
  unfold cosT
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by
      show Continuous fun p : ℝ × ℝ => f p.2 * Real.cos (p.1 * p.2)
      fun_prop) 0 L

/-- **Lorentzian against a profile**: `∫ 2c/(c² + r²) (∫₀ᴸ f(y) cos(ry) dy) dr
= 2π ∫₀ᴸ f(y) e^{−cy} dy`. -/
theorem lorentz_profile {c L : ℝ} (hc : 0 < c) (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * cosT f L r =
      2 * π * ∫ y in (0 : ℝ)..L, f y * Real.exp (-c * y) := by
  set F : ℝ → ℝ → ℝ := fun y r => f y * (Real.cos (r * y) * (2 * c / (c ^ 2 + r ^ 2)))
  have hcont : Continuous (Function.uncurry F) := by
    have hd : ∀ r : ℝ, c ^ 2 + r ^ 2 ≠ 0 := fun r => by positivity
    simp only [F]
    exact (hf.comp continuous_fst).mul
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * p.1)).mul
        (continuous_const.div (by fun_prop) fun p => hd p.2))
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc 0 L)).prod volume) := by
    rw [uIoc_of_le hL.le]
    have hg : Integrable (fun p : ℝ × ℝ => |f p.1| * (2 * c / (c ^ 2 + (1 * p.2) ^ 2)))
        ((volume.restrict (Ioc 0 L)).prod volume) :=
      (hf.abs.integrableOn_Ioc).mul_prod (lorentz_integrable hc one_ne_zero)
    refine hg.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [F, Function.uncurry, one_mul, norm_mul, Real.norm_eq_abs]
    have hw : 0 ≤ 2 * c / (c ^ 2 + p.2 ^ 2) := by positivity
    rw [abs_of_nonneg hw]
    calc |f p.1| * (|Real.cos (p.2 * p.1)| * (2 * c / (c ^ 2 + p.2 ^ 2)))
        ≤ |f p.1| * (1 * (2 * c / (c ^ 2 + p.2 ^ 2))) := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = |f p.1| * (2 * c / (c ^ 2 + p.2 ^ 2)) := by ring
  have hswap := intervalIntegral_integral_swap hint
  have hlhs : (∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * cosT f L r) =
      ∫ r : ℝ, ∫ y in (0 : ℝ)..L, F y r := by
    congr 1; funext r
    simp only [cosT, F, ← intervalIntegral.integral_const_mul]
    congr 1; funext y; ring
  rw [hlhs, ← hswap, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hL.le] at hy
  simp only [F]
  rw [integral_const_mul, lorentz_cos_integral hc, abs_of_nonneg hy.1]
  ring

/-! ### The digamma series against a decaying source -/

theorem integrable_of_bounds {T : ℝ → ℝ} (hT : Continuous T) {M0 M2 : ℝ}
    (h0 : ∀ r, |T r| ≤ M0) (h2 : ∀ r, |r ^ 2 * T r| ≤ M2) : Integrable T := by
  refine (integrable_inv_one_add_sq.const_mul (M0 + M2)).mono' hT.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => ?_)
  have a := h0 r
  have b := h2 r
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)] at b
  rw [Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc |T r| * (1 + r ^ 2) = |T r| + r ^ 2 * |T r| := by ring
    _ ≤ M0 + M2 := by linarith

theorem archTerm_mul_integrable {T : ℝ → ℝ} (hTi : Integrable T) (k : ℕ) :
    Integrable fun r => archTerm k r * T r := by
  have hc := archWidth_pos k
  refine hTi.bdd_mul (c := 1 / ((k : ℝ) + 1) + 2 / archWidth k)
    (archTerm_continuous k).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs]
  unfold archTerm
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  refine add_le_add le_rfl ?_
  rw [div_le_div_iff₀ (by positivity) hc]
  nlinarith [sq_nonneg r]

theorem archTerm_mul_norm_integral_le {T : ℝ → ℝ} (hTi : Integrable T) {M2 : ℝ}
    (h2 : ∀ r, |r ^ 2 * T r| ≤ M2) (k : ℕ) :
    ∫ r, ‖archTerm k r * T r‖ ≤ (3 * (∫ r, |T r|) + 8 * π * M2) / ((k : ℝ) + 1) ^ 2 := by
  have hc := archWidth_pos k
  have hB0 : 0 ≤ M2 := by simpa using h2 0
  set d := 1 / ((k : ℝ) + 1) - 2 / archWidth k
  have hSabs : Integrable fun r => |T r| := hTi.abs
  have hG : Integrable fun r => |d| * |T r| + 2 / archWidth k * M2 * (archWidth k ^ 2 + r ^ 2)⁻¹ :=
    (hSabs.const_mul _).add ((inv_lorentz_integrable hc).const_mul _)
  have hpt : ∀ r, ‖archTerm k r * T r‖ ≤
      |d| * |T r| + 2 / archWidth k * M2 * (archWidth k ^ 2 + r ^ 2)⁻¹ := by
    intro r
    have hden : 0 < archWidth k ^ 2 + r ^ 2 := by positivity
    rw [Real.norm_eq_abs, archTerm_split, add_mul]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
    rw [show 2 / archWidth k * (r ^ 2 * (archWidth k ^ 2 + r ^ 2)⁻¹) * T r =
        2 / archWidth k * (r ^ 2 * T r) * (archWidth k ^ 2 + r ^ 2)⁻¹ by ring,
      abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 / archWidth k),
      abs_of_pos (inv_pos.mpr hden)]
    gcongr
    exact h2 r
  refine (integral_mono ((archTerm_mul_integrable hTi k).norm) hG hpt).trans ?_
  rw [integral_add (hSabs.const_mul _) ((inv_lorentz_integrable hc).const_mul _),
    integral_const_mul, integral_const_mul, inv_lorentz_integral hc]
  have hM : 0 ≤ ∫ r, |T r| := integral_nonneg fun r => abs_nonneg _
  have hd := archShift_abs_le k
  have hsq := archWidth_sq_ge k
  have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have h2' : 2 / archWidth k * M2 * (π / archWidth k) ≤ 8 * π * M2 / ((k : ℝ) + 1) ^ 2 := by
    rw [show 2 / archWidth k * M2 * (π / archWidth k) = 2 * π * M2 / archWidth k ^ 2 by ring,
      div_le_div_iff₀ (by positivity) hk1]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * π * M2)]
  calc |d| * (∫ r, |T r|) + 2 / archWidth k * M2 * (π / archWidth k)
      ≤ 3 / ((k : ℝ) + 1) ^ 2 * (∫ r, |T r|) + 8 * π * M2 / ((k : ℝ) + 1) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hd hM) h2'
    _ = _ := by ring

theorem archTerm_mul_summable {T : ℝ → ℝ} (hTi : Integrable T) {M2 : ℝ}
    (h2 : ∀ r, |r ^ 2 * T r| ≤ M2) : Summable fun k => ∫ r, ‖archTerm k r * T r‖ := by
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun r => norm_nonneg _)
    (fun k => archTerm_mul_norm_integral_le hTi h2 k) ?_
  exact (summable_inv_succ_sq.mul_left (3 * (∫ r, |T r|) + 8 * π * M2)).congr fun k => by ring

/-- **The digamma series against a decaying source.** For continuous `T` with
`|T| ≤ M₀` and `|r² T| ≤ M₂`, and every constant `C`,
`∫ (∑' k, a_k(r) − C) T(r) dr = ∑' k, ∫ a_k T − C ∫ T`. -/
theorem arch_series_generic {T : ℝ → ℝ} (hT : Continuous T) {M0 M2 : ℝ}
    (h0 : ∀ r, |T r| ≤ M0) (h2 : ∀ r, |r ^ 2 * T r| ≤ M2) (C : ℝ) :
    ∫ r, ((∑' k, archTerm k r) - C) * T r =
      (∑' k, ∫ r, archTerm k r * T r) - C * ∫ r, T r := by
  have hTi := integrable_of_bounds hT h0 h2
  set b : ℕ → ℝ := fun k => if k = 0 then C else 0 with hb
  set F : ℕ → ℝ → ℝ := fun k r => (archTerm k r - b k) * T r with hF
  have hFint : ∀ k, Integrable (F k) := fun k =>
    ((archTerm_mul_integrable hTi k).sub (hTi.const_mul (b k))).congr
      (Filter.Eventually.of_forall fun r => by simp only [hF, Pi.sub_apply]; ring)
  have hFval : ∀ k, ∫ r, F k r = (∫ r, archTerm k r * T r) - b k * ∫ r, T r := fun k => by
    have : F k = fun r => archTerm k r * T r - b k * T r := by
      funext r; simp only [hF]; ring
    rw [this, integral_sub (archTerm_mul_integrable hTi k) (hTi.const_mul (b k)),
      integral_const_mul]
  have hbsum : Summable fun k => |b k| * ∫ r, |T r| := by
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    have : k ≠ 0 := by simpa using hk
    simp [hb, this]
  have hFsum : Summable fun k => ∫ r, ‖F k r‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun r => norm_nonneg _)
      (fun k => ?_) ((archTerm_mul_summable hTi h2).add hbsum)
    have hpt : ∀ r, ‖F k r‖ ≤ ‖archTerm k r * T r‖ + |b k| * |T r| := by
      intro r
      simp only [hF, Real.norm_eq_abs, sub_mul]
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_mul (b k)]
    have hG : Integrable fun r => ‖archTerm k r * T r‖ + |b k| * |T r| :=
      (archTerm_mul_integrable hTi k).norm.add (hTi.abs.const_mul _)
    refine (integral_mono (hFint k).norm hG hpt).trans_eq ?_
    rw [integral_add (archTerm_mul_integrable hTi k).norm (hTi.abs.const_mul _),
      integral_const_mul]
  have hpt : ∀ r, ∑' k, F k r = ((∑' k, archTerm k r) - C) * T r := by
    intro r
    simp only [hF]
    rw [tsum_mul_right, ((archTerm_summable r).tsum_sub (hasSum_ite_eq 0 C).summable),
      tsum_ite_eq]
  have hxsum : Summable fun k => ∫ r, archTerm k r * T r :=
    Summable.of_norm_bounded (archTerm_mul_summable hTi h2) fun k =>
      norm_integral_le_integral_norm _
  rw [← funext hpt, ← integral_tsum_of_summable_integral_norm hFint hFsum, tsum_congr hFval,
    hxsum.tsum_sub ((hasSum_ite_eq 0 C).summable.mul_right _), tsum_mul_right, tsum_ite_eq]

/-! ### The diagonal profile -/

/-- The diagonal profile `2(1 − y/L) cos(ωy)`, `ω = 2πn/L`. -/
def diagProfile (L : ℝ) (n : ℤ) (y : ℝ) : ℝ := 2 * (1 - y / L) * Real.cos (2 * π * n / L * y)

/-- Its cosine transform `D(r)`. -/
def diagD (L r : ℝ) (n : ℤ) : ℝ := cosT (diagProfile L n) L r

theorem diagProfile_continuous (L : ℝ) (n : ℤ) : Continuous (diagProfile L n) := by
  unfold diagProfile; fun_prop

theorem diag_hasDerivAt (L ω r y : ℝ) :
    HasDerivAt (fun y => (-(2 / L) * Real.cos (ω * y) - 2 * ω * (1 - y / L) * Real.sin (ω * y)) *
        Real.cos (r * y) + r * (2 * (1 - y / L) * Real.cos (ω * y)) * Real.sin (r * y))
      ((r ^ 2 - ω ^ 2) * (2 * (1 - y / L) * Real.cos (ω * y) * Real.cos (r * y)) +
        4 * ω / L * (Real.sin (ω * y) * Real.cos (r * y))) y := by
  have hs : ∀ a : ℝ, HasDerivAt (fun y => Real.sin (a * y)) (Real.cos (a * y) * a) y :=
    fun a => by simpa using ((hasDerivAt_id y).const_mul a).sin
  have hc : ∀ a : ℝ, HasDerivAt (fun y => Real.cos (a * y)) (-Real.sin (a * y) * a) y :=
    fun a => by simpa using ((hasDerivAt_id y).const_mul a).cos
  have hl : HasDerivAt (fun y => 1 - y / L) (-(1 / L)) y := by
    simpa using ((hasDerivAt_id y).div_const L).const_sub 1
  have h1 := ((((hc ω).const_mul (-(2 / L))).sub ((hl.const_mul (2 * ω)).mul (hs ω))).mul
    (hc r)).add ((((hl.const_mul 2).mul (hc ω)).const_mul r).mul (hs r))
  refine h1.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- **Diagonal identity.** `(r² − ω²) D(r) = (2/L)(1 − cos(rL)) + (4ω/L) S(r, n, L)`. -/
theorem diag_identity {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) :
    (r ^ 2 - (2 * π * n / L) ^ 2) * diagD L r n =
      2 / L * (1 - Real.cos (r * L)) + 4 * (2 * π * n / L) / L * sourceS L r n := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  have hS : sourceS L r n = -∫ y in (0 : ℝ)..L, Real.sin (ω * y) * Real.cos (r * y) := by
    simp only [sourceS]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext y
    rw [sin_node L y n, hω]; ring
  have hD : diagD L r n =
      ∫ y in (0 : ℝ)..L, 2 * (1 - y / L) * Real.cos (ω * y) * Real.cos (r * y) := by
    simp only [diagD, cosT, diagProfile, hω]
  have hint1 : IntervalIntegrable
      (fun y => 2 * (1 - y / L) * Real.cos (ω * y) * Real.cos (r * y)) volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hint2 : IntervalIntegrable (fun y => Real.sin (ω * y) * Real.cos (r * y)) volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
    (fun y _ => diag_hasDerivAt L ω r y) (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  have hωL : ω * L = n * (2 * π) := by rw [← hω]; field_simp
  rw [hωL, sin_int_mul_two_pi', Real.cos_int_mul_two_pi, div_self hL.ne'] at key
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, sub_self, zero_div, sub_zero, mul_one,
    zero_mul, add_zero] at key
  rw [hω, hD, hS]
  linear_combination key

theorem diagD_abs_le {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) : |diagD L r n| ≤ 2 * L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
    (f := fun y => diagProfile L n y * Real.cos (r * y)) (C := 2)
    (fun y hy => by
      rw [uIoc_of_le hL.le] at hy
      have h1 : 0 ≤ 1 - y / L := by rw [sub_nonneg, div_le_one hL]; exact hy.2
      have h2 : 1 - y / L ≤ 1 := by have := div_nonneg hy.1.le hL.le; linarith
      simp only [diagProfile, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg h1]
      calc 2 * (1 - y / L) * |Real.cos (2 * π * n / L * y)| * |Real.cos (r * y)|
          ≤ 2 * 1 * 1 * 1 := by
            gcongr
            · exact Real.abs_cos_le_one _
            · exact Real.abs_cos_le_one _
        _ = 2 := by ring)
  simpa [diagD, cosT, abs_of_pos hL] using h

theorem sq_mul_diagD_abs_le {L : ℝ} (hL : 0 < L) (n : ℤ) (r : ℝ) :
    |r ^ 2 * diagD L r n| ≤
      2 * L * (2 * π * n / L) ^ 2 + 4 / L + 4 * |2 * π * n / L| := by
  have hid := diag_identity hL n r
  have hD := diagD_abs_le hL n r
  have hS := sourceS_abs_le hL n r
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  rw [hω] at hid ⊢
  have h1 : r ^ 2 * diagD L r n =
      ω ^ 2 * diagD L r n + 2 / L * (1 - Real.cos (r * L)) + 4 * ω / L * sourceS L r n := by
    linear_combination hid
  rw [h1]
  have hcos : |1 - Real.cos (r * L)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (r * L), Real.cos_le_one (r * L)]
  calc |ω ^ 2 * diagD L r n + 2 / L * (1 - Real.cos (r * L)) + 4 * ω / L * sourceS L r n|
      ≤ |ω ^ 2 * diagD L r n| + |2 / L * (1 - Real.cos (r * L))| +
          |4 * ω / L * sourceS L r n| := abs_add_three _ _ _
    _ = ω ^ 2 * |diagD L r n| + 2 / L * |1 - Real.cos (r * L)| +
          4 * |ω| / L * |sourceS L r n| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ω), abs_div, abs_div, abs_mul,
          abs_of_pos hL, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ ω ^ 2 * (2 * L) + 2 / L * 2 + 4 * |ω| / L * L := by gcongr
    _ = 2 * L * ω ^ 2 + 4 / L + 4 * |ω| := by field_simp; ring

theorem diagD_continuous (L : ℝ) (n : ℤ) : Continuous fun r => diagD L r n :=
  cosT_continuous (diagProfile_continuous L n) L

/-! ### The Lorentzian value of the diagonal profile -/

theorem exp_trig_hasDerivAt (c ω p q s t y : ℝ) :
    HasDerivAt (fun y => 2 * Real.exp (-c * y) *
        ((p + q * y) * Real.cos (ω * y) - (s + t * y) * Real.sin (ω * y)))
      (2 * Real.exp (-c * y) *
        ((-c * (p + q * y) + q - ω * (s + t * y)) * Real.cos (ω * y) +
          (c * (s + t * y) - ω * (p + q * y) - t) * Real.sin (ω * y))) y := by
  have hs : HasDerivAt (fun y => Real.sin (ω * y)) (Real.cos (ω * y) * ω) y := by
    simpa using ((hasDerivAt_id y).const_mul ω).sin
  have hc : HasDerivAt (fun y => Real.cos (ω * y)) (-Real.sin (ω * y) * ω) y := by
    simpa using ((hasDerivAt_id y).const_mul ω).cos
  have he : HasDerivAt (fun y => Real.exp (-c * y)) (Real.exp (-c * y) * (-c)) y := by
    simpa using ((hasDerivAt_id y).const_mul (-c)).exp
  have hlin : ∀ a b : ℝ, HasDerivAt (fun y => a + b * y) b y := fun a b => by
    simpa using ((hasDerivAt_id y).const_mul b).const_add a
  have h := (he.const_mul 2).mul (((hlin p q).mul hc).sub ((hlin s t).mul hs))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- `∫₀ᴸ 2(1 − y/L) cos(ωy) e^{−cy} dy = 2 (c/(c² + ω²) − (1 − e^{−cL})(c² − ω²)/(L (c² + ω²)²))`. -/
theorem diag_exp_integral {L : ℝ} (hL : 0 < L) (n : ℤ) {c : ℝ} (hc : 0 < c) :
    ∫ y in (0 : ℝ)..L, diagProfile L n y * Real.exp (-c * y) =
      2 * (c / (c ^ 2 + (2 * π * n / L) ^ 2) -
        (1 - Real.exp (-c * L)) * (c ^ 2 - (2 * π * n / L) ^ 2) /
          (L * (c ^ 2 + (2 * π * n / L) ^ 2) ^ 2)) := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  have hD : c ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have hL0 : L ≠ 0 := hL.ne'
  set D := c ^ 2 + ω ^ 2 with hDdef
  set p := -c / D + (c ^ 2 - ω ^ 2) / (L * D ^ 2)
  set q := c / (L * D)
  set s := -ω / D + 2 * c * ω / (L * D ^ 2)
  set t := ω / (L * D)
  have hderiv : ∀ y, HasDerivAt (fun y => 2 * Real.exp (-c * y) *
      ((p + q * y) * Real.cos (ω * y) - (s + t * y) * Real.sin (ω * y)))
      (diagProfile L n y * Real.exp (-c * y)) y := by
    intro y
    refine (exp_trig_hasDerivAt c ω p q s t y).congr_deriv ?_
    have hcos : -c * (p + q * y) + q - ω * (s + t * y) = 1 - y / L := by
      simp only [p, q, s, t, hDdef]; field_simp; ring
    have hsin : c * (s + t * y) - ω * (p + q * y) - t = 0 := by
      simp only [p, q, s, t, hDdef]; field_simp; ring
    rw [hcos, hsin, diagProfile, hω]
    ring
  rw [hω, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    (by apply Continuous.intervalIntegrable; unfold diagProfile; fun_prop)]
  have hωL : ω * L = n * (2 * π) := by rw [← hω]; field_simp
  rw [hωL, sin_int_mul_two_pi', Real.cos_int_mul_two_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, Real.exp_zero, mul_one, sub_zero, add_zero]
  simp only [p, q, hDdef]
  field_simp
  ring

/-- **Lorentzian value of the diagonal source.** -/
theorem lorentz_diag {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (n : ℤ) :
    ∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * diagD L r n =
      4 * π * (c / (c ^ 2 + (2 * π * n / L) ^ 2) -
        (1 - Real.exp (-c * L)) * (c ^ 2 - (2 * π * n / L) ^ 2) /
          (L * (c ^ 2 + (2 * π * n / L) ^ 2) ^ 2)) := by
  simp only [diagD]
  rw [lorentz_profile hc hL (diagProfile_continuous L n), diag_exp_integral hL n hc]
  ring

/-- If `|x − a| ≤ A/c` for every `c ≥ 1`, then `x = a`. -/
theorem eq_of_abs_sub_le_div {x a A : ℝ} (h : ∀ c : ℝ, 1 ≤ c → |x - a| ≤ A / c) : x = a := by
  by_contra hx
  have hx' : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hc : 1 ≤ (|A| + 1) / |x - a| + 1 := by
    have : 0 ≤ (|A| + 1) / |x - a| := by positivity
    linarith
  have h' := h _ hc
  have hpos : 0 < (|A| + 1) / |x - a| + 1 := by linarith
  rw [le_div_iff₀ hpos] at h'
  have : |x - a| * ((|A| + 1) / |x - a|) = |A| + 1 := by field_simp
  nlinarith [le_abs_self A]

/-- **The diagonal source has total mass `2π`**: `∫ D(r) dr = 2π`. -/
theorem diagD_integral {L : ℝ} (hL : 0 < L) (n : ℤ) : ∫ r : ℝ, diagD L r n = 2 * π := by
  have hB := fun r => sq_mul_diagD_abs_le hL n r
  have hDint := integrable_of_bounds (diagD_continuous L n) (diagD_abs_le hL n) hB
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, 2 * π * n / L = ω := ⟨_, rfl⟩
  simp only [hω] at hB
  set M2 := 2 * L * ω ^ 2 + 4 / L + 4 * |ω|
  refine eq_of_abs_sub_le_div (A := M2 * π + 2 * π * ω ^ 2 + 2 * π / L) fun c hc1 => ?_
  have hc : 0 < c := by linarith
  have hden : ∀ r : ℝ, 0 < c ^ 2 + r ^ 2 := fun r => by positivity
  have hTint : Integrable fun r : ℝ => r ^ 2 * diagD L r n * (c ^ 2 + r ^ 2)⁻¹ := by
    refine ((inv_lorentz_integrable hc).const_mul M2).mono' ?_
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (((continuous_pow 2).mul (diagD_continuous L n)).mul
        ((continuous_const.add (continuous_pow 2)).inv₀ fun r => (hden r).ne')).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (hden r)]
      exact mul_le_mul_of_nonneg_right (hB r) (inv_nonneg.mpr (hden r).le)
  have hJ : |∫ r : ℝ, r ^ 2 * diagD L r n * (c ^ 2 + r ^ 2)⁻¹| ≤ M2 * π / c := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((inv_lorentz_integrable hc).const_mul M2)
      (Filter.Eventually.of_forall fun r => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (hden r)]
      exact mul_le_mul_of_nonneg_right (hB r) (inv_nonneg.mpr (hden r).le)
    · rw [integral_const_mul, inv_lorentz_integral hc]; ring
  have hsplit : (fun r : ℝ => 2 * c / (c ^ 2 + r ^ 2) * diagD L r n) =
      fun r => 2 / c * (diagD L r n - r ^ 2 * diagD L r n * (c ^ 2 + r ^ 2)⁻¹) := by
    funext r
    have := (hden r).ne'
    field_simp
    ring
  have hV := lorentz_diag hc hL n
  rw [hsplit, integral_const_mul, integral_sub hDint hTint, hω] at hV
  set I := ∫ r : ℝ, diagD L r n
  set J := ∫ r : ℝ, r ^ 2 * diagD L r n * (c ^ 2 + r ^ 2)⁻¹
  have hD0 : 0 < c ^ 2 + ω ^ 2 := by positivity
  set E := (1 - Real.exp (-c * L)) * (c ^ 2 - ω ^ 2) / (L * (c ^ 2 + ω ^ 2) ^ 2)
  have hIJ : I - 2 * π = J + (-(2 * π * ω ^ 2 / (c ^ 2 + ω ^ 2)) - 2 * π * c * E) := by
    have h2 : I - J = c / 2 * (2 / c * (I - J)) := by field_simp
    rw [hV] at h2
    have h3 : c / 2 * (4 * π * (c / (c ^ 2 + ω ^ 2) - E)) - 2 * π =
        -(2 * π * ω ^ 2 / (c ^ 2 + ω ^ 2)) - 2 * π * c * E := by
      field_simp; ring
    linear_combination h2 + h3
  have he0 : 0 ≤ 1 - Real.exp (-c * L) := by
    have : Real.exp (-c * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have he1 : 1 - Real.exp (-c * L) ≤ 1 := by linarith [Real.exp_pos (-c * L)]
  have hEb : |2 * π * c * E| ≤ 2 * π / L / c := by
    have hnum : |(1 - Real.exp (-c * L)) * (c ^ 2 - ω ^ 2)| ≤ c ^ 2 + ω ^ 2 := by
      rw [abs_mul, abs_of_nonneg he0]
      have : |c ^ 2 - ω ^ 2| ≤ c ^ 2 + ω ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg c, sq_nonneg ω]
      calc (1 - Real.exp (-c * L)) * |c ^ 2 - ω ^ 2| ≤ 1 * (c ^ 2 + ω ^ 2) := by
            gcongr
        _ = c ^ 2 + ω ^ 2 := one_mul _
    have hE : |E| ≤ 1 / (L * c ^ 2) := by
      simp only [E]
      rw [abs_div, abs_of_pos (by positivity : 0 < L * (c ^ 2 + ω ^ 2) ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      calc |(1 - Real.exp (-c * L)) * (c ^ 2 - ω ^ 2)| * (L * c ^ 2)
          ≤ (c ^ 2 + ω ^ 2) * (L * c ^ 2) := by gcongr
        _ ≤ 1 * (L * (c ^ 2 + ω ^ 2) ^ 2) := by
            nlinarith [mul_nonneg (mul_nonneg hL.le hD0.le) (sq_nonneg ω)]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π * c)]
    calc 2 * π * c * |E| ≤ 2 * π * c * (1 / (L * c ^ 2)) := by gcongr
      _ = 2 * π / L / c := by field_simp
  have hWb : |2 * π * ω ^ 2 / (c ^ 2 + ω ^ 2)| ≤ 2 * π * ω ^ 2 / c := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ hD0 hc]
    have h2π : (0 : ℝ) ≤ 2 * π := by positivity
    nlinarith [mul_nonneg (mul_nonneg h2π (sq_nonneg ω)) (by nlinarith : (0 : ℝ) ≤ c ^ 2 - c),
      mul_nonneg (mul_nonneg h2π (sq_nonneg ω)) (sq_nonneg ω)]
  rw [hIJ]
  calc |J + (-(2 * π * ω ^ 2 / (c ^ 2 + ω ^ 2)) - 2 * π * c * E)|
      ≤ |J| + (|2 * π * ω ^ 2 / (c ^ 2 + ω ^ 2)| + |2 * π * c * E|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (abs_sub _ _).trans (add_le_add (le_of_eq (abs_neg _)) le_rfl)
    _ ≤ M2 * π / c + (2 * π * ω ^ 2 / c + 2 * π / L / c) := add_le_add hJ (add_le_add hWb hEb)
    _ = (M2 * π + 2 * π * ω ^ 2 + 2 * π / L) / c := by field_simp; ring

/-- **One digamma term against the diagonal source.** -/
theorem archTerm_diag_integral {L : ℝ} (hL : 0 < L) (n : ℤ) (k : ℕ) :
    ∫ r, archTerm k r * diagD L r n =
      2 * π * archTerm k (2 * π * n / L) +
        4 * π / L * ((1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - (2 * π * n / L) ^ 2) /
          (archWidth k ^ 2 + (2 * π * n / L) ^ 2) ^ 2) := by
  have hc := archWidth_pos k
  have hDint := integrable_of_bounds (diagD_continuous L n) (diagD_abs_le hL n)
    (sq_mul_diagD_abs_le hL n)
  have hlor : Integrable fun r => 2 * archWidth k / (archWidth k ^ 2 + r ^ 2) * diagD L r n := by
    have := (archTerm_mul_integrable hDint k).sub (hDint.const_mul (1 / ((k : ℝ) + 1)))
    refine (this.neg).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [archTerm, Pi.neg_apply, Pi.sub_apply]
    ring
  simp only [archTerm, sub_mul]
  rw [integral_sub (hDint.const_mul _) hlor, integral_const_mul, diagD_integral hL n,
    lorentz_diag hc hL n]
  have hD : archWidth k ^ 2 + (2 * π * n / L) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem summable_diag_tail {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    Summable fun k => (1 - Real.exp (-archWidth k * L)) * (archWidth k ^ 2 - ω ^ 2) /
      (archWidth k ^ 2 + ω ^ 2) ^ 2 := by
  refine Summable.of_norm_bounded ((summable_inv_succ_sq).mul_left 4) fun k => ?_
  have hc := archWidth_pos k
  have hsq := archWidth_sq_ge k
  have hD : 0 < archWidth k ^ 2 + ω ^ 2 := by positivity
  have he0 : 0 ≤ 1 - Real.exp (-archWidth k * L) := by
    have : Real.exp (-archWidth k * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have he1 : 1 - Real.exp (-archWidth k * L) ≤ 1 := by
    linarith [Real.exp_pos (-archWidth k * L)]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg he0,
    abs_of_pos (by positivity : (0 : ℝ) < (archWidth k ^ 2 + ω ^ 2) ^ 2),
    div_le_iff₀ (by positivity)]
  have hab : |archWidth k ^ 2 - ω ^ 2| ≤ archWidth k ^ 2 + ω ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ω]
  have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  calc (1 - Real.exp (-archWidth k * L)) * |archWidth k ^ 2 - ω ^ 2|
      ≤ 1 * (archWidth k ^ 2 + ω ^ 2) := by gcongr
    _ ≤ 4 * (1 / ((k : ℝ) + 1) ^ 2) * (archWidth k ^ 2 + ω ^ 2) ^ 2 := by
        rw [one_mul, show 4 * (1 / ((k : ℝ) + 1) ^ 2) * (archWidth k ^ 2 + ω ^ 2) ^ 2 =
          (archWidth k ^ 2 + ω ^ 2) * (4 * (archWidth k ^ 2 + ω ^ 2) / ((k : ℝ) + 1) ^ 2) by
            field_simp]
        refine le_mul_of_one_le_right hD.le ?_
        rw [le_div_iff₀ hk1]
        nlinarith [sq_nonneg ω]

/-- **Diagonal archimedean value.** For every constant `C`,
`∫ (∑' k, a_k(r) − C) D(r) dr
  = 2π (∑' k, a_k(ω) − C) + (4π/L) ∑' k, (1 − e^{−c_k L})(c_k² − ω²)/(c_k² + ω²)²`. -/
theorem arch_series_diag {L : ℝ} (hL : 0 < L) (n : ℤ) (C : ℝ) :
    ∫ r, ((∑' k, archTerm k r) - C) * diagD L r n =
      2 * π * ((∑' k, archTerm k (2 * π * n / L)) - C) +
        4 * π / L * ∑' k, (1 - Real.exp (-archWidth k * L)) *
          (archWidth k ^ 2 - (2 * π * n / L) ^ 2) / (archWidth k ^ 2 + (2 * π * n / L) ^ 2) ^ 2 := by
  rw [arch_series_generic (diagD_continuous L n) (diagD_abs_le hL n) (sq_mul_diagD_abs_le hL n),
    diagD_integral hL n]
  simp_rw [archTerm_diag_integral hL n]
  rw [((archTerm_summable _).mul_left (2 * π)).tsum_add
      ((summable_diag_tail hL _).mul_left (4 * π / L)), tsum_mul_left, tsum_mul_left]
  ring

end AEGIS.CvSArchDiagV1

#print axioms AEGIS.CvSArchDiagV1.cosT_continuous
#print axioms AEGIS.CvSArchDiagV1.lorentz_profile
#print axioms AEGIS.CvSArchDiagV1.integrable_of_bounds
#print axioms AEGIS.CvSArchDiagV1.archTerm_mul_integrable
#print axioms AEGIS.CvSArchDiagV1.archTerm_mul_norm_integral_le
#print axioms AEGIS.CvSArchDiagV1.archTerm_mul_summable
#print axioms AEGIS.CvSArchDiagV1.arch_series_generic
#print axioms AEGIS.CvSArchDiagV1.diag_hasDerivAt
#print axioms AEGIS.CvSArchDiagV1.diag_identity
#print axioms AEGIS.CvSArchDiagV1.diagD_abs_le
#print axioms AEGIS.CvSArchDiagV1.sq_mul_diagD_abs_le
#print axioms AEGIS.CvSArchDiagV1.exp_trig_hasDerivAt
#print axioms AEGIS.CvSArchDiagV1.diag_exp_integral
#print axioms AEGIS.CvSArchDiagV1.lorentz_diag
#print axioms AEGIS.CvSArchDiagV1.eq_of_abs_sub_le_div
#print axioms AEGIS.CvSArchDiagV1.diagD_integral
#print axioms AEGIS.CvSArchDiagV1.archTerm_diag_integral
#print axioms AEGIS.CvSArchDiagV1.summable_diag_tail
#print axioms AEGIS.CvSArchDiagV1.arch_series_diag
