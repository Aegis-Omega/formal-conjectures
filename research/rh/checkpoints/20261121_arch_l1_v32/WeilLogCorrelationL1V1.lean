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

import Mathlib

/-!
AEGIS Ω — L¹ bound for a logarithmic autocorrelation (Claude Lab, 2026-11-16).

For `h : ℝ → ℂ` vanishing outside `[c, c + w]`, with `h` and `‖h‖²` integrable,

  ∫ u, ‖∫ v, h (v + u) * conj (h v)‖ ≤ w · ∫ ‖h‖².

`WeilWidthArchCorrelationV25` proves only the pointwise bound `‖C_g(u)‖ ≤ E`; integrating that over the
support-difference interval (width 2w) gives the factor 2w used by `WeilSeparatedArchBridgeV31`. This lemma gives
the factor w instead. It is the step behind the constant 30/649 in the dyadic Archimedean decay bound
`|B_arch(g, T_{k log 2} g)| ≤ (30/649) 2^{-5k/2} E(g)` (packets of log-width ≤ 1/32).

`l1_crosscorr_le` is the two-packet form: for `h`, `k` supported on intervals of length `w`,
`∫ u, ‖∫ v, h (v + u) conj (k v)‖ ≤ (w/2)(∫ ‖h‖² + ∫ ‖k‖²)`, against `2w · max‖C‖ ≤ w(∫ ‖h‖² + ∫ ‖k‖²)`
for the pointwise route.

Abstract real analysis only: Fubini through `integral_convolution`, and Cauchy–Schwarz on the support through
the discriminant of `t ↦ ∫_I (|h| − t)²`. No Weil kernel, no global sign, not RH.
-/

open MeasureTheory Set ComplexConjugate
open scoped Convolution
noncomputable section
namespace AEGIS.WeilLogCorrelationL1V1

/-- The autocorrelation of a real function is the convolution of its reflection with itself. -/
theorem autocorr_eq_convolution (a : ℝ → ℝ) (u : ℝ) :
    ∫ v, a (v + u) * a v = ((fun t => a (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) u := by
  rw [convolution_lsmul]
  calc ∫ v, a (v + u) * a v = ∫ t, (fun v => a (v + u) * a v) (-t) :=
        (integral_neg_eq_self (fun v => a (v + u) * a v) volume).symm
    _ = ∫ t, (fun t => a (-t)) t • a (u - t) := by
        congr 1; funext t; simp only [smul_eq_mul]; rw [neg_add_eq_sub, mul_comm]

theorem integrable_autocorr (a : ℝ → ℝ) (ha : Integrable a) :
    Integrable (fun u => ∫ v, a (v + u) * a v) := by
  have h1 : (fun u => ∫ v, a (v + u) * a v) =
      ((fun t => a (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) := by
    funext u; exact autocorr_eq_convolution a u
  rw [h1]
  exact Integrable.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) ha.comp_neg ha

/-- Fubini for the autocorrelation: `∫ u, ∫ v, a (v + u) a v = (∫ a)²`. -/
theorem integral_autocorr_real (a : ℝ → ℝ) (ha : Integrable a) :
    ∫ u, ∫ v, a (v + u) * a v = (∫ x, a x) ^ 2 := by
  have h1 : (fun u => ∫ v, a (v + u) * a v) =
      ((fun t => a (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) := by
    funext u; exact autocorr_eq_convolution a u
  rw [h1, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) ha.comp_neg ha,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, integral_neg_eq_self a volume]
  ring

/-- Cauchy–Schwarz on the support `[c, c + w]`: `(∫ a)² ≤ w ∫ a²`. -/
theorem sq_integral_le_mul (a : ℝ → ℝ) (c w : ℝ) (hw : 0 ≤ w)
    (hsupp : ∀ x, x ∉ Icc c (c + w) → a x = 0) (ha : Integrable a)
    (ha2 : Integrable (fun x => a x ^ 2)) :
    (∫ x, a x) ^ 2 ≤ w * ∫ x, a x ^ 2 := by
  have hS : ∫ x in Icc c (c + w), a x = ∫ x, a x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  have hT : ∫ x in Icc c (c + w), a x ^ 2 = ∫ x, a x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hsupp x hx])
  have hvol : volume.real (Icc c (c + w)) = w := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hq : ∀ t : ℝ, 0 ≤ w * (t * t) + (-2 * ∫ x, a x) * t + ∫ x, a x ^ 2 := by
    intro t
    have h1 : Integrable (fun x => a x ^ 2) (volume.restrict (Icc c (c + w))) := ha2.restrict
    have h2 : Integrable (fun x => (2 * t) * a x) (volume.restrict (Icc c (c + w))) :=
      ha.restrict.const_mul _
    have h3 : Integrable (fun _ : ℝ => t ^ 2) (volume.restrict (Icc c (c + w))) := integrable_const _
    have hexp : (∫ x in Icc c (c + w), (a x - t) ^ 2) =
        (∫ x in Icc c (c + w), a x ^ 2) - (2 * t) * (∫ x in Icc c (c + w), a x) + t ^ 2 * w := by
      have hfun : (fun x => (a x - t) ^ 2) = fun x => (a x ^ 2 - (2 * t) * a x) + t ^ 2 := by
        funext x; ring
      have e1 : (∫ x in Icc c (c + w), (a x ^ 2 - (2 * t) * a x + t ^ 2)) =
          (∫ x in Icc c (c + w), (a x ^ 2 - (2 * t) * a x)) + ∫ x in Icc c (c + w), t ^ 2 :=
        integral_add (h1.sub h2) h3
      have e2 : (∫ x in Icc c (c + w), (a x ^ 2 - (2 * t) * a x)) =
          (∫ x in Icc c (c + w), a x ^ 2) - ∫ x in Icc c (c + w), (2 * t) * a x :=
        integral_sub h1 h2
      rw [hfun, e1, e2, integral_const_mul, setIntegral_const, hvol, smul_eq_mul]
      ring
    have hnn : 0 ≤ ∫ x in Icc c (c + w), (a x - t) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)
    rw [hexp, hS, hT] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

/-- **L¹ bound.** For `h` vanishing outside `[c, c + w]`:
`∫ u, ‖∫ v, h (v + u) · conj (h v)‖ ≤ w · ∫ ‖h‖²`. -/
theorem l1_autocorr_le (h : ℝ → ℂ) (c w : ℝ) (hw : 0 ≤ w)
    (hsupp : ∀ x, x ∉ Icc c (c + w) → h x = 0) (hi : Integrable h)
    (hi2 : Integrable (fun x => ‖h x‖ ^ 2)) :
    ∫ u, ‖∫ v, h (v + u) * conj (h v)‖ ≤ w * ∫ x, ‖h x‖ ^ 2 := by
  have ha : Integrable (fun x => ‖h x‖) := hi.norm
  calc ∫ u, ‖∫ v, h (v + u) * conj (h v)‖ ≤ ∫ u, ∫ v, ‖h (v + u)‖ * ‖h v‖ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
        · exact integrable_autocorr (fun x => ‖h x‖) ha
        · refine Filter.Eventually.of_forall (fun u => ?_)
          calc ‖∫ v, h (v + u) * conj (h v)‖ ≤ ∫ v, ‖h (v + u) * conj (h v)‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ v, ‖h (v + u)‖ * ‖h v‖ := by
                congr 1; funext v; rw [norm_mul, Complex.norm_conj]
    _ = (∫ x, ‖h x‖) ^ 2 := integral_autocorr_real (fun x => ‖h x‖) ha
    _ ≤ w * ∫ x, ‖h x‖ ^ 2 :=
        sq_integral_le_mul (fun x => ‖h x‖) c w hw (fun x hx => by simp [hsupp x hx]) ha hi2

/-! ### Cross-correlation of two packets -/

theorem crosscorr_eq_convolution (a b : ℝ → ℝ) (u : ℝ) :
    ∫ v, a (v + u) * b v = ((fun t => b (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) u := by
  rw [convolution_lsmul]
  calc ∫ v, a (v + u) * b v = ∫ t, (fun v => a (v + u) * b v) (-t) :=
        (integral_neg_eq_self (fun v => a (v + u) * b v) volume).symm
    _ = ∫ t, (fun t => b (-t)) t • a (u - t) := by
        congr 1; funext t; simp only [smul_eq_mul]; rw [neg_add_eq_sub, mul_comm]

theorem integrable_crosscorr (a b : ℝ → ℝ) (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun u => ∫ v, a (v + u) * b v) := by
  have h1 : (fun u => ∫ v, a (v + u) * b v) =
      ((fun t => b (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) := by
    funext u; exact crosscorr_eq_convolution a b u
  rw [h1]
  exact Integrable.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hb.comp_neg ha

/-- Fubini for the cross-correlation: `∫ u, ∫ v, a (v + u) b v = (∫ a)(∫ b)`. -/
theorem integral_crosscorr_real (a b : ℝ → ℝ) (ha : Integrable a) (hb : Integrable b) :
    ∫ u, ∫ v, a (v + u) * b v = (∫ x, a x) * ∫ x, b x := by
  have h1 : (fun u => ∫ v, a (v + u) * b v) =
      ((fun t => b (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) := by
    funext u; exact crosscorr_eq_convolution a b u
  rw [h1, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hb.comp_neg ha,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, integral_neg_eq_self b volume]
  ring

/-- **Cross-correlation L¹ bound.** For `h`, `k` vanishing outside intervals of length `w`:
`∫ u, ‖∫ v, h (v + u) · conj (k v)‖ ≤ (w / 2) · (∫ ‖h‖² + ∫ ‖k‖²)`. -/
theorem l1_crosscorr_le (h k : ℝ → ℂ) (c d w : ℝ) (hw : 0 ≤ w)
    (hsupp : ∀ x, x ∉ Icc c (c + w) → h x = 0) (ksupp : ∀ x, x ∉ Icc d (d + w) → k x = 0)
    (hi : Integrable h) (ki : Integrable k)
    (hi2 : Integrable (fun x => ‖h x‖ ^ 2)) (ki2 : Integrable (fun x => ‖k x‖ ^ 2)) :
    ∫ u, ‖∫ v, h (v + u) * conj (k v)‖ ≤ (w / 2) * ((∫ x, ‖h x‖ ^ 2) + ∫ x, ‖k x‖ ^ 2) := by
  have ha : Integrable (fun x => ‖h x‖) := hi.norm
  have hb : Integrable (fun x => ‖k x‖) := ki.norm
  have hA : (∫ x, ‖h x‖) ^ 2 ≤ w * ∫ x, ‖h x‖ ^ 2 :=
    sq_integral_le_mul (fun x => ‖h x‖) c w hw (fun x hx => by simp [hsupp x hx]) ha hi2
  have hB : (∫ x, ‖k x‖) ^ 2 ≤ w * ∫ x, ‖k x‖ ^ 2 :=
    sq_integral_le_mul (fun x => ‖k x‖) d w hw (fun x hx => by simp [ksupp x hx]) hb ki2
  calc ∫ u, ‖∫ v, h (v + u) * conj (k v)‖ ≤ ∫ u, ∫ v, ‖h (v + u)‖ * ‖k v‖ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
        · exact integrable_crosscorr (fun x => ‖h x‖) (fun x => ‖k x‖) ha hb
        · refine Filter.Eventually.of_forall (fun u => ?_)
          calc ‖∫ v, h (v + u) * conj (k v)‖ ≤ ∫ v, ‖h (v + u) * conj (k v)‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ v, ‖h (v + u)‖ * ‖k v‖ := by
                congr 1; funext v; rw [norm_mul, Complex.norm_conj]
    _ = (∫ x, ‖h x‖) * ∫ x, ‖k x‖ :=
        integral_crosscorr_real (fun x => ‖h x‖) (fun x => ‖k x‖) ha hb
    _ ≤ (w / 2) * ((∫ x, ‖h x‖ ^ 2) + ∫ x, ‖k x‖ ^ 2) := by
        nlinarith [sq_nonneg ((∫ x, ‖h x‖) - ∫ x, ‖k x‖), hA, hB]

end AEGIS.WeilLogCorrelationL1V1

#print axioms AEGIS.WeilLogCorrelationL1V1.l1_autocorr_le
#print axioms AEGIS.WeilLogCorrelationL1V1.sq_integral_le_mul
#print axioms AEGIS.WeilLogCorrelationL1V1.integral_autocorr_real
#print axioms AEGIS.WeilLogCorrelationL1V1.l1_crosscorr_le
