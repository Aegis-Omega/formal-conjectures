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

import WeilMomentKillerConstructionV1

/-!
# The converse of the moment killer

`AEGIS.WeilMomentKillerConstructionV1.momentKiller ψ = ψ' + ψ''` sends a smooth compactly supported `ψ`
to a smooth compactly supported `φ` with `∫ φ = 0` and `∫ φ eᵘ = 0` (`integral_momentKiller`,
`integral_momentKiller_mul_exp`), and it only kills zero (`eq_zero_of_momentKiller_eq_zero`).

This module proves the converse (HOLON OPTIMUS V2): every smooth compactly supported `φ` with both
moments zero is `momentKiller ψ` for exactly one smooth compactly supported `ψ`, the potential

    ψ(t) = ∫_{-A}^{t} (1 − e^{s−t}) φ(s) ds = Φ₀(t) − e^{−t} Φ₁(t),
    Φ₀(t) = ∫_{-A}^{t} φ,   Φ₁(t) = ∫_{-A}^{t} φ(s) eˢ ds,

for any `A ≥ 0` with `tsupport φ ⊆ Ioo (-A) A` (`exists_momentKiller_eq`, `momentKiller_injective`).
Beyond `A` the potential is `∫ φ − e^{−t} ∫ φ eˢ`, so it has compact support exactly because both
moments vanish (`pot_eq_zero`). For complex test functions apply this to the real and imaginary parts.
Not RH.
-/

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace AEGIS.WeilMomentKillerInverseV1

open AEGIS.WeilMomentKillerConstructionV1 (momentKiller)

/-- `∫_a^t f`. -/
def prim (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in a..t, f s

theorem hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (prim a f) (f t) t :=
  (hf.integral_hasStrictDerivAt a t).hasDerivAt

theorem deriv_prim {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) : deriv (prim a f) = f :=
  funext fun t => (hasDerivAt_prim hf a t).deriv

theorem contDiff_prim {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) : ContDiff ℝ ∞ (prim a f) :=
  contDiff_infty_iff_deriv.mpr ⟨fun t => (hasDerivAt_prim hf.continuous a t).differentiableAt,
    by rw [deriv_prim hf.continuous]; exact hf⟩

theorem prim_eq_zero_of_le (A : ℝ) {f : ℝ → ℝ} (hf0 : ∀ x, x ≤ -A → f x = 0) {t : ℝ}
    (ht : t ≤ -A) : prim (-A) f t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_]
  · simp
  · rw [Set.uIcc_of_ge ht] at hx
    exact hf0 x hx.2

theorem prim_eq_integral (A : ℝ) (hA0 : 0 ≤ A) {f : ℝ → ℝ}
    (hf0 : ∀ x, x ∉ Ioo (-A) A → f x = 0) {t : ℝ} (ht : A ≤ t) :
    prim (-A) f t = ∫ x, f x := by
  unfold prim
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hf0 x fun h => hx ⟨h.1, h.2.le.trans ht⟩

theorem exists_A {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    ∃ A : ℝ, 0 ≤ A ∧ tsupport φ ⊆ Ioo (-A) A := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun x hx => ?_⟩
  have h := hR hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have h3 := le_abs_self R
  exact ⟨by linarith, by linarith⟩

/-- The potential `Φ₀(t) − e^{−t} Φ₁(t)`. -/
def pot (A : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  prim (-A) φ t - Real.exp (-t) * prim (-A) (fun s => φ s * Real.exp s) t

theorem hasDerivAt_exp_neg (t : ℝ) :
    HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t :=
  ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring)

theorem exp_neg_mul_mul_exp (t c : ℝ) : Real.exp (-t) * (c * Real.exp t) = c := by
  rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

section

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (A : ℝ)
include hφ

theorem cont1 : Continuous fun s => φ s * Real.exp s := hφ.continuous.mul Real.continuous_exp

theorem hasDerivAt_pot (t : ℝ) :
    HasDerivAt (pot A φ) (Real.exp (-t) * prim (-A) (fun s => φ s * Real.exp s) t) t := by
  have h := (hasDerivAt_prim hφ.continuous (-A) t).sub
    ((hasDerivAt_exp_neg t).mul (hasDerivAt_prim (cont1 hφ) (-A) t))
  refine h.congr_deriv ?_
  rw [exp_neg_mul_mul_exp]
  ring

theorem deriv_pot :
    deriv (pot A φ) = fun t => Real.exp (-t) * prim (-A) (fun s => φ s * Real.exp s) t :=
  funext fun t => (hasDerivAt_pot hφ A t).deriv

theorem hasDerivAt_deriv_pot (t : ℝ) :
    HasDerivAt (deriv (pot A φ))
      (φ t - Real.exp (-t) * prim (-A) (fun s => φ s * Real.exp s) t) t := by
  rw [deriv_pot hφ A]
  have h := (hasDerivAt_exp_neg t).mul (hasDerivAt_prim (cont1 hφ) (-A) t)
  refine h.congr_deriv ?_
  rw [exp_neg_mul_mul_exp]
  ring

/-- **The potential is a preimage**: `ψ' + ψ'' = φ`. -/
theorem momentKiller_pot : momentKiller (pot A φ) = φ := by
  funext t
  show deriv (pot A φ) t + deriv (deriv (pot A φ)) t = φ t
  rw [(hasDerivAt_deriv_pot hφ A t).deriv, (hasDerivAt_pot hφ A t).deriv]
  ring

theorem contDiff_pot : ContDiff ℝ ∞ (pot A φ) :=
  (contDiff_prim hφ (-A)).sub
    ((Real.contDiff_exp.comp contDiff_neg).mul (contDiff_prim (hφ.mul Real.contDiff_exp) (-A)))

omit hφ in
/-- **Compact support from the two moments**: outside `[-A, A]` the potential vanishes. -/
theorem pot_eq_zero (hA0 : 0 ≤ A) (hA : tsupport φ ⊆ Ioo (-A) A) (h0 : ∫ u, φ u = 0)
    (h1 : ∫ u, φ u * Real.exp u = 0) {t : ℝ} (ht : t ∉ Icc (-A) A) : pot A φ t = 0 := by
  have hz : ∀ x, x ∉ Ioo (-A) A → φ x = 0 := fun x hx => by
    by_contra h
    exact hx (hA (subset_tsupport φ (Function.mem_support.mpr h)))
  have hz' : ∀ x, x ∉ Ioo (-A) A → φ x * Real.exp x = 0 := fun x hx => by rw [hz x hx, zero_mul]
  rcases not_and_or.mp ht with h | h
  · have ht' : t ≤ -A := (not_le.mp h).le
    have hb : ∀ x, x ≤ -A → φ x = 0 := fun x hx => hz x fun h' => by linarith [h'.1]
    have hb' : ∀ x, x ≤ -A → φ x * Real.exp x = 0 := fun x hx => by rw [hb x hx, zero_mul]
    simp only [pot, prim_eq_zero_of_le A hb ht', prim_eq_zero_of_le A hb' ht', mul_zero, sub_zero]
  · have ht' : A ≤ t := (not_le.mp h).le
    simp only [pot, prim_eq_integral A hA0 hz ht', prim_eq_integral A hA0 hz' ht', h0, h1, mul_zero,
      sub_zero]

end

/-- **The converse of the moment killer** (HOLON OPTIMUS V2). -/
theorem exists_momentKiller_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (h0 : ∫ u, φ u = 0) (h1 : ∫ u, φ u * Real.exp u = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ momentKiller ψ = φ := by
  obtain ⟨A, hA0, hA⟩ := exists_A hc
  exact ⟨pot A φ, contDiff_pot hφ A,
    HasCompactSupport.intro isCompact_Icc fun t ht => pot_eq_zero A hA0 hA h0 h1 ht,
    momentKiller_pot hφ A⟩

/-- **Uniqueness**: the preimage is unique among smooth compactly supported functions. -/
theorem momentKiller_injective {ψ₁ ψ₂ : ℝ → ℝ} (h1 : ContDiff ℝ ∞ ψ₁) (h2 : ContDiff ℝ ∞ ψ₂)
    (c1 : HasCompactSupport ψ₁) (c2 : HasCompactSupport ψ₂)
    (h : momentKiller ψ₁ = momentKiller ψ₂) : ψ₁ = ψ₂ := by
  have e1 : deriv (ψ₁ - ψ₂) = deriv ψ₁ - deriv ψ₂ := funext fun x =>
    deriv_sub ((h1.differentiable (by simp)) x) ((h2.differentiable (by simp)) x)
  have e2 : deriv (deriv ψ₁ - deriv ψ₂) = deriv (deriv ψ₁) - deriv (deriv ψ₂) := funext fun x =>
    deriv_sub ((AEGIS.WeilMomentKillerConstructionV1.differentiable_deriv h1) x)
      ((AEGIS.WeilMomentKillerConstructionV1.differentiable_deriv h2) x)
  have hd : momentKiller (ψ₁ - ψ₂) = 0 := by
    funext u
    have hu := congrFun h u
    simp only [momentKiller] at hu
    show deriv (ψ₁ - ψ₂) u + deriv (deriv (ψ₁ - ψ₂)) u = 0
    rw [e1, e2]
    simp only [Pi.sub_apply]
    linarith
  funext x
  have := AEGIS.WeilMomentKillerConstructionV1.eq_zero_of_momentKiller_eq_zero (h1.sub h2)
    (c1.sub c2) hd x
  simpa [sub_eq_zero] using this

end AEGIS.WeilMomentKillerInverseV1

end

#print axioms AEGIS.WeilMomentKillerInverseV1.exists_momentKiller_eq
#print axioms AEGIS.WeilMomentKillerInverseV1.momentKiller_injective
