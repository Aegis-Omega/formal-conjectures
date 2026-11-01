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
# Every two-moment-zero packet is a moment-killer image, V1

`WeilMomentKillerConstructionV1` proves one direction: for smooth compactly supported `ψ`, the
function `momentKiller ψ = ψ' + ψ''` is smooth, compactly supported, and has
`∫ φ = 0` and `∫ φ(u) e^u du = 0`. This file proves the converse in the same log coordinate:

* `exists_momentKiller_eq_of_vanish`: if `φ` is smooth, vanishes for `u ≤ a` and for `u ≥ b`, and
  has both moments zero, then `φ = momentKiller ψ` for a smooth `ψ` that also vanishes for
  `u ≤ a` and for `u ≥ b`, so `ψ` lives in the same window as `φ`;
* `exists_momentKiller_eq`: the same with `HasCompactSupport` in place of an explicit window.

Together with the forward direction, the moment-killer is a bijection from smooth compactly
supported functions onto the smooth compactly supported functions with both moments zero
(injectivity is `eq_zero_of_momentKiller_eq_zero`).

The construction is two primitives: `A u = ∫_a^u φ`, `B u = ∫_a^u e^t A(t) dt`, `ψ u = e^{-u} B u`.
Then `ψ' = A - ψ` and `ψ'' = φ - ψ'`. The first moment makes `A` vanish beyond `b`; the second makes
`B` vanish beyond `b`, because `(e^t A)' = e^t A + e^t φ` integrates to zero over `[a, u]`.

The multiplicative packets of `WeilMomentConditionsV1` are related to this coordinate by
`x = e^u` (`WeilLogChangeOfVariablesV1`); this file does not perform that transport. It proves no
sign of the Weil form and nothing about RH.
-/

open MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace AEGIS.WeilMomentKillerRangeV1

open AEGIS.WeilMomentKillerConstructionV1

/-- The primitive `u ↦ ∫_a^u f`. -/
def prim (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := ∫ t in a..u, f t

theorem hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (a u : ℝ) :
    HasDerivAt (prim a f) (f u) u :=
  (hf.integral_hasStrictDerivAt a u).hasDerivAt

theorem deriv_prim {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) : deriv (prim a f) = f :=
  funext fun u => (hasDerivAt_prim hf a u).deriv

theorem contDiff_prim {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) : ContDiff ℝ ∞ (prim a f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun u => (hasDerivAt_prim hf.continuous a u).differentiableAt, ?_⟩
  rw [deriv_prim hf.continuous]
  exact hf

/-- The primitive vanishes left of `a` when `f` does. -/
theorem prim_eq_zero_left {f : ℝ → ℝ} {a u : ℝ} (hf : ∀ t, t ≤ a → f t = 0) (hu : u ≤ a) :
    prim a f u = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
  · simp
  · intro t ht
    rw [uIcc_of_ge hu] at ht
    exact hf t ht.2

/-- Right of the window the primitive is the full integral. -/
theorem prim_eq_integral {f : ℝ → ℝ} {a b u : ℝ} (hf : ∀ t, t ≤ a → f t = 0)
    (hg : ∀ t, b ≤ t → f t = 0) (hab : a ≤ b) (hu : b ≤ u) :
    prim a f u = ∫ t, f t := by
  unfold prim
  rw [intervalIntegral.integral_of_le (hab.trans hu)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with h | h
  · exact hf t h
  · exact hg t (hu.trans h.le)

section Window

variable {φ : ℝ → ℝ} {a b : ℝ}

/-- The converse of the moment-killer construction on an explicit window `[a, b]`. -/
theorem exists_momentKiller_eq_of_vanish (hab : a ≤ b) (hφ : ContDiff ℝ ∞ φ)
    (hl : ∀ t, t ≤ a → φ t = 0) (hr : ∀ t, b ≤ t → φ t = 0)
    (h1 : ∫ u, φ u = 0) (h2 : ∫ u, φ u * Real.exp u = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, t ≤ a → ψ t = 0) ∧ (∀ t, b ≤ t → ψ t = 0) ∧
      momentKiller ψ = φ := by
  set A := prim a φ with hA_def
  have hAs : ContDiff ℝ ∞ A := contDiff_prim hφ a
  have hAl : ∀ t, t ≤ a → A t = 0 := fun t ht => prim_eq_zero_left hl ht
  have hAr : ∀ t, b ≤ t → A t = 0 := fun t ht => by
    rw [hA_def, prim_eq_integral hl hr hab ht, h1]
  set g : ℝ → ℝ := fun t => Real.exp t * A t with hg_def
  have hgs : ContDiff ℝ ∞ g := Real.contDiff_exp.mul hAs
  set B := prim a g with hB_def
  have hBs : ContDiff ℝ ∞ B := contDiff_prim hgs a
  have hgl : ∀ t, t ≤ a → g t = 0 := fun t ht => by simp [hg_def, hAl t ht]
  have hBl : ∀ t, t ≤ a → B t = 0 := fun t ht => prim_eq_zero_left hgl ht
  -- second moment: `B` vanishes right of `b`
  have hBr : ∀ u, b ≤ u → B u = 0 := by
    intro u hu
    set e : ℝ → ℝ := fun t => φ t * Real.exp t with he_def
    have hec : Continuous e := hφ.continuous.mul Real.continuous_exp
    have hgc : Continuous g := hgs.continuous
    have hderiv : ∀ t, HasDerivAt (fun t => Real.exp t * A t) (g t + e t) t := by
      intro t
      refine ((Real.hasDerivAt_exp t).fun_mul (hasDerivAt_prim hφ.continuous a t)).congr_deriv ?_
      simp only [hg_def, he_def, hA_def]
      ring
    have hftc : ∫ t in a..u, (g t + e t) = Real.exp u * A u - Real.exp a * A a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        ((hgc.add hec).intervalIntegrable a u)
    rw [hAr u hu, hAl a le_rfl, mul_zero, mul_zero, sub_zero,
      intervalIntegral.integral_add (hgc.intervalIntegrable a u) (hec.intervalIntegrable a u)]
      at hftc
    have hel : ∀ t, t ≤ a → e t = 0 := fun t ht => by simp [he_def, hl t ht]
    have her : ∀ t, b ≤ t → e t = 0 := fun t ht => by simp [he_def, hr t ht]
    have heint : ∫ t in a..u, e t = 0 := by
      have := prim_eq_integral hel her hab hu
      unfold prim at this
      rw [this]
      exact h2
    rw [heint, add_zero] at hftc
    exact hftc
  set ψ : ℝ → ℝ := fun u => Real.exp (-u) * B u with hψ_def
  have hψs : ContDiff ℝ ∞ ψ := (Real.contDiff_exp.comp contDiff_neg).mul hBs
  -- `ψ' = A - ψ`
  have hψ' : ∀ u, HasDerivAt ψ (A u - ψ u) u := by
    intro u
    have hE := (hasDerivAt_neg u).exp
    refine (hE.fun_mul (hasDerivAt_prim hgs.continuous a u)).congr_deriv ?_
    have hone : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    simp only [hψ_def, hg_def, hB_def]
    linear_combination (A u) * hone
  have hdψ : deriv ψ = fun u => A u - ψ u := funext fun u => (hψ' u).deriv
  -- `ψ'' = φ - ψ'`
  have hψ'' : ∀ u, HasDerivAt (fun u => A u - ψ u) (φ u - (A u - ψ u)) u :=
    fun u => (hasDerivAt_prim hφ.continuous a u).sub (hψ' u)
  have hddψ : deriv (deriv ψ) = fun u => φ u - (A u - ψ u) := by
    rw [hdψ]
    exact funext fun u => (hψ'' u).deriv
  refine ⟨ψ, hψs, fun t ht => ?_, fun t ht => ?_, ?_⟩
  · simp [hψ_def, hBl t ht]
  · simp [hψ_def, hBr t ht]
  · funext u
    simp only [momentKiller]
    rw [hddψ, hdψ]
    dsimp only
    ring

/-- The converse of the moment-killer construction, compact-support form. -/
theorem exists_momentKiller_eq (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (h1 : ∫ u, φ u = 0) (h2 : ∫ u, φ u * Real.exp u = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ momentKiller ψ = φ := by
  obtain ⟨r, hr⟩ := hc.isBounded.subset_ball (0 : ℝ)
  set R := max r 0 with hR_def
  have hR0 : 0 ≤ R := le_max_right r 0
  have hz : ∀ t, R ≤ |t| → φ t = 0 := by
    intro t ht
    by_contra h
    have hm := hr (subset_tsupport φ (Function.mem_support.2 h))
    rw [mem_ball, Real.dist_eq, sub_zero] at hm
    linarith [le_max_left r 0]
  have hl : ∀ t, t ≤ -R → φ t = 0 := fun t ht => hz t (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hrt : ∀ t, R ≤ t → φ t = 0 := fun t ht => hz t (by rw [abs_of_nonneg (by linarith)]; exact ht)
  obtain ⟨ψ, hψs, hψl, hψr, hψ⟩ :=
    exists_momentKiller_eq_of_vanish (by linarith) hφ hl hrt h1 h2
  refine ⟨ψ, hψs, HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_, hψ⟩
  intro t ht
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · exact hψl t h.le
  · exact hψr t h.le

end Window

end AEGIS.WeilMomentKillerRangeV1

#print axioms AEGIS.WeilMomentKillerRangeV1.exists_momentKiller_eq_of_vanish
#print axioms AEGIS.WeilMomentKillerRangeV1.exists_momentKiller_eq
