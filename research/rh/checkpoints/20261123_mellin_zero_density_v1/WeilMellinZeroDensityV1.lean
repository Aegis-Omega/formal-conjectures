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

import WeilStrictSignMellinV1
import WeilMellinInversionV1
import Hadamard.OrderOne.ZeroCountingBounds

/-!
AEGIS Ω — `MellinZeroNonvanishing` from a count of the distinct zeros of `ζ` (Claude Lab, 2026-11-23).

`DistinctZeroSuperlinear`: for every `C` there is a radius `R ≥ 1` and more than `C · R` distinct nontrivial
zeros of `ζ` of modulus at most `R`. The statement involves only `ζ`.

* `mellin_differentiable`, `norm_mellin_le`: the Mellin transform of a compactly supported smooth packet is
  entire, of exponential type.
* `exists_mellin_ne_zero`: it is not identically zero unless the packet is (Mellin inversion,
  `weil_compact_smooth_mellin_inversion_v1`).
* `mellinZeroNonvanishing_of_distinctZeroSuperlinear`: by Jensen's formula
  (`Hadamard.ZeroCounting.card_zeros_le_of_max_one_maxModulus`), an entire function of exponential type that is
  not identically zero has `O(R)` distinct zeros in a disk of radius `R`. So it cannot vanish at superlinearly
  many points.
* `strictWeilSign_of_rh_distinct`, `fineBudget_of_rh_distinct`: with RH as a hypothesis.

`DistinctZeroSuperlinear` is NOT proved here. Not RH.
-/

open Set Complex Metric Filter Topology MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace AEGIS.WeilMellinZeroDensityV1

open AEGIS.WeilFineBudgetEquivV1 AEGIS.WeilStrictSignMellinV1

/-- More than `C · R` distinct nontrivial zeros of modulus at most `R`, for every `C` and some `R ≥ 1`. -/
def DistinctZeroSuperlinear : Prop :=
  ∀ C : ℝ, ∃ R : ℝ, 1 ≤ R ∧ ∃ S : Finset RiemannNontrivialZeroIndexV2,
    (∀ ρ ∈ S, ‖ρ.1‖ ≤ R) ∧ C * R < S.card

/-- A packet vanishes outside some `[A, B]` with `0 < A`. -/
theorem support_bounds (g : WeilCompactSmoothGV1) :
    ∃ A B : ℝ, 0 < A ∧ ∀ t : ℝ, g.1 t ≠ 0 → A ≤ t ∧ t ≤ B := by
  have hK : IsCompact (tsupport g.1) := g.2.2.1
  rcases (tsupport g.1).eq_empty_or_nonempty with h | h
  · refine ⟨1, 1, one_pos, fun t ht => ?_⟩
    have htK : t ∈ tsupport g.1 := subset_tsupport g.1 (Function.mem_support.mpr ht)
    rw [h] at htK
    exact absurd htK (Set.notMem_empty t)
  · obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn h continuous_id.continuousOn
    obtain ⟨B, hB⟩ := hK.bddAbove
    refine ⟨a, B, g.2.2.2 ha, fun t ht => ?_⟩
    have htK : t ∈ tsupport g.1 := subset_tsupport g.1 (Function.mem_support.mpr ht)
    exact ⟨by simpa using hamin htK, hB htK⟩

/-- The Mellin transform of a packet is entire. -/
theorem mellin_differentiable (g : WeilCompactSmoothGV1) : Differentiable ℂ (mellin g.1) := by
  obtain ⟨A, B, hA, hAB⟩ := support_bounds g
  intro s
  have htop : ∀ᶠ t in atTop, g.1 t = 0 := by
    filter_upwards [eventually_gt_atTop B] with t ht
    by_contra hne
    exact absurd (hAB t hne).2 (not_le.mpr ht)
  have hbot : ∀ᶠ t in 𝓝[>] (0 : ℝ), g.1 t = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hA] with t ht
    by_contra hne
    exact absurd (hAB t hne).1 (not_le.mpr ht.2)
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (g.2.1.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · exact (Asymptotics.isBigO_zero _ _).congr' (htop.mono fun t ht => ht.symm) EventuallyEq.rfl
  · exact (Asymptotics.isBigO_zero _ _).congr' (hbot.mono fun t ht => ht.symm) EventuallyEq.rfl

/-- Exponential type: `‖M g(s)‖ ≤ exp(c (‖s‖ + 1)) · ∫ ‖g‖` with `c = |log A| + |log B|`. -/
theorem norm_mellin_le (g : WeilCompactSmoothGV1) {A B : ℝ} (hA : 0 < A)
    (hAB : ∀ t : ℝ, g.1 t ≠ 0 → A ≤ t ∧ t ≤ B) (s : ℂ) :
    ‖mellin g.1 s‖ ≤ Real.exp ((|Real.log A| + |Real.log B|) * (‖s‖ + 1)) *
      ∫ t in Ioi (0 : ℝ), ‖g.1 t‖ := by
  set E : ℝ := Real.exp ((|Real.log A| + |Real.log B|) * (‖s‖ + 1)) with hE
  have hint : Integrable (fun t => ‖g.1 t‖) (volume.restrict (Ioi (0 : ℝ))) :=
    (g.2.1.continuous.integrable_of_hasCompactSupport g.2.2.1).norm.integrableOn
  have key : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ (s - 1) • g.1 t‖ ≤ E * ‖g.1 t‖ := by
    intro t ht
    rw [norm_smul]
    by_cases hg : g.1 t = 0
    · simp [hg]
    obtain ⟨hAt, htB⟩ := hAB t hg
    have hcp : ‖(t : ℂ) ^ (s - 1)‖ ≤ E := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_def_of_pos ht, hE]
      apply Real.exp_le_exp.mpr
      have hlogA : Real.log A ≤ Real.log t := Real.log_le_log hA hAt
      have hlogB : Real.log t ≤ Real.log B := Real.log_le_log ht htB
      have habs : |Real.log t| ≤ |Real.log A| + |Real.log B| := by
        rw [abs_le]
        constructor
        · have h1 := neg_abs_le (Real.log A)
          have h2 := abs_nonneg (Real.log B)
          linarith
        · have h1 := le_abs_self (Real.log B)
          have h2 := abs_nonneg (Real.log A)
          linarith
      have hre : |(s - 1).re| ≤ ‖s‖ + 1 := by
        calc |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
          _ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖s‖ + 1 := by simp
      calc Real.log t * (s - 1).re ≤ |Real.log t * (s - 1).re| := le_abs_self _
        _ = |Real.log t| * |(s - 1).re| := abs_mul _ _
        _ ≤ (|Real.log A| + |Real.log B|) * (‖s‖ + 1) :=
            mul_le_mul habs hre (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hcp (norm_nonneg _)
  rw [mellin]
  calc ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • g.1 t‖
      ≤ ∫ t in Ioi (0 : ℝ), E * ‖g.1 t‖ := by
        refine norm_integral_le_of_norm_le (hint.const_mul E) ?_
        exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => key t ht)
    _ = E * ∫ t in Ioi (0 : ℝ), ‖g.1 t‖ := integral_const_mul E _

/-- A nonzero packet has a Mellin transform that is nonzero somewhere. -/
theorem exists_mellin_ne_zero (g : WeilCompactSmoothGV1) (hg0 : g.1 ≠ 0) :
    ∃ s : ℂ, mellin g.1 s ≠ 0 := by
  by_contra hall
  have hF : mellin g.1 = 0 := funext fun s => by
    by_contra hne
    exact hall ⟨s, hne⟩
  apply hg0
  funext x
  by_cases hx : 0 < x
  · rw [← weil_compact_smooth_mellin_inversion_v1 g 0 hx, hF]
    simp [mellinInv]
  · by_contra hne
    exact hx (g.2.2.2 (subset_tsupport g.1 (Function.mem_support.mpr hne)))

/-- **The reduction.** Superlinearly many distinct nontrivial zeros of `ζ` imply
`MellinZeroNonvanishing`. -/
theorem mellinZeroNonvanishing_of_distinctZeroSuperlinear (h : DistinctZeroSuperlinear) :
    MellinZeroNonvanishing := by
  intro g _hm hg0
  by_contra hall
  have hall' : ∀ r : RiemannNontrivialZeroIndexV2, mellin g.1 r.1 = 0 := fun r => by
    by_contra hne
    exact hall ⟨r, hne⟩
  obtain ⟨A, B, hA, hAB⟩ := support_bounds g
  obtain ⟨s0, hs0⟩ := exists_mellin_ne_zero g hg0
  set F : ℂ → ℂ := mellin g.1 with hFdef
  have hFd : Differentiable ℂ F := mellin_differentiable g
  set f : ℂ → ℂ := fun z => F (z + s0) with hfdef
  have hfd : Differentiable ℂ f := hFd.comp (differentiable_id.add_const s0)
  have hf0 : f 0 ≠ 0 := by simpa [hfdef] using hs0
  set c : ℝ := |Real.log A| + |Real.log B| with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set K : ℝ := ∫ t in Ioi (0 : ℝ), ‖g.1 t‖ with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set α : ℝ := c / Real.log 2 with hα
  set β : ℝ := (c * (‖s0‖ + 1) + Real.log (max 1 K) - Real.log ‖f 0‖) / Real.log 2 with hβ
  have hα0 : 0 ≤ α := div_nonneg hc0 hlog2.le
  -- Jensen: at most `α R + β` distinct zeros of `f` in `‖u‖ ≤ R / 2`.
  have hcount : ∀ R : ℝ, 0 < R →
      (({u : ℂ | u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support ∧ ‖u‖ ≤ R / 2} :
        Set ℂ).ncard : ℝ) ≤ α * R + β := by
    intro R hR
    have hJ := Hadamard.ZeroCounting.card_zeros_le_of_max_one_maxModulus f hR hfd hf0
    have hM : Hadamard.maxModulus f R ≤ Real.exp (c * (R + ‖s0‖ + 1)) * K := by
      refine Hadamard.maxModulus_le_of_forall_norm_le f hfd.continuous hR.le fun z hz => ?_
      have h1 := norm_mellin_le g hA hAB (z + s0)
      have h2 : ‖z + s0‖ ≤ R + ‖s0‖ := by
        calc ‖z + s0‖ ≤ ‖z‖ + ‖s0‖ := norm_add_le _ _
          _ = R + ‖s0‖ := by rw [hz]
      have h3 : Real.exp (c * (‖z + s0‖ + 1)) ≤ Real.exp (c * (R + ‖s0‖ + 1)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith) hc0
      calc ‖f z‖ = ‖mellin g.1 (z + s0)‖ := rfl
        _ ≤ Real.exp (c * (‖z + s0‖ + 1)) * K := h1
        _ ≤ Real.exp (c * (R + ‖s0‖ + 1)) * K := mul_le_mul_of_nonneg_right h3 hK0
    have hx0 : 0 ≤ c * (R + ‖s0‖ + 1) := mul_nonneg hc0 (by positivity)
    have hex : 1 ≤ Real.exp (c * (R + ‖s0‖ + 1)) := Real.one_le_exp hx0
    have hmax : max 1 (Hadamard.maxModulus f R) ≤
        Real.exp (c * (R + ‖s0‖ + 1)) * max 1 K := by
      apply max_le
      · calc (1 : ℝ) ≤ Real.exp (c * (R + ‖s0‖ + 1)) := hex
          _ ≤ Real.exp (c * (R + ‖s0‖ + 1)) * max 1 K :=
            le_mul_of_one_le_right (by positivity) (le_max_left _ _)
      · calc Hadamard.maxModulus f R ≤ Real.exp (c * (R + ‖s0‖ + 1)) * K := hM
          _ ≤ Real.exp (c * (R + ‖s0‖ + 1)) * max 1 K :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    have hlog : Real.log (max 1 (Hadamard.maxModulus f R)) ≤
        c * (R + ‖s0‖ + 1) + Real.log (max 1 K) := by
      have hpos : 0 < max 1 (Hadamard.maxModulus f R) := lt_of_lt_of_le one_pos (le_max_left _ _)
      calc Real.log (max 1 (Hadamard.maxModulus f R))
          ≤ Real.log (Real.exp (c * (R + ‖s0‖ + 1)) * max 1 K) := Real.log_le_log hpos hmax
        _ = c * (R + ‖s0‖ + 1) + Real.log (max 1 K) := by
            rw [Real.log_mul (Real.exp_pos _).ne' (lt_of_lt_of_le one_pos (le_max_left _ _)).ne',
              Real.log_exp]
    calc _ ≤ (Real.log (max 1 (Hadamard.maxModulus f R)) - Real.log ‖f 0‖) / Real.log 2 := hJ
      _ ≤ (c * (R + ‖s0‖ + 1) + Real.log (max 1 K) - Real.log ‖f 0‖) / Real.log 2 :=
          div_le_div_of_nonneg_right (by linarith) hlog2.le
      _ = α * R + β := by
          rw [hα, hβ, div_mul_eq_mul_div, ← add_div]
          congr 1
          ring
  -- The zeros of `ζ` give that many zeros of `f`.
  obtain ⟨R', hR'1, S, hSR, hScard⟩ := h (2 * α + |2 * α * ‖s0‖ + β|)
  set R : ℝ := 2 * (R' + ‖s0‖) with hRdef
  have hR : 0 < R := by
    have := norm_nonneg s0
    rw [hRdef]
    linarith
  set T : Set ℂ :=
    {u : ℂ | u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support ∧ ‖u‖ ≤ R / 2} with hT
  have hTfin : T.Finite :=
    ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).finiteSupport
      (isCompact_closedBall _ _)).subset fun u hu => hu.1
  have hmaps : ∀ ρ ∈ (S : Set RiemannNontrivialZeroIndexV2), ρ.1 - s0 ∈ T := by
    intro ρ hρ
    have hnorm : ‖ρ.1 - s0‖ ≤ R / 2 := by
      calc ‖ρ.1 - s0‖ ≤ ‖ρ.1‖ + ‖s0‖ := norm_sub_le _ _
        _ ≤ R' + ‖s0‖ := by linarith [hSR ρ (Finset.mem_coe.mp hρ)]
        _ = R / 2 := by rw [hRdef]; ring
    have hmem : ρ.1 - s0 ∈ closedBall (0 : ℂ) |R| := by
      rw [mem_closedBall, dist_zero_right, abs_of_pos hR]
      linarith
    have hzero : f (ρ.1 - s0) = 0 := by
      simp only [hfdef, sub_add_cancel]
      exact hall' ρ
    exact ⟨Hadamard.OrderOne.mem_divisor_support_of_zero hfd hmem hf0 hzero, hnorm⟩
  have hinj : InjOn (fun ρ : RiemannNontrivialZeroIndexV2 => ρ.1 - s0)
      (S : Set RiemannNontrivialZeroIndexV2) := by
    intro ρ₁ _ ρ₂ _ he
    exact Subtype.ext (sub_left_injective he)
  have hle : (S.card : ℝ) ≤ T.ncard := by
    have := Set.ncard_le_ncard_of_injOn (fun ρ : RiemannNontrivialZeroIndexV2 => ρ.1 - s0) hmaps hinj hTfin
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hTle := hcount R hR
  have hbound : (S.card : ℝ) ≤ 2 * α * R' + (2 * α * ‖s0‖ + β) := by
    calc (S.card : ℝ) ≤ T.ncard := hle
      _ ≤ α * R + β := hTle
      _ = 2 * α * R' + (2 * α * ‖s0‖ + β) := by rw [hRdef]; ring
  have habs : (2 * α * ‖s0‖ + β) ≤ |2 * α * ‖s0‖ + β| * R' := by
    calc (2 * α * ‖s0‖ + β) ≤ |2 * α * ‖s0‖ + β| := le_abs_self _
      _ = |2 * α * ‖s0‖ + β| * 1 := (mul_one _).symm
      _ ≤ |2 * α * ‖s0‖ + β| * R' := mul_le_mul_of_nonneg_left hR'1 (abs_nonneg _)
  have hexp : (2 * α + |2 * α * ‖s0‖ + β|) * R' = 2 * α * R' + |2 * α * ‖s0‖ + β| * R' := by ring
  linarith

/-- With RH as a hypothesis, superlinearly many distinct zeros give the strict Weil sign. -/
theorem strictWeilSign_of_rh_distinct (hRH : RiemannHypothesis) (hD : DistinctZeroSuperlinear) :
    StrictWeilSign :=
  strictWeilSign_of_rh_mellin hRH (mellinZeroNonvanishing_of_distinctZeroSuperlinear hD)

/-- With RH as a hypothesis, superlinearly many distinct zeros give the per-packet fine budget for every
`c ≤ 43/10`. -/
theorem fineBudget_of_rh_distinct {c : ℝ} (hc : c ≤ 43 / 10) (hRH : RiemannHypothesis)
    (hD : DistinctZeroSuperlinear) : FineBudget c :=
  (fineBudget_iff_rh_and_mellin hc).mpr ⟨hRH, mellinZeroNonvanishing_of_distinctZeroSuperlinear hD⟩

end AEGIS.WeilMellinZeroDensityV1

#print axioms AEGIS.WeilMellinZeroDensityV1.mellinZeroNonvanishing_of_distinctZeroSuperlinear
#print axioms AEGIS.WeilMellinZeroDensityV1.strictWeilSign_of_rh_distinct
#print axioms AEGIS.WeilMellinZeroDensityV1.fineBudget_of_rh_distinct
