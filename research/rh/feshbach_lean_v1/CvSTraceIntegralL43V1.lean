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

import CvSTraceCellL43V1

/-!
# From checked cells to the slack function and the trace integral at L = 4/3

For a list of cells that pass `cellOk`, the step function
`sFun cs t = Σ_c s_c · 𝟙[a_c ≤ |t| < b_c]` is measurable, bounded and nonnegative, and

* `integrable_mul`, `integral_mul_le`: `t ↦ sFun cs t · trialDist(t)` is integrable with
  integral at most `total k cs = Σ_c 2 (b_c − a_c) s_c TD_c`;
* `slack_ge`: if the cells chain from `0` to `tmax` and `h₊` clears `m + w₂⁺ + w₃⁺` at `tmax`,
  then `m − ScertM 3 t ≤ sFun cs t` for every real `t`.

Not RH.
-/

open MeasureTheory Set

noncomputable section

namespace AEGIS.CvSTraceIntegralL43V1

open AEGIS.CvSTraceCellL43V1 AEGIS.CvSTraceDistV1 AEGIS.CvSTraceV1 AEGIS.CvSTauPrimeL12V1
open AEGIS.CvSDiagL12V1 AEGIS.CvSHplusBoundsV1 AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauL12V1

def cellSet (c : Cell) : Set ℝ := {t | (c.a : ℝ) ≤ |t| ∧ |t| < c.b}

def sFun : List Cell → ℝ → ℝ
  | [], _ => 0
  | c :: cs, t => (cellSet c).indicator (fun _ => (c.s : ℝ)) t + sFun cs t

def bnd (k : Consts) : List Cell → ℝ → ℝ
  | [], _ => 0
  | c :: cs, t => (cellSet c).indicator (fun _ => (c.s : ℝ) * c.TD k) t + bnd k cs t

def total (k : Consts) : List Cell → ℚ
  | [] => 0
  | c :: cs => 2 * (c.b - c.a) * c.s * c.TD k + total k cs

def sMax : List Cell → ℚ
  | [] => 0
  | c :: cs => c.s + sMax cs

theorem cellSet_measurable (c : Cell) : MeasurableSet (cellSet c) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

theorem cellSet_sub (c : Cell) :
    cellSet c ⊆ Icc (c.a : ℝ) c.b ∪ Icc (-(c.b : ℝ)) (-(c.a : ℝ)) := by
  intro t ⟨h1, h2⟩
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at h1 h2
    exact Or.inl ⟨h1, h2.le⟩
  · rw [abs_of_nonpos h] at h1 h2
    exact Or.inr ⟨by linarith, by linarith⟩

theorem volume_cellSet_lt (c : Cell) : volume (cellSet c) < ⊤ :=
  (measure_mono (cellSet_sub c)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨measure_Icc_lt_top, measure_Icc_lt_top⟩))

theorem volume_cellSet_le (c : Cell) (hab : (c.a : ℝ) ≤ c.b) :
    (volume (cellSet c)).toReal ≤ 2 * ((c.b : ℝ) - c.a) := by
  have h1 : volume (cellSet c) ≤ ENNReal.ofReal ((c.b : ℝ) - c.a) + ENNReal.ofReal ((c.b : ℝ) - c.a) := by
    refine (measure_mono (cellSet_sub c)).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Icc, Real.volume_Icc, show -(c.a : ℝ) - -(c.b : ℝ) = c.b - c.a by ring]
  have h2 := ENNReal.toReal_mono (by finiteness) h1
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at h2
  linarith

theorem integrable_ind (c : Cell) (C : ℝ) : Integrable ((cellSet c).indicator fun _ => C) :=
  (integrable_indicator_iff (cellSet_measurable c)).2
    (integrableOn_const (volume_cellSet_lt c).ne)

theorem integral_ind_le (c : Cell) {C : ℝ} (hC : 0 ≤ C) (hab : (c.a : ℝ) ≤ c.b) :
    ∫ t, (cellSet c).indicator (fun _ => C) t ≤ 2 * ((c.b : ℝ) - c.a) * C := by
  rw [integral_indicator_const C (cellSet_measurable c), smul_eq_mul]
  have := volume_cellSet_le c hab
  simp only [measureReal_def]
  nlinarith

theorem sFun_measurable : ∀ cs : List Cell, Measurable (sFun cs)
  | [] => measurable_const
  | c :: cs => (measurable_const.indicator (cellSet_measurable c)).add (sFun_measurable cs)

variable {m : ℚ} {k : Consts}

theorem sFun_nonneg : ∀ {cs : List Cell}, (∀ c ∈ cs, cellOk m c = true) → ∀ t, 0 ≤ sFun cs t
  | [], _, _ => le_rfl
  | c :: cs, h, t => by
    have hs : (0 : ℝ) ≤ c.s := by exact_mod_cast (cellOk_facts (h c (by simp))).2.2.2.2.2.2.2.2.2.2.2.2.1
    have := sFun_nonneg (cs := cs) (fun c hc => h c (by simp [hc])) t
    simp only [sFun]
    exact add_nonneg (indicator_nonneg (fun _ _ => hs) _) this

theorem sFun_le : ∀ {cs : List Cell}, (∀ c ∈ cs, cellOk m c = true) → ∀ t, sFun cs t ≤ sMax cs
  | [], _, _ => by simp [sFun, sMax]
  | c :: cs, h, t => by
    have hs : (0 : ℝ) ≤ c.s := by exact_mod_cast (cellOk_facts (h c (by simp))).2.2.2.2.2.2.2.2.2.2.2.2.1
    have := sFun_le (cs := cs) (fun c hc => h c (by simp [hc])) t
    simp only [sFun, sMax, Rat.cast_add]
    have hi : (cellSet c).indicator (fun _ => (c.s : ℝ)) t ≤ c.s :=
      indicator_le_self' (fun _ _ => hs) t
    linarith

theorem sFun_ge : ∀ {cs : List Cell}, (∀ c ∈ cs, cellOk m c = true) → ∀ {c : Cell}, c ∈ cs →
    ∀ {t : ℝ}, t ∈ cellSet c → (c.s : ℝ) ≤ sFun cs t
  | [], _, _, hc, _, _ => by simp at hc
  | c' :: cs, h, c, hc, t, ht => by
    have hrest := sFun_nonneg (cs := cs) (fun c hc => h c (by simp [hc])) t
    have hs' : (0 : ℝ) ≤ c'.s := by exact_mod_cast (cellOk_facts (h c' (by simp))).2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [sFun]
    rcases List.mem_cons.mp hc with e | hc'
    · subst e
      rw [indicator_of_mem ht]
      linarith
    · have := sFun_ge (cs := cs) (fun c hc => h c (by simp [hc])) hc' ht
      have := indicator_nonneg (s := cellSet c') (fun _ _ => hs') t
      linarith

/-! ### The trace integral -/

theorem TD_nonneg {c : Cell} (hk : constOk k = true) (hc : cellOk m c = true)
    {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V) (hVc : ∀ i, Continuous (V i)) :
    (0 : ℝ) ≤ c.TD k := by
  obtain ⟨ha, hab, -⟩ := cellOk_facts hc
  have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have hab' : (c.a : ℝ) ≤ c.b := by exact_mod_cast hab.le
  have h := (cell_sound hk hc hV hVc (t := c.a) (by rw [abs_of_nonneg ha']) (by rwa [abs_of_nonneg ha'])).1
  refine le_trans ?_ h
  exact integral_nonneg fun _ => sq_nonneg _

theorem trialDist_nonneg (V : Fin 141 → ℝ → ℂ) (t : ℝ) : 0 ≤ trialDist 0 (4 / 3) V (cfC h43) t :=
  integral_nonneg fun _ => sq_nonneg _

theorem mul_le_bnd (hk : constOk k = true) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) :
    ∀ {cs : List Cell}, (∀ c ∈ cs, cellOk m c = true) → ∀ t,
      sFun cs t * trialDist 0 (4 / 3) V (cfC h43) t ≤ bnd k cs t
  | [], _, t => by simp [sFun, bnd]
  | c :: cs, h, t => by
    have hrest := mul_le_bnd hk hV hVc (cs := cs) (fun c hc => h c (by simp [hc])) t
    have hc := h c (by simp)
    have hs : (0 : ℝ) ≤ c.s := by exact_mod_cast (cellOk_facts hc).2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [sFun, bnd, add_mul]
    refine add_le_add ?_ hrest
    by_cases ht : t ∈ cellSet c
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      exact mul_le_mul_of_nonneg_left (cell_sound hk hc hV hVc ht.1 ht.2.le).1 hs
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]

theorem bnd_integrable : ∀ cs : List Cell, Integrable (bnd k cs)
  | [] => integrable_zero _ _ _
  | c :: cs => (integrable_ind c _).add (bnd_integrable cs)

theorem integral_bnd_le (hk : constOk k = true) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) :
    ∀ {cs : List Cell}, (∀ c ∈ cs, cellOk m c = true) → ∫ t, bnd k cs t ≤ total k cs
  | [], _ => by simp [bnd, total]
  | c :: cs, h => by
    have hrest := integral_bnd_le hk hV hVc (cs := cs) (fun c hc => h c (by simp [hc]))
    have hc := h c (by simp)
    obtain ⟨-, hab, -⟩ := cellOk_facts hc
    have hs : (0 : ℝ) ≤ c.s := by exact_mod_cast (cellOk_facts hc).2.2.2.2.2.2.2.2.2.2.2.2.1
    have hTD := TD_nonneg hk hc hV hVc
    have hab' : (c.a : ℝ) ≤ c.b := by exact_mod_cast hab.le
    simp only [bnd, total]
    rw [integral_add (integrable_ind c _) (bnd_integrable cs)]
    have := integral_ind_le c (mul_nonneg hs hTD) hab'
    push_cast
    nlinarith

theorem integrable_mul (hk : constOk k = true) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) {cs : List Cell} (h : ∀ c ∈ cs, cellOk m c = true) :
    Integrable fun t => sFun cs t * trialDist 0 (4 / 3) V (cfC h43) t := by
  refine (bnd_integrable (k := k) cs).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((sFun_measurable cs).mul (trialDist_continuous h43 hVc).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sFun_nonneg h t) (trialDist_nonneg V t))]
    exact mul_le_bnd hk hV hVc h t

theorem integral_mul_le (hk : constOk k = true) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) {cs : List Cell} (h : ∀ c ∈ cs, cellOk m c = true) :
    ∫ t, sFun cs t * trialDist 0 (4 / 3) V (cfC h43) t ≤ total k cs :=
  (integral_mono (integrable_mul hk hV hVc h) (bnd_integrable (k := k) cs) (mul_le_bnd hk hV hVc h)).trans
    (integral_bnd_le hk hV hVc h)

/-! ### The slack covers the symbol deficit -/

def chainOk : ℚ → List Cell → ℚ → Bool
  | a, [], hi => decide (a = hi)
  | a, c :: cs, hi => decide (c.a = a) && chainOk c.b cs hi

theorem chain_cover : ∀ {cs : List Cell} {a hi : ℚ}, chainOk a cs hi = true →
    ∀ {τ : ℝ}, (a : ℝ) ≤ τ → τ < hi → ∃ c ∈ cs, (c.a : ℝ) ≤ τ ∧ τ < c.b
  | [], a, hi, h, τ, h1, h2 => by
    simp only [chainOk, decide_eq_true_eq] at h
    subst h
    linarith
  | c :: cs, a, hi, h, τ, h1, h2 => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hb : τ < c.b
    · exact ⟨c, by simp, by rw [h.1]; exact h1, hb⟩
    · obtain ⟨c', hc', hh⟩ := chain_cover h.2 (not_lt.mp hb) h2
      exact ⟨c', by simp [hc'], hh⟩

theorem cell_slack {c : Cell} (hc : cellOk m c = true) {t : ℝ} (h1 : (c.a : ℝ) ≤ |t|) :
    (m : ℝ) - ScertM 3 t ≤ c.s := by
  obtain ⟨ha, -, -, -, -, -, -, -, -, -, -, -, -, hlog, hsl⟩ := cellOk_facts hc
  have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have hq : ((c.a ^ 2 : ℚ) : ℝ) ≤ t ^ 2 := by push_cast; rw [← sq_abs t]; nlinarith
  have hh := hplus_ge_of_sq (q := c.a ^ 2) (by positivity) hlog hq
  have hS := scertM_three_ge t
  have hs := (Rat.cast_le (K := ℝ)).mpr hsl
  push_cast at hs
  linarith

theorem slack_ge {cs : List Cell} (h : ∀ c ∈ cs, cellOk m c = true) {tmax : ℚ} (h0 : 0 ≤ tmax)
    (hch : chainOk 0 cs tmax = true) (hl : logOk (aK ^ 2 + tmax ^ 2) = true)
    (htail : m + w2Hi + w3Hi ≤ hpLo (tmax ^ 2) (tmax ^ 2)) (t : ℝ) :
    (m : ℝ) - ScertM 3 t ≤ sFun cs t := by
  by_cases ht : |t| < tmax
  · obtain ⟨c, hc, h1, h2⟩ := chain_cover hch (by push_cast; exact abs_nonneg t) ht
    exact (cell_slack (h c hc) h1).trans (sFun_ge h hc ⟨h1, h2⟩)
  · have h0' : (0 : ℝ) ≤ tmax := by exact_mod_cast h0
    have hq : ((tmax ^ 2 : ℚ) : ℝ) ≤ t ^ 2 := by
      push_cast; rw [← sq_abs t]; nlinarith [not_lt.mp ht]
    have hh := hplus_ge_of_sq (q := tmax ^ 2) (by positivity) hl hq
    have hS := scertM_three_ge t
    have hs := (Rat.cast_le (K := ℝ)).mpr htail
    push_cast at hs
    have := sFun_nonneg h t
    linarith

theorem total_append (l1 l2 : List Cell) : total k (l1 ++ l2) = total k l1 + total k l2 := by
  induction l1 with
  | nil => simp [total]
  | cons c cs ih => simp only [List.cons_append, total, ih]; ring

/-- **The trace premises from a checked cell list.** -/
theorem premises_of_cells (hk : constOk k = true) {cs : List Cell} (h : ∀ c ∈ cs, cellOk m c = true)
    {tmax : ℚ} (h0 : 0 ≤ tmax) (hch : chainOk 0 cs tmax = true)
    (hl : logOk (aK ^ 2 + tmax ^ 2) = true) (htail : m + w2Hi + w3Hi ≤ hpLo (tmax ^ 2) (tmax ^ 2))
    {T : ℚ} (hT : total k cs ≤ T) {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) :
    Measurable (sFun cs) ∧ (∀ t, |sFun cs t| ≤ (sMax cs : ℝ)) ∧ (∀ t, 0 ≤ sFun cs t) ∧
      (∀ t : ℝ, 0 ≤ Wt t * (ScertM 3 t - m) + Wt t * sFun cs t) ∧
      Integrable (fun t => sFun cs t * trialDist 0 (4 / 3) V (cfC h43) t) ∧
      (∫ t, sFun cs t * trialDist 0 (4 / 3) V (cfC h43) t) ≤ (T : ℝ) := by
  refine ⟨sFun_measurable cs, fun t => ?_, sFun_nonneg h, fun t => ?_, integrable_mul hk hV hVc h,
    (integral_mul_le hk hV hVc h).trans (by exact_mod_cast hT)⟩
  · rw [abs_of_nonneg (sFun_nonneg h t)]
    exact sFun_le h t
  · have hs := slack_ge h h0 hch hl htail t
    have hW : 0 ≤ Wt t := by unfold Wt; positivity
    rw [← mul_add]
    exact mul_nonneg hW (by linarith)

/-- `hk` of the window theorem at `L = 4/3`, with `κ = 52`, `m = 8/5` and any `T ≤ 7/2`. -/
theorem gap_of_T {T : ℚ} (hT : T ≤ 7 / 2) :
    52 ≤ (2 * Real.pi) ^ 2 * (4 / 3 : ℝ) * (8 / 5 - (T : ℝ) / (2 * Real.pi)) := by
  have hp := pi_bounds.1
  have hpos := Real.pi_pos
  have e : (2 * Real.pi) ^ 2 * (4 / 3 : ℝ) * (8 / 5 - (T : ℝ) / (2 * Real.pi)) =
      128 / 15 * Real.pi ^ 2 - 8 / 3 * T * Real.pi := by
    field_simp
    ring
  rw [e]
  have hT' : (T : ℝ) ≤ 7 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hT; push_cast at this; exact this
  have hl : (314159 / 100000 : ℝ) < Real.pi := by
    have : (314159 / 100000 : ℝ) < piLo := by norm_num [piLo]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hT' hpos.le]

end AEGIS.CvSTraceIntegralL43V1

#print axioms AEGIS.CvSTraceIntegralL43V1.volume_cellSet_le
#print axioms AEGIS.CvSTraceIntegralL43V1.sFun_measurable
#print axioms AEGIS.CvSTraceIntegralL43V1.integrable_mul
#print axioms AEGIS.CvSTraceIntegralL43V1.integral_mul_le
#print axioms AEGIS.CvSTraceIntegralL43V1.chain_cover
#print axioms AEGIS.CvSTraceIntegralL43V1.slack_ge
#print axioms AEGIS.CvSTraceIntegralL43V1.premises_of_cells
#print axioms AEGIS.CvSTraceIntegralL43V1.gap_of_T
