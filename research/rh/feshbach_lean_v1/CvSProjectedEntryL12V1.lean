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
import CvSProjectedSymmetryV1
import CvSDiagL12V1
import CvSDividedDifferenceCollectionV1

/-!
# Source enclosures of the projected CvS entries at `L = 6/5` (`hIv`)

`projectedEntry_mem_certI_of_check`: given `bigCheck = true`, for every prime cutoff `M ≥ 3` and all `i j : Fin 139`,
`(Im certI i j).Mem certQ (projectedEntry M i j)`. With `CvSProjectedSymmetryV1.projected_lower_of_Iv`
this discharges the interval hypothesis of the packed `139 × 139` certificate.

Method (midpoint + radius, exact integers):
* `transformedCoeff_eq`: `X_ki = f_k w_ki / 2^42` with `f_k = -(2πn/L)² - 1/4` and the integer
  second difference `w_ki` of the columns of `certR` (three-point `sinSq` support).
* Collection (`CvSDividedDifferenceCollectionV1`): with `ν_k = n_k`, `H_ki = Σ_l X_li/(ν_k - ν_l)`,
  `projectedEntry = Σ_k X_ki X_kj D_k + Σ_k C τ_k (X_ki H_kj + X_kj H_ki)`, `C = L/(2π²)`.
* Midpoints: `π² ≈ SI/2^70`, `X̂ = xI/σ`, `Ĥ = hI/(σΛ)` (`Λ = lcm(1..140)`), `τ̂, D̂` the centres of the
  kernel-checked boxes (`CvSTauPrimeL12V1.tau_mem`, `CvSDiagL12V1.diag_mem`). `Ê_ij = neI i j / DE`
  is exact; `hI` and `neI` are packed GMP dot products (`CvSPackedGramV1.gramEntry_eq`).
* `entry_error`: `|E - Ê| ≤ aD_i aD_j + C⁺(aT_i bT_j + aT_j bT_i) + Rπ` (weighted Cauchy–Schwarz for
  the `τ, D` radii; crude global bound `Rπ` for the `π²` error).
* `bigCheck`: one closed Boolean computation checks every column bound and, for `i ≤ j`, that
  `[Ê - rad, Ê + rad]` lies in both `Im certI i j` and `Im certI j i` (data from
  `tools/gen_projected_entry.py`, untrusted; its exact-integer mirror evaluates it to `true` on all
  9730 upper-triangle entries).

STATUS: the analytic bridge is fully proved, but the Lean kernel replay of `bigCheck` is NOT included
yet (the direct `decide +kernel` exceeded 13 GB). The consequences are therefore stated under the
single hypothesis `[Fact (bigCheck = true)]`, a closed computation with no analytic content.
No `native_decide`, no new axioms. Not RH.
-/

open Finset

namespace AEGIS.CvSProjectedEntryL12V1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1 AEGIS.CvSProjectedPackedCertificateL12V1
  AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSRowTailV1

/-! ## Real error lemmas -/

/-- Weighted Cauchy–Schwarz with certified square-root bounds. -/
theorem cs_bound {ι : Type*} [Fintype ι] (ρ a b : ι → ℝ) (hρ : ∀ k, 0 ≤ ρ k) {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hA : ∑ k, ρ k * a k ^ 2 ≤ A ^ 2)
    (hB : ∑ k, ρ k * b k ^ 2 ≤ B ^ 2) :
    ∑ k, ρ k * (|a k| * |b k|) ≤ A * B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => √(ρ k) * |a k|)
    (fun k => √(ρ k) * |b k|)
  have e1 : ∀ k, √(ρ k) * |a k| * (√(ρ k) * |b k|) = ρ k * (|a k| * |b k|) := fun k => by
    rw [show √(ρ k) * |a k| * (√(ρ k) * |b k|) = (√(ρ k) * √(ρ k)) * (|a k| * |b k|) by ring,
      Real.mul_self_sqrt (hρ k)]
  have e2 : ∀ (c : ι → ℝ) k, (√(ρ k) * |c k|) ^ 2 = ρ k * c k ^ 2 := fun c k => by
    rw [mul_pow, Real.sq_sqrt (hρ k), sq_abs]
  simp only [e1, e2] at h
  have hS : 0 ≤ ∑ k, ρ k * (|a k| * |b k|) :=
    sum_nonneg fun k _ => mul_nonneg (hρ k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hP : (∑ k, ρ k * a k ^ 2) * (∑ k, ρ k * b k ^ 2) ≤ A ^ 2 * B ^ 2 :=
    mul_le_mul hA hB (sum_nonneg fun k _ => mul_nonneg (hρ k) (sq_nonneg _)) (sq_nonneg _)
  nlinarith [mul_nonneg hA0 hB0]

theorem sum_abs_le_card {ι : Type*} [Fintype ι] (f : ι → ℝ) {c : ℝ} (h : ∀ k, |f k| ≤ c) :
    |∑ k, f k| ≤ Fintype.card ι * c := by
  calc |∑ k, f k| ≤ ∑ k, |f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, c := sum_le_sum fun k _ => h k
    _ = Fintype.card ι * c := by simp [card_univ]
/-- Midpoint–radius error for a collected projected entry. -/
theorem entry_error {ι : Type*} [Fintype ι]
    (X Y Xh Yh H G Hh Gh D Dh rD T Th rT : ι → ℝ) (C Ch : ℝ)
    {dX dH dC XM HM DM TM RT CP aD bD aT bT cH cG : ℝ}
    (hD : ∀ k, |D k - Dh k| ≤ rD k) (hT : ∀ k, |T k - Th k| ≤ rT k)
    (hX : ∀ k, |X k - Xh k| ≤ dX) (hY : ∀ k, |Y k - Yh k| ≤ dX)
    (hH : ∀ k, |H k - Hh k| ≤ dH) (hG : ∀ k, |G k - Gh k| ≤ dH)
    (hXm : ∀ k, |Xh k| ≤ XM) (hYm : ∀ k, |Yh k| ≤ XM)
    (hHm : ∀ k, |Hh k| ≤ HM) (hGm : ∀ k, |Gh k| ≤ HM)
    (hDm : ∀ k, |D k| ≤ DM) (hTm : ∀ k, |Th k| ≤ TM)
    (hrD : ∀ k, 0 ≤ rD k) (hrT : ∀ k, 0 ≤ rT k) (hRT : ∀ k, rT k ≤ RT) (hRT0 : 0 ≤ RT)
    (hC : 0 ≤ C) (hCP : C ≤ CP) (hCh : 0 ≤ Ch) (hChP : Ch ≤ CP) (hdC : |C - Ch| ≤ dC)
    (hdX : 0 ≤ dX) (hdH : 0 ≤ dH) (hXM : 0 ≤ XM) (hHM : 0 ≤ HM) (hTM : 0 ≤ TM)
    (haD : 0 ≤ aD) (hbD : 0 ≤ bD) (haT : 0 ≤ aT) (hbT : 0 ≤ bT) (hcH : 0 ≤ cH) (hcG : 0 ≤ cG)
    (sD1 : ∑ k, rD k * Xh k ^ 2 ≤ aD ^ 2) (sD2 : ∑ k, rD k * Yh k ^ 2 ≤ bD ^ 2)
    (sT1 : ∑ k, rT k * Xh k ^ 2 ≤ aT ^ 2) (sT2 : ∑ k, rT k * Yh k ^ 2 ≤ bT ^ 2)
    (sH1 : ∑ k, rT k * Hh k ^ 2 ≤ cH ^ 2) (sH2 : ∑ k, rT k * Gh k ^ 2 ≤ cG ^ 2) :
    |((∑ k, X k * Y k * D k) + ∑ k, C * T k * (X k * G k + Y k * H k)) -
      ((∑ k, Xh k * Yh k * Dh k) + ∑ k, Ch * Th k * (Xh k * Gh k + Yh k * Hh k))| ≤
      aD * bD + CP * (aT * cG + bT * cH) +
      (Fintype.card ι * (DM * ((XM + dX) * dX + dX * XM)) +
        CP * (Fintype.card ι * (RT * (2 * (dX * (HM + dH) + XM * dH)))) +
        Fintype.card ι * (TM * (dC * (2 * ((XM + dX) * (HM + dH))) +
          CP * (2 * ((XM + dX) * dH + dX * HM))))) := by
  set N := (Fintype.card ι : ℝ)
  have tri : ∀ {u v : ℝ} {d m : ℝ}, |u - v| ≤ d → |v| ≤ m → |u| ≤ m + d := fun h1 h2 => by
    have := abs_sub_abs_le_abs_sub _ _ |>.trans h1; linarith
  have prod : ∀ {u v u' v' : ℝ} {d e m n : ℝ}, |u - u'| ≤ d → |v - v'| ≤ e → |u'| ≤ m →
      |v'| ≤ n → 0 ≤ d → 0 ≤ e → |u * v - u' * v'| ≤ (m + d) * e + d * n := by
    intro u v u' v' d e m n h1 h2 h3 h4 hd he
    have hu := tri h1 h3
    rw [show u * v - u' * v' = u * (v - v') + (u - u') * v' by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hu h2 (abs_nonneg _) (by linarith [abs_nonneg u']))
      (mul_le_mul h1 h4 (abs_nonneg _) hd)
  have split : ((∑ k, X k * Y k * D k) + ∑ k, C * T k * (X k * G k + Y k * H k)) -
      ((∑ k, Xh k * Yh k * Dh k) + ∑ k, Ch * Th k * (Xh k * Gh k + Yh k * Hh k)) =
      (∑ k, Xh k * Yh k * (D k - Dh k)) + (∑ k, (X k * Y k - Xh k * Yh k) * D k) +
      (∑ k, C * (T k - Th k) * (X k * G k + Y k * H k)) +
      ∑ k, Th k * (C * (X k * G k + Y k * H k) - Ch * (Xh k * Gh k + Yh k * Hh k)) := by
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [split]
  have b1 : |∑ k, (Xh k * Yh k * (D k - Dh k))| ≤ aD * bD := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ => ?_).trans
      (cs_bound rD Xh Yh hrD haD hbD sD1 sD2))
    rw [abs_mul, abs_mul, mul_comm (rD k)]
    exact mul_le_mul_of_nonneg_left (hD k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have b2 : |∑ k, (X k * Y k - Xh k * Yh k) * D k| ≤
      N * (DM * ((XM + dX) * dX + dX * XM)) := by
    refine sum_abs_le_card _ fun k => ?_
    rw [abs_mul, mul_comm DM]
    exact mul_le_mul (prod (hX k) (hY k) (hXm k) (hYm k) hdX hdX) (hDm k) (abs_nonneg _)
      (by positivity)
  have b3 : |∑ k, C * (T k - Th k) * (X k * G k + Y k * H k)| ≤
      CP * (aT * cG + bT * cH + N * (RT * (2 * (dX * (HM + dH) + XM * dH)))) := by
    have pt : ∀ k, |C * (T k - Th k) * (X k * G k + Y k * H k)| ≤
        C * (rT k * (|Xh k| * |Gh k|) + rT k * (|Yh k| * |Hh k|) +
          RT * (2 * (dX * (HM + dH) + XM * dH))) := fun k => by
      have q : ∀ {u u' v v' : ℝ}, |u - u'| ≤ dX → |v - v'| ≤ dH → |u'| ≤ XM → |v'| ≤ HM →
          |u * v| ≤ |u'| * |v'| + (dX * (HM + dH) + XM * dH) := by
        intro u u' v v' h1 h2 h3 h4
        have a1 := tri h1 (le_refl _); have a2 := tri h2 (le_refl _)
        rw [abs_mul]
        nlinarith [abs_nonneg u', abs_nonneg v', abs_nonneg u, abs_nonneg v]
      have e1 := q (hX k) (hG k) (hXm k) (hGm k)
      have e2 := q (hY k) (hH k) (hYm k) (hHm k)
      rw [abs_mul, abs_mul, abs_of_nonneg hC, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have hs := (abs_add_le (X k * G k) (Y k * H k)).trans (add_le_add e1 e2)
      have hm : 0 ≤ dX * (HM + dH) + XM * dH := by positivity
      calc |T k - Th k| * |X k * G k + Y k * H k|
          ≤ rT k * (|Xh k| * |Gh k| + (dX * (HM + dH) + XM * dH) +
              (|Yh k| * |Hh k| + (dX * (HM + dH) + XM * dH))) :=
            mul_le_mul (hT k) hs (abs_nonneg _) (hrT k)
        _ ≤ _ := by nlinarith [hRT k, hrT k]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ => pt k).trans ?_)
    rw [← mul_sum]
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    have c1 := cs_bound rT Xh Gh hrT haT hcG sT1 sH2
    have c2 := cs_bound rT Yh Hh hrT hbT hcH sT2 sH1
    calc C * (∑ k, rT k * (|Xh k| * |Gh k|) + ∑ k, rT k * (|Yh k| * |Hh k|) +
          N * (RT * (2 * (dX * (HM + dH) + XM * dH))))
        ≤ CP * (∑ k, rT k * (|Xh k| * |Gh k|) + ∑ k, rT k * (|Yh k| * |Hh k|) +
          N * (RT * (2 * (dX * (HM + dH) + XM * dH)))) := by
          refine mul_le_mul_of_nonneg_right hCP ?_
          have := sum_nonneg fun k (_ : k ∈ univ) =>
            mul_nonneg (hrT k) (mul_nonneg (abs_nonneg (Xh k)) (abs_nonneg (Gh k)))
          have := sum_nonneg fun k (_ : k ∈ univ) =>
            mul_nonneg (hrT k) (mul_nonneg (abs_nonneg (Yh k)) (abs_nonneg (Hh k)))
          have : 0 ≤ N * (RT * (2 * (dX * (HM + dH) + XM * dH))) := by positivity
          linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [c1, c2]) (hC.trans hCP)
  have b4 : |∑ k, Th k * (C * (X k * G k + Y k * H k) - Ch * (Xh k * Gh k + Yh k * Hh k))| ≤
      N * (TM * (dC * (2 * ((XM + dX) * (HM + dH))) + CP * (2 * ((XM + dX) * dH + dX * HM)))) := by
    refine sum_abs_le_card _ fun k => ?_
    have p1 := prod (hX k) (hG k) (hXm k) (hGm k) hdX hdH
    have p2 := prod (hY k) (hH k) (hYm k) (hHm k) hdX hdH
    have m1 : |X k * G k| ≤ (XM + dX) * (HM + dH) := by
      rw [abs_mul]; exact mul_le_mul (tri (hX k) (hXm k)) (tri (hG k) (hGm k)) (abs_nonneg _)
        (by linarith)
    have m2 : |Y k * H k| ≤ (XM + dX) * (HM + dH) := by
      rw [abs_mul]; exact mul_le_mul (tri (hY k) (hYm k)) (tri (hH k) (hHm k)) (abs_nonneg _)
        (by linarith)
    rw [abs_mul]
    refine mul_le_mul (hTm k) ?_ (abs_nonneg _) hTM
    rw [show C * (X k * G k + Y k * H k) - Ch * (Xh k * Gh k + Yh k * Hh k) =
      (C - Ch) * (X k * G k + Y k * H k) +
        Ch * ((X k * G k - Xh k * Gh k) + (Y k * H k - Yh k * Hh k)) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul hdC ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
        ((abs_nonneg _).trans hdC)
    · rw [abs_mul, abs_of_nonneg hCh]
      exact mul_le_mul hChP ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
        (hCh.trans hChP)
  have := abs_add_le (∑ k, (Xh k * Yh k * (D k - Dh k)) +
    ∑ k, (X k * Y k - Xh k * Yh k) * D k +
    ∑ k, C * (T k - Th k) * (X k * G k + Y k * H k))
    (∑ k, Th k * (C * (X k * G k + Y k * H k) - Ch * (Xh k * Gh k + Yh k * Hh k)))
  have := abs_add_le (∑ k, (Xh k * Yh k * (D k - Dh k)) +
    ∑ k, (X k * Y k - Xh k * Yh k) * D k)
    (∑ k, C * (T k - Th k) * (X k * G k + Y k * H k))
  have := abs_add_le (∑ k, (Xh k * Yh k * (D k - Dh k)))
    (∑ k, (X k * Y k - Xh k * Yh k) * D k)
  linarith [b1, b2, b3, b4]


/-! ## Packed dot products over `List.range` -/

theorem getD_map_range {α : Type*} {n k : ℕ} (f : ℕ → α) (d : α) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem all_natAbs {l : List ℤ} {B : ℕ} (h : l.all (fun x => x.natAbs ≤ B) = true) :
    ∀ x ∈ l, -(B : ℤ) ≤ x ∧ x ≤ B := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simp only [decide_eq_true_eq] at this
  omega

theorem gram_range {b B n : ℕ} (f g : ℕ → ℤ) (hn : 0 < n)
    (hf : ((List.range n).map f).all (fun x => x.natAbs ≤ B) = true)
    (hg : ((List.range n).map g).all (fun x => x.natAbs ≤ B) = true)
    (hb : n * n * (2 * B * (2 * B)) < b) :
    gramEntry b B n (pack b (offRow B ((List.range n).map f))) ((List.range n).map f).sum
      (pack b (offRow B ((List.range n).map g)).reverse) ((List.range n).map g).sum =
      ∑ k ∈ range n, f k * g k := by
  have h := gramEntry_eq (b := b) (B := B) (r := (List.range n).map f)
    (r' := (List.range n).map g) (by simpa using hn) (by simp) (all_natAbs hf) (all_natAbs hg)
    (by simpa using hb)
  simp only [List.length_map, List.length_range] at h
  rw [h]
  exact sum_congr rfl fun k hk => by
    rw [getD_map_range f 0 (mem_range.mp hk), getD_map_range g 0 (mem_range.mp hk)]

/-! ## Exact integer data (`tools/gen_projected_entry.py`, untrusted) -/

/-- `round(π² · 2^70)`. -/
def SI : ℤ := 11651972255721781414236

/-- `lcm(1, …, 140)`. -/
def LAM : ℤ := 33312720618553145840562713089120360606823375590405920630576000

/-- `σ = 9 · 2^112`. -/
def sigX : ℤ := 46730671726813448656774466962980864

/-- `9 · 2^68`. -/
def C68 : ℤ := 2656331146614175432704

/-- Entry `(m, i)` of `certR`. -/
def rI (m i : ℕ) : ℤ := (certR.getD m []).getD i 0

/-- `certR` entry at a signed row, zero outside `0 ≤ m < 139`. -/
def rZ (m : ℤ) (i : ℕ) : ℤ := if 0 ≤ m ∧ m < 139 then rI m.toNat i else 0

/-- The second difference `2 r(n) - r(n-1) - r(n+1)` of column `i` (row of centre `c` is `c + 69`). -/
def wZ (n : ℤ) (i : ℕ) : ℤ := 2 * rZ (n + 69) i - rZ (n + 68) i - rZ (n + 70) i

/-- `X̂_ki = xI k i / σ = (-(25/9) n² SI/2^70 - 1/4) w_ki / 2^42`, `n = k - 70`. -/
def xI (k i : ℕ) : ℤ := -(25 * (((k : ℤ) - 70) * ((k : ℤ) - 70)) * SI + C68) * wZ ((k : ℤ) - 70) i

/-- `Λ / (k - l)` off the diagonal. -/
def kp (k l : ℕ) : ℤ := if k = l then 0 else LAM / ((k : ℤ) - l)

def B1 : ℕ := 2 ^ 205
def b1 : ℕ := 2 ^ 429

def xL (i : ℕ) : List ℤ := (List.range 141).map fun k => xI k i

def kL (k : ℕ) : List ℤ := (List.range 141).map (kp k)

def kPk : List (ℕ × ℤ) :=
  (List.range 141).map fun k => (pack b1 (offRow B1 (kL k)), (kL k).sum)

/-- `hI k i = Σ_l kp k l · xI l i`, one packed product per entry. -/
def hL (i : ℕ) : List ℤ :=
  kPk.map fun p => gramEntry b1 B1 141 p.1 p.2 (pack b1 (offRow B1 (xL i)).reverse) (xL i).sum

def hI (k i : ℕ) : ℤ := (hL i).getD k 0

/-- `(diagLo + diagHi) · 2^48` for `n = 0, …, 70`. -/
def dmI : List ℤ := [-1621470873250693, 72867527927359, 156152043574333, 652085244362639, 955939350283701, 815203910320460, 1433191442183718, 983047314087104, 1516997085583372, 1267819991984966, 1345915931986924, 1601252372694548, 1229281382251250, 1829872713039023, 1390844882501449, 1857542630524617, 1778993871243868, 1739087130709896, 2124587195143944, 1646874549319031, 2191992323467332, 1731185647960258, 1992732179894170, 1988723521551900, 1770210723388332, 2256625436773974, 1776170830896252, 2347965742950018, 2046587550407171, 2218625850281064, 2377894049836662, 2017066184638494, 2517144690345978, 1962637194009322, 2388015047515706, 2150893444967840, 2150666354930340, 2459390300646426, 2050616061707347, 2647569981251296, 2200374267478141, 2571132194977921, 2488674740975910, 2319670576004291, 2688976955551642, 2145708142147544, 2661069301484842, 2239700197797992, 2466159447426708, 2552043705869160, 2302761404159980, 2829526247575098, 2330418456790382, 2841605216477024, 2538153101076764, 2593890436461888, 2764474693480308, 2330136673744555, 2840819753319408, 2313972914439944, 2730867527659014, 2586423662959852, 2552387900238816, 2923456044422976, 2472794949947130, 3037474011874590, 2571223647801376, 2840990520229346, 2778962141043802, 2529582500942673, 2940408463764094]

/-- `(diagHi - diagLo) · 2^48`. -/
def drI : List ℤ := [4316517, 4316517, 4316517, 4316517, 4316517, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316515, 4316515, 4316515, 4316516, 4316516, 4316516, 4316515, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316515, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316515, 4316516, 4316515, 4316515, 4316516, 4316515, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316515, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316516, 4316515, 4316516]

/-- `(tauFLo + tauFHi) · 2^48` for `k = 1, …, 70`. -/
def tmI : List ℤ := [603636491069812, 2136734926680448, -1267632783039759, 2418955922912229, 559117974556887, 3206443977406714, 4429545399033904, 3558539748044442, 6634303145118690, 2900415229497463, 5096899697392160, 1839167298810975, 1360645655917176, 1612704696676215, -956645066911321, 2694830736882934, 319599907451442, 4100833403095473, 3870931166599697, 4289957359011069, 6248482397641160, 2834057242106865, 5241734740881528, 1063705974775554, 1946636520692750, 847503213291094, -413052635408491, 2630151349017525, 345635623616577, 4781352681213778, 3335040781141517, 5094548708542745, 5604000231312563, 3050659934260420, 5064149584525739, 524649523355784, 2422507454725874, 57343342098702, 322124062229112, 2293818001439693, 689984264805389, 5176570479988170, 2960568553508950, 5848459121004708, 4821397754086434, 3495826972373394, 4570601526347138, 292573576830649, 2681092267128697, -619244856762953, 1126372891410881, 1774182836616752, 1325515224176010, 5249825272562743, 2842064056421963, 6424385487604717, 4035716612450559, 4064988668609503, 3819268520981084, 378508573091417, 2653433885992864, -1064595247175955, 1864862526511719, 1192899804258340, 2170705696935575, 5020679574717242, 3023693750419363, 6723328138773624, 3378619496708378, 4628001002670026]

/-- `(tauFHi - tauFLo) · 2^48`. -/
def trI : List ℤ := [55206628, 55592206, 55291049, 55301769, 55680993, 55810550, 55514438, 55618060, 55683132, 55811685, 55571014, 55527783, 55704098, 55657113, 55874915, 55921502, 55823404, 55603269, 55692233, 55677013, 55972038, 55779191, 55906056, 55960004, 55948574, 55878568, 55756123, 55951085, 55733783, 55834112, 55891467, 55909263, 55890659, 55838576, 55755715, 55979952, 55838702, 56003164, 55811844, 55923881, 56011189, 55755822, 55800018, 55823594, 55827740, 55813578, 55782172, 56039781, 55974293, 55894377, 55800891, 55991548, 55870588, 56031829, 55306823, 53209479, 51486701, 49600963, 48049124, 46347455, 44944670, 43403873, 42131647, 40732066, 39574685, 38299576, 37243625, 36078656, 35112620, 34045462]

def d2 (k : ℕ) : ℤ := dmI.getD (Int.natAbs ((k : ℤ) - 70)) 0
def dr (k : ℕ) : ℤ := drI.getD (Int.natAbs ((k : ℤ) - 70)) 0
def tK (k : ℕ) : ℤ :=
  if k < 70 then -tmI.getD (69 - k) 0 else if k = 70 then 0 else tmI.getD (k - 71) 0
def tr (k : ℕ) : ℤ := if k = 70 then 0 else trI.getD (Int.natAbs ((k : ℤ) - 70) - 1) 0

def C1 : ℤ := 5 * SI * LAM
def C2 : ℤ := 3541774862152233910272

/-- The row vector of the collected entry: `C1·D̂·x̂`, `C2·τ̂·x̂`, `C2·ĥ`. -/
def vI (i k : ℕ) : ℤ :=
  if k < 141 then C1 * (d2 k * xI k i)
  else if k < 282 then C2 * (tK (k - 141) * xI (k - 141) i) else C2 * hI (k - 282) i

/-- The column vector: `x̂`, `ĥ`, `τ̂·x̂`. -/
def wI (j k : ℕ) : ℤ :=
  if k < 141 then xI k j else if k < 282 then hI (k - 141) j else tK (k - 282) * xI (k - 282) j

def vL (i : ℕ) : List ℤ := (List.range 423).map (vI i)
def wL (j : ℕ) : List ℤ := (List.range 423).map (wI j)

def B2 : ℕ := 2 ^ 448
def b2 : ℕ := 2 ^ 925

def colPk (i : ℕ) : ℕ × ℤ × ℕ × ℤ :=
  (pack b2 (offRow B2 (vL i)), (vL i).sum, pack b2 (offRow B2 (wL i)).reverse, (wL i).sum)

def cols : List (ℕ × ℤ × ℕ × ℤ) := (List.range 139).map colPk

/-- `neI i j = Σ_k vI i k · wI j k = DE · Ê_ij`. -/
def neI (i j : ℕ) : ℤ :=
  gramEntry b2 B2 423 (cols.getD i default).1 (cols.getD i default).2.1
    (cols.getD j default).2.2.1 (cols.getD j default).2.2.2

/-- Column radii at scale `2^64`: `aD² ≥ Σ ρD X̂²`, `aT² ≥ Σ ρτ X̂²`, `bT² ≥ Σ ρτ Ĥ²`. -/
def AD : List ℕ := [1615293544995987, 1615293731134505, 1615293732774834, 1615293756306348, 1615293740093585, 1615293735544687, 1615293715663672, 1615293746501866, 1615293700839674, 1615293722439313, 1615293730152622, 1615293577447994, 1615293695201933, 1615293728523269, 1615293703022241, 1615293703584838, 1615293723199836, 1615293717537101, 1615293726198662, 1615293716166618, 1615293724671413, 1615293729755671, 1615293713814553, 1615293733806656, 1615293724233475, 1615293571411949, 1615293720916942, 1615293577020929, 1615293568376770, 1615293714756211, 1615293567575805, 1615293703889377, 1615293709401947, 1615293714209551, 1615293717823702, 1615293718926728, 1615293722809986, 1615293718143541, 1615293721601773, 1615293725947016, 1615293578318963, 1615293717776626, 1615293721433229, 1615293717427214, 1615293724337496, 1615293721787050, 1615293722126883, 1615293724709567, 1615293724340378, 1615293583917417, 1615293712552551, 1615293717217549, 1615293716925712, 1615293586114086, 1615293574761431, 1615293564645053, 1615293684605700, 1615293697759513, 1615293706691643, 1615293714472704, 1615293719200603, 1615293722382177, 1615293723500229, 1615293723436192, 1615293788508911, 1615293852940450, 1615293865700518, 1615293843797655, 1615293827087204, 1615293903111656, 1615293911760075, 1615293912672196, 1615293912929539, 1615293728334419, 1615293727780486, 1615293727369176, 1615293726828056, 1615293726431976, 1615293726592434, 1615293727044993, 1615293725901115, 1615293540034510, 1615293539659457, 1615293538594184, 1615293725789951, 1615293726411914, 1615293724786343, 1615293539960212, 1615293725964988, 1615293727923837, 1615293724107897, 1615293726307115, 1615293723376060, 1615293724430612, 1615293725929603, 1615293726968839, 1615293537763690, 1615293726726969, 1615293726751765, 1615293726372614, 1615293730244276, 1615293723086556, 1615293731694456, 1615293726351276, 1615293727047226, 1615293728416353, 1615293543283666, 1615293731790441, 1615293536791333, 1615293544017766, 1615293729033469, 1615293542560311, 1615293732953094, 1615293719433426, 1615293730708928, 1615293727178572, 1615293720153194, 1615293732076116, 1615293714449092, 1615293736421406, 1615293717321622, 1615293719674914, 1615293733770352, 1615293737600051, 1615293738935941, 1615293533608376, 1615293719209403, 1615293730144582, 1615293728108818, 1615293715922852, 1615293724890145, 1615293741032771, 1615293730519231, 1615293725504919, 1615293738998389, 1615293713123283, 1615293712393950, 1615293522058370, 1615293723754689]
def AT : List ℕ := [4604585455364785, 4670928188323460, 4741467536861146, 4814490493167714, 4887421597622422, 4966316207431971, 5042931903678322, 5127727769848819, 5208805183226402, 5299835417946241, 5386043076147148, 5483810335788379, 5575818648845814, 5680959490180976, 5733804931532628, 5746735256574667, 5763551532441108, 5764598850871999, 5773536344247531, 5780672124788371, 5786357639748740, 5778348080867280, 5780714015423622, 5782239074660505, 5782883895801766, 5782598624989207, 5781325313651479, 5792298358035412, 5789686616840026, 5785711365398245, 5794029465086374, 5787998022936514, 5794239474161375, 5785596083219162, 5789194339675195, 5791743008984770, 5793017400330882, 5792803146463774, 5790890507731321, 5787069363799698, 5796133261958585, 5788782462422775, 5793945899389907, 5797273691969862, 5798354591291678, 5796771253129358, 5792091422473354, 5799814495048508, 5788799912058241, 5789124578515117, 5785572368972791, 5793712084308701, 5797990871839620, 5797126254829969, 5789726618099849, 5791003217291159, 5784813887195918, 5785469311166199, 5793108482041072, 5790514653560383, 5788784237776692, 5785619605959956, 5792075835060919, 5792306872888217, 5785316442322678, 5778324209064906, 5779184910651269, 5789609835262772, 5783355538075950, 5778350452165283, 5795365782051571, 5781137687281914, 5781680554451880, 5801213253816242, 5807981726459634, 5792719762395536, 5798113741546343, 5801508739533838, 5808195506010984, 5795706252596762, 5793462121470940, 5802639277659122, 5800200803712956, 5811526620780566, 5813950929591281, 5808859223922444, 5797408684235252, 5802042186549046, 5801251602810262, 5816591881237953, 5806571514538397, 5813168508045432, 5815972585809581, 5815380318158536, 5811743827105898, 5805376477924847, 5815514102447902, 5804215061941364, 5809435662769341, 5812418367999172, 5813343970374431, 5812377491869722, 5809669909322926, 5805359191426046, 5817018944527545, 5809677583597095, 5818225429558240, 5808281118889749, 5814107090422658, 5818643283368388, 5805366531687897, 5807666748996891, 5808893519467589, 5809109330785819, 5808372798232185, 5806738771887508, 5820129771349870, 5816728761357386, 5812575549415123, 5807713408878640, 5817625580573573, 5811339044429067, 5819717969368207, 5781948185373550, 5671268265538349, 5578711566834774, 5475606052065142, 5389276928898519, 5292994014440250, 5212284449651469, 5122168802594303, 5046547538707984, 4962024950553803, 4891025298276866, 4811590854879520, 4744801884480918, 4670009579631143, 4607067610868659, 4536522136993485]
def BT : List ℕ := [4035904386880603, 5973175390623930, 6850367798979079, 7388085582691729, 7776748963941185, 8079710224023521, 8343342799345454, 8571899873016636, 8791812557056141, 8992525047826685, 9196834296473119, 9387818025732132, 9587404226059599, 9765435291111282, 9935952054062866, 10030350909983827, 10067514211677713, 10107277502161444, 10131882523752938, 10165433088462787, 10195251607575878, 10223045325993811, 10234588678602968, 10254956984467333, 10274200223104814, 10291054418964168, 10307709292477999, 10320013377977960, 10343158216203863, 10353853051176461, 10358104400770504, 10375687121297966, 10376320286169384, 10389132205407291, 10387286904516491, 10396058227748565, 10404390712845955, 10410332671612774, 10413489697285325, 10416399161461774, 10414568973278993, 10427791653950520, 10425118832033220, 10433447713779877, 10440254582243251, 10443321085583710, 10444518269882947, 10439565641539344, 10448682667500055, 10438447869349160, 10441548916939335, 10443092924064412, 10457680698814817, 10467006686637491, 10469550684255611, 10464742083071211, 10472416866779988, 10476399213304472, 10493448261656687, 10520976977803625, 10538706164305998, 10568078198325086, 10616068901770918, 10696189678209761, 10797440950201725, 10978515545730866, 11317573390949677, 11923712803449414, 13061996696041514, 12527249614236054, 9607911612608342, 10058279981248382, 10238221225473472, 10321208055670995, 10368678396264533, 10404535811066528, 10416453131991670, 10431637597076736, 10435211791350650, 10445451762037093, 10449135326328353, 10449942091889986, 10462827292230479, 10464491072087112, 10468391456354312, 10467114559145967, 10469305860755715, 10464620518075513, 10473519209006621, 10468699425860807, 10480978057859273, 10478540726861430, 10480522222939436, 10480087427147225, 10477553695482935, 10479808019427594, 10470015583698474, 10477289582152661, 10472868542451485, 10473960725772970, 10473987838270697, 10472323091994306, 10469805462474187, 10472694720021642, 10465120187402982, 10472875804364898, 10463465682884290, 10468901822265413, 10463066255701654, 10455984181497050, 10457731550956931, 10448866970146642, 10445438776358251, 10441874825664698, 10438072101746965, 10439138864897963, 10429449611217640, 10426759805176000, 10415950038682009, 10407222382294840, 10385489897385368, 10369560665988068, 10311576905219890, 10222269311332127, 10118018246735008, 9962281568455915, 9811957072514490, 9647727426597562, 9495905633815279, 9333377301456356, 9182708668121086, 9020918886141882, 8867707071372737, 8699191903341907, 8529581489373326, 8326329187435235, 8075048562258407, 7635076156161260, 6059462482772295]

def XMI : ℕ := 46729191919268866134397042734068736
def HMI : ℕ := 2202901447828710064039139892846420487723654644766933106865303785208136081716241816632480496143360
def DMI : ℤ := 3037474016191106
def TMI : ℕ := 6723328138773624
def RTI : ℤ := 56039781
/-- `C⁺ = CPI / 2^64 ≥ 3 / (5 π²)`. -/
def CPI : ℤ := 1121427566337318869
/-- `Rπ ≤ RPI / 2^192`. -/
def RPI : ℤ := 2343884123908082020122574108333844570736106

def T64 : ℤ := 18446744073709551616
def T128 : ℤ := 340282366920938463463374607431768211456
def SR : ℤ := 6277101735386680763835789423207666416102355444464034512896
def Q49 : ℤ := 1229345158361594177691221987911758058109648077837682040792162540537900367981421002752
def DE : ℤ := Q49 * LAM * 5 * SI

def radI (i j : ℕ) : ℤ :=
  (AD.getD i 0 : ℤ) * AD.getD j 0 * T64 +
    CPI * ((AT.getD i 0 : ℤ) * BT.getD j 0 + (AT.getD j 0 : ℤ) * BT.getD i 0) + RPI

def ivOk (I : Iv) (ne r : ℤ) : Bool :=
  decide (I.lo * SR * DE + r * T64 * DE ≤ ne * T64 * SR) &&
    decide (ne * T64 * SR + r * T64 * DE ≤ I.hi * SR * DE)

def entryOk (i j : ℕ) : Bool :=
  ivOk (Im certI i j) (neI i j) (radI i j) && ivOk (Im certI j i) (neI i j) (radI i j)

def colOk (i : ℕ) : Bool :=
  (xL i).all (fun x => x.natAbs ≤ XMI) && (hL i).all (fun x => x.natAbs ≤ HMI) &&
  (vL i).all (fun x => x.natAbs ≤ B2) && (wL i).all (fun x => x.natAbs ≤ B2) &&
  decide (T128 * ((List.range 141).map fun k => dr k * (xI k i * xI k i)).sum ≤
    (AD.getD i 0 : ℤ) * AD.getD i 0 * Q49) &&
  decide (T128 * ((List.range 141).map fun k => tr k * (xI k i * xI k i)).sum ≤
    (AT.getD i 0 : ℤ) * AT.getD i 0 * Q49) &&
  decide (T128 * ((List.range 141).map fun k => tr k * (hI k i * hI k i)).sum ≤
    (BT.getD i 0 : ℤ) * BT.getD i 0 * (Q49 * LAM * LAM))

def bigCheck : Bool :=
  (List.range 140).all (fun m => LAM % ((m : ℤ) + 1) == 0) &&
  (List.range 141).all (fun k => (kL k).all fun x => x.natAbs ≤ B1) &&
  (List.range 139).all colOk &&
  (List.range 139).all fun i => (List.range' i (139 - i)).all (entryOk i)

/-! ## Small table checks -/

open AEGIS.CvSDiagL12V1 AEGIS.CvSTauPrimeL12V1 in
/-- The integer centres and radii are exactly those of the source boxes. -/
def tabOk : Bool :=
  (List.range 71).all (fun m =>
    decide ((dmI.getD m 0 : ℚ) = (diagLo.getD m 0 + diagHi.getD m 0) * 2 ^ 48) &&
    decide ((drI.getD m 0 : ℚ) = (diagHi.getD m 0 - diagLo.getD m 0) * 2 ^ 48) &&
    decide (((dmI.getD m 0).natAbs : ℤ) + drI.getD m 0 ≤ DMI) && decide (0 ≤ drI.getD m 0)) &&
  (List.range 70).all (fun m =>
    decide ((tmI.getD m 0 : ℚ) = (tauFLo.getD m 0 + tauFHi.getD m 0) * 2 ^ 48) &&
    decide ((trI.getD m 0 : ℚ) = (tauFHi.getD m 0 - tauFLo.getD m 0) * 2 ^ 48) &&
    decide ((tmI.getD m 0).natAbs ≤ TMI) && decide (0 ≤ trI.getD m 0) &&
    decide (trI.getD m 0 ≤ RTI))

theorem tabOk_true : tabOk = true := by
  decide +kernel

/-! ## The source matrix in collected form -/

theorem sum_range_ite_int (f : ℕ → ℝ) (m : ℤ) :
    ∑ j ∈ range 139, (if (j : ℤ) = m then f j else 0) =
      if 0 ≤ m ∧ m < 139 then f m.toNat else 0 := by
  split_ifs with hm
  · rw [Finset.sum_eq_single m.toNat]
    · rw [if_pos (by omega)]
    · intro j _ hj; rw [if_neg (by omega)]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · exact sum_eq_zero fun j hj => if_neg (by have := mem_range.mp hj; omega)

/-- **Three-point support**: `X_ki = f_k w_ki / 2^42`. -/
theorem transformedCoeff_eq (k : Fin 141) (i : Fin 139) :
    transformedCoeff k i =
      (-(2 * Real.pi * (signedFreq k : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4) *
        (wZ (signedFreq k) i : ℝ) / 2 ^ 42 := by
  set fac := (-(2 * Real.pi * (signedFreq k : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4) with hfac
  set c := signedFreq k with hc
  have hterm : ∀ j : Fin 139, atomWeight j k * rCoeff j i =
      fac / 2 ^ 40 * ((1 / 2) * (if ((j : ℕ) : ℤ) = c + 69 then (rI j i : ℝ) else 0) +
        (-1 / 4) * (if ((j : ℕ) : ℤ) = c + 70 then (rI j i : ℝ) else 0) +
        (-1 / 4) * (if ((j : ℕ) : ℤ) = c + 68 then (rI j i : ℝ) else 0)) := by
    intro j
    simp only [atomWeight, rCoeff, atomCenter, rI, ← hc, ← hfac]
    by_cases h1 : c = ((j : ℕ) : ℤ) - 69
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg h1]
      by_cases h2 : c = ((j : ℕ) : ℤ) - 69 - 1 ∨ c = ((j : ℕ) : ℤ) - 69 + 1
      · rw [if_pos h2, if_neg (by omega)]
        rcases h2 with h2 | h2
        · rw [if_pos (by omega), if_neg (by omega)]; ring
        · rw [if_neg (by omega), if_pos (by omega)]; ring
      · rw [if_neg h2, if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  unfold transformedCoeff
  simp_rw [hterm]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (1 / 2) * (if (j : ℤ) = c + 69 then (rI j i : ℝ) else 0) +
      (-1 / 4) * (if (j : ℤ) = c + 70 then (rI j i : ℝ) else 0) +
      (-1 / 4) * (if (j : ℤ) = c + 68 then (rI j i : ℝ) else 0)) 139,
    sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    sum_range_ite_int (fun j => (rI j i : ℝ)), sum_range_ite_int (fun j => (rI j i : ℝ)),
    sum_range_ite_int (fun j => (rI j i : ℝ))]
  simp only [wZ, rZ]
  push_cast
  split_ifs <;> ring

/-- The off-diagonal entries are divided differences; the diagonal is kept. -/
theorem signedEntry_eq (M : ℕ) (k l : Fin 141) :
    signedEntry M k l =
      if k = l then cvsEntry M (6 / 5) (signedFreq k) (signedFreq k)
      else 6 / 5 / (2 * Real.pi ^ 2) *
        ((tau M (6 / 5) (signedFreq k) - tau M (6 / 5) (signedFreq l)) /
          ((signedFreq k : ℝ) - (signedFreq l : ℝ))) := by
  split_ifs with h
  · subst h; rfl
  · have hne : signedFreq k ≠ signedFreq l := fun e => h (Fin.ext (by
      simp only [signedFreq] at e; omega))
    exact cvsEntry_off M (by norm_num) hne

theorem projectedEntry_collect (M : ℕ) (i j : Fin 139) :
    projectedEntry M i j =
      (∑ k, transformedCoeff k i * transformedCoeff k j *
        cvsEntry M (6 / 5) (signedFreq k) (signedFreq k)) +
      ∑ k, 6 / 5 / (2 * Real.pi ^ 2) * tau M (6 / 5) (signedFreq k) *
        (transformedCoeff k i *
            (∑ l, transformedCoeff l j / ((signedFreq k : ℝ) - (signedFreq l : ℝ))) +
          transformedCoeff k j *
            (∑ l, transformedCoeff l i / ((signedFreq k : ℝ) - (signedFreq l : ℝ)))) := by
  rw [projectedEntry]
  simp_rw [signedEntry_eq]
  exact AEGIS.CvSDividedDifferenceCollectionV1.diagonal_divided_difference_collection
    (fun k => transformedCoeff k i) (fun k => transformedCoeff k j)
    (fun k => tau M (6 / 5) (signedFreq k)) (fun k => (signedFreq k : ℝ))
    (fun k => cvsEntry M (6 / 5) (signedFreq k) (signedFreq k)) (6 / 5 / (2 * Real.pi ^ 2))
/-! ## Source boxes, `π²`, and the midpoint errors -/

open AEGIS.CvSDiagL12V1 AEGIS.CvSTauPrimeL12V1 in
theorem tab_diag {m : ℕ} (hm : m < 71) :
    ((dmI.getD m 0 : ℤ) : ℝ) = (((diagLo.getD m 0 : ℚ) : ℝ) + ((diagHi.getD m 0 : ℚ) : ℝ)) * 2 ^ 48 ∧
    ((drI.getD m 0 : ℤ) : ℝ) = (((diagHi.getD m 0 : ℚ) : ℝ) - ((diagLo.getD m 0 : ℚ) : ℝ)) * 2 ^ 48 ∧
    ((dmI.getD m 0).natAbs : ℤ) + drI.getD m 0 ≤ DMI ∧ 0 ≤ drI.getD m 0 := by
  have h := tabOk_true
  simp only [tabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.1 m hm
  refine ⟨?_, ?_, h3, h4⟩
  · have := congrArg (fun q : ℚ => (q : ℝ)) h1; push_cast at this; exact this
  · have := congrArg (fun q : ℚ => (q : ℝ)) h2; push_cast at this; exact this

open AEGIS.CvSDiagL12V1 AEGIS.CvSTauPrimeL12V1 in
theorem tab_tau {m : ℕ} (hm : m < 70) :
    ((tmI.getD m 0 : ℤ) : ℝ) = (((tauFLo.getD m 0 : ℚ) : ℝ) + ((tauFHi.getD m 0 : ℚ) : ℝ)) * 2 ^ 48 ∧
    ((trI.getD m 0 : ℤ) : ℝ) = (((tauFHi.getD m 0 : ℚ) : ℝ) - ((tauFLo.getD m 0 : ℚ) : ℝ)) * 2 ^ 48 ∧
    (tmI.getD m 0).natAbs ≤ TMI ∧ 0 ≤ trI.getD m 0 ∧ trI.getD m 0 ≤ RTI := by
  have h := tabOk_true
  simp only [tabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h.2 m hm
  refine ⟨?_, ?_, h3, h4, h5⟩
  · have := congrArg (fun q : ℚ => (q : ℝ)) h1; push_cast at this; exact this
  · have := congrArg (fun q : ℚ => (q : ℝ)) h2; push_cast at this; exact this

theorem box_of {x lo hi c r : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) (hc : c = (lo + hi) * 2 ^ 48)
    (hr : r = (hi - lo) * 2 ^ 48) : |x - c / 2 ^ 49| ≤ r / 2 ^ 49 := by
  subst hc hr
  rw [abs_le]; constructor <;> nlinarith

/-- `|D_k - D̂_k| ≤ ρD_k` from `CvSDiagL12V1.diag_mem`. -/
theorem diag_box {M : ℕ} (hM : 3 ≤ M) (k : Fin 141) :
    |cvsEntry M (6 / 5) (signedFreq k) (signedFreq k) - (d2 k : ℝ) / 2 ^ 49| ≤
      (dr k : ℝ) / 2 ^ 49 := by
  have hk := k.isLt
  set m := Int.natAbs (signedFreq k) with hm
  have hm70 : m ≤ 70 := by simp only [hm, signedFreq]; omega
  have hcv : cvsEntry M (6 / 5) (signedFreq k) (signedFreq k) =
      cvsEntry M (6 / 5) (m : ℤ) (m : ℤ) := by
    rcases Int.natAbs_eq (signedFreq k) with h | h
    · rw [← hm] at h; rw [h]
    · rw [← hm] at h; rw [h, AEGIS.CvSDiagL12V1.cvsEntry_diag_neg hM]
  obtain ⟨lo, hi⟩ := AEGIS.CvSDiagL12V1.diag_mem hM hm70
  obtain ⟨e1, e2, -, -⟩ := tab_diag (m := m) (by omega)
  have hd : d2 k = dmI.getD m 0 := rfl
  have hr : dr k = drI.getD m 0 := rfl
  rw [hcv, hd, hr]
  exact box_of lo hi e1 e2

/-- `|τ_k - τ̂_k| ≤ ρτ_k` from `CvSTauPrimeL12V1.tau_mem` (odd extension, `τ_0 = 0`). -/
theorem tau_box {M : ℕ} (hM : 3 ≤ M) (k : Fin 141) :
    |tau M (6 / 5) (signedFreq k) - (tK k : ℝ) / 2 ^ 49| ≤ (tr k : ℝ) / 2 ^ 49 := by
  have hk := k.isLt
  rcases lt_trichotomy k.val 70 with h | h | h
  · have e : signedFreq k = -(((70 - k.val : ℕ) : ℤ)) := by simp only [signedFreq]; omega
    obtain ⟨lo, hi⟩ := AEGIS.CvSTauPrimeL12V1.tau_mem hM (k := 70 - k.val) (by omega) (by omega)
    obtain ⟨e1, e2, -, -, -⟩ := tab_tau (m := 69 - k.val) (by omega)
    rw [show 70 - k.val - 1 = 69 - k.val by omega] at lo hi
    have ht : tK k = -tmI.getD (69 - k.val) 0 := by simp [tK, h]
    have hr : tr k = trI.getD (69 - k.val) 0 := by
      simp only [tr, if_neg (show k.val ≠ 70 by omega)]
      congr 1; omega
    rw [e, AEGIS.CvSTauPrimeL12V1.tau_neg, ht, hr]
    exact box_of (lo := -((AEGIS.CvSTauPrimeL12V1.tauFHi.getD (69 - k.val) 0 : ℚ) : ℝ))
      (hi := -((AEGIS.CvSTauPrimeL12V1.tauFLo.getD (69 - k.val) 0 : ℚ) : ℝ)) (by linarith)
      (by linarith) (by push_cast; rw [e1]; ring) (by rw [e2]; ring)
  · have e : signedFreq k = 0 := by simp only [signedFreq]; omega
    have ht : tK k = 0 := by simp [tK, h]
    have hr : tr k = 0 := by simp [tr, h]
    rw [e, AEGIS.CvSTauPrimeL12V1.tau_zero, ht, hr]; simp
  · have e : signedFreq k = (((k.val - 70 : ℕ)) : ℤ) := by simp only [signedFreq]; omega
    obtain ⟨lo, hi⟩ := AEGIS.CvSTauPrimeL12V1.tau_mem hM (k := k.val - 70) (by omega) (by omega)
    obtain ⟨e1, e2, -, -, -⟩ := tab_tau (m := k.val - 71) (by omega)
    rw [show k.val - 70 - 1 = k.val - 71 by omega] at lo hi
    have ht : tK k = tmI.getD (k.val - 71) 0 := by
      simp [tK, show ¬ k.val < 70 by omega, show k.val ≠ 70 by omega]
    have hr : tr k = trI.getD (k.val - 71) 0 := by
      simp only [tr, if_neg (show k.val ≠ 70 by omega)]
      congr 1; omega
    rw [e, ht, hr]
    exact box_of lo hi e1 e2

theorem pi_sq_bounds : |Real.pi ^ 2 - (SI : ℝ) / 2 ^ 70| ≤ 1 / 2 ^ 63 ∧ (9 : ℝ) ≤ SI / 2 ^ 70 ∧
    (9 : ℝ) ≤ Real.pi ^ 2 ∧ 3 / (5 * Real.pi ^ 2) ≤ (CPI : ℝ) / 2 ^ 64 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  have u : Real.pi ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, by norm_num [SI], by nlinarith, ?_⟩
  · norm_num [SI] at l ⊢; linarith
  · norm_num [SI] at u ⊢; linarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num [CPI] at l ⊢; nlinarith

theorem sigX_real : (sigX : ℝ) = 9 * 2 ^ 112 := by norm_num [sigX]

/-- The `π²` error of a transformed coefficient is relative: `|X - X̂| ≤ (2^-63/9) |X̂|`. -/
theorem X_err (k : Fin 141) (i : Fin 139) :
    |transformedCoeff k i - (xI k i : ℝ) / sigX| ≤ 1 / 2 ^ 63 / 9 * |(xI k i : ℝ) / sigX| := by
  obtain ⟨hs, h9, -, -⟩ := pi_sq_bounds
  rw [transformedCoeff_eq]
  set n : ℝ := (signedFreq k : ℝ)
  set w : ℝ := (wZ (signedFreq k) i : ℝ)
  set sh : ℝ := (SI : ℝ) / 2 ^ 70
  have ex : xI k i = -(25 * (signedFreq k * signedFreq k) * SI + C68) * wZ (signedFreq k) i := rfl
  have hx : (xI k i : ℝ) / sigX = (-(25 / 9) * n ^ 2 * sh - 1 / 4) * (w / 2 ^ 42) := by
    rw [ex, sigX_real]; push_cast
    rw [show (C68 : ℝ) = 9 * 2 ^ 68 by norm_num [C68]]
    simp only [sh, n, w]; ring
  have hn : 0 ≤ n ^ 2 := sq_nonneg n
  have key : |-(25 / 9) * n ^ 2 * (Real.pi ^ 2 - sh)| ≤
      1 / 2 ^ 63 / 9 * |-(25 / 9) * n ^ 2 * sh - 1 / 4| := by
    rw [abs_of_neg (show -(25 / 9) * n ^ 2 * sh - 1 / 4 < 0 by nlinarith),
      show |-(25 / 9) * n ^ 2 * (Real.pi ^ 2 - sh)| = 25 / 9 * n ^ 2 * |Real.pi ^ 2 - sh| by
        rw [abs_mul, abs_mul, abs_of_nonneg hn]; norm_num]
    have ha := abs_nonneg (Real.pi ^ 2 - sh)
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hs), mul_nonneg hn (sub_nonneg.mpr h9)]
  rw [hx]
  calc |(-(2 * Real.pi * n / (6 / 5 : ℝ)) ^ 2 - 1 / 4) * w / 2 ^ 42 -
        (-(25 / 9) * n ^ 2 * sh - 1 / 4) * (w / 2 ^ 42)|
      = |-(25 / 9) * n ^ 2 * (Real.pi ^ 2 - sh)| * |w / 2 ^ 42| := by
        rw [← abs_mul]; congr 1; ring
    _ ≤ 1 / 2 ^ 63 / 9 * |-(25 / 9) * n ^ 2 * sh - 1 / 4| * |w / 2 ^ 42| :=
        mul_le_mul_of_nonneg_right key (abs_nonneg _)
    _ = 1 / 2 ^ 63 / 9 * |(-(25 / 9) * n ^ 2 * sh - 1 / 4) * (w / 2 ^ 42)| := by
        rw [abs_mul]; ring

theorem abs_div_int_le (a : ℝ) (m : ℤ) : |a / (m : ℝ)| ≤ |a| := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [abs_div]
    exact div_le_self (abs_nonneg a) (by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      rw [← Int.cast_abs]; exact_mod_cast this)

/-! ## The exact midpoint and the interval check -/

theorem Q49_real : (Q49 : ℝ) = 2 ^ 49 * sigX * sigX := by norm_num [Q49, sigX]

theorem DE_real : (DE : ℝ) = 2 ^ 49 * sigX * sigX * LAM * 5 * SI := by
  rw [DE]; push_cast; rw [Q49_real]

theorem lsum_range (n : ℕ) (g : ℕ → ℤ) :
    ((List.range n).map g).sum = ∑ k ∈ range n, g k := by
  rw [sum_eq_range]
  simp only [List.length_map, List.length_range]
  exact sum_congr rfl fun k hk => getD_map_range g 0 (mem_range.mp hk)

theorem ivOk_mem {I : Iv} {ne r : ℤ} (h : ivOk I ne r = true) {x : ℝ}
    (hx : |x - (ne : ℝ) / DE| ≤ (r : ℝ) / SR) : I.Mem certQ x := by
  simp only [ivOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hDE : (0 : ℝ) < DE := by
    have : (0 : ℤ) < DE := by norm_num [DE, Q49, LAM, SI]
    exact_mod_cast this
  have hSR : (0 : ℝ) < SR := by norm_num [SR]
  have hT : (T64 : ℝ) = 2 ^ 64 := by norm_num [T64]
  have h1' : (I.lo : ℝ) * SR * DE + r * T64 * DE ≤ ne * T64 * SR := by exact_mod_cast h1
  have h2' : (ne : ℝ) * T64 * SR + r * T64 * DE ≤ I.hi * SR * DE := by exact_mod_cast h2
  rw [hT] at h1' h2'
  rw [abs_le] at hx
  have hp : (0 : ℝ) < SR * DE := by positivity
  have e1 : ((ne : ℝ) / DE - r / SR) * 2 ^ 64 * (SR * DE) = ne * 2 ^ 64 * SR - r * 2 ^ 64 * DE := by
    field_simp
  have e2 : ((ne : ℝ) / DE + r / SR) * 2 ^ 64 * (SR * DE) = ne * 2 ^ 64 * SR + r * 2 ^ 64 * DE := by
    field_simp
  simp only [Iv.Mem, certQ]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ hp
    calc (I.lo : ℝ) * (SR * DE) ≤ ((ne : ℝ) / DE - r / SR) * 2 ^ 64 * (SR * DE) := by
          rw [e1]; linarith
      _ ≤ x * 2 ^ 64 * (SR * DE) := by gcongr; linarith
  · rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ hp
    calc x * 2 ^ 64 * (SR * DE) ≤ ((ne : ℝ) / DE + r / SR) * 2 ^ 64 * (SR * DE) := by
          gcongr; linarith
      _ ≤ (I.hi : ℝ) * (SR * DE) := by rw [e2]; linarith

/-- Column radius from the kernel inequality `2^128 S ≤ A² Q`. -/
theorem cs_real {S A Q : ℝ} (hQ : 0 < Q) (h : 2 ^ 128 * S ≤ A * A * Q) : S / Q ≤ (A / 2 ^ 64) ^ 2 := by
  rw [div_le_iff₀ hQ]
  have : (A / 2 ^ 64) ^ 2 * Q = A * A * Q / 2 ^ 128 := by ring
  rw [this, le_div_iff₀ (by positivity)]
  linarith

/-- The global `π²` remainder of `entry_error` with the constants used below. -/
noncomputable def Rpi : ℝ :=
    (Fintype.card (Fin 141) : ℝ) * ((DMI : ℝ) / 2 ^ 49 *
        (((XMI : ℝ) / sigX + 1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) +
          1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX) * ((XMI : ℝ) / sigX))) +
      (CPI : ℝ) / 2 ^ 64 * ((Fintype.card (Fin 141) : ℝ) * ((RTI : ℝ) / 2 ^ 49 *
        (2 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX) *
            ((HMI : ℝ) / (sigX * LAM) + 141 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX))) +
          (XMI : ℝ) / sigX * (141 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX))))))) +
      (Fintype.card (Fin 141) : ℝ) * ((TMI : ℝ) / 2 ^ 49 *
        (3 * (1 / 2 ^ 63) / 405 * (2 * (((XMI : ℝ) / sigX + 1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) *
            ((HMI : ℝ) / (sigX * LAM) + 141 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX))))) +
          (CPI : ℝ) / 2 ^ 64 * (2 * (((XMI : ℝ) / sigX + 1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) *
              (141 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX))) +
            1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX) * ((HMI : ℝ) / (sigX * LAM))))))

theorem Rpi_le : Rpi ≤ (RPI : ℝ) / 2 ^ 192 := by
  unfold Rpi
  simp only [Fintype.card_fin]
  norm_num [DMI, XMI, HMI, RTI, TMI, CPI, RPI, sigX, LAM]
/-! ## Assembly -/

theorem D_abs {M : ℕ} (hM : 3 ≤ M) (k : Fin 141) :
    |cvsEntry M (6 / 5) (signedFreq k) (signedFreq k)| ≤ (DMI : ℝ) / 2 ^ 49 := by
  have h := diag_box hM k
  have hk := k.isLt
  obtain ⟨-, -, h3, -⟩ := tab_diag (m := Int.natAbs (signedFreq k))
    (by simp only [signedFreq]; omega)
  have h3' : |d2 k| + dr k ≤ DMI := by rw [← Int.natCast_natAbs]; exact h3
  have h3'' : |(d2 k : ℝ)| + (dr k : ℝ) ≤ DMI := by exact_mod_cast h3'
  have := abs_sub_abs_le_abs_sub (cvsEntry M (6 / 5) (signedFreq k) (signedFreq k))
    ((d2 k : ℝ) / 2 ^ 49)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 49)] at this
  have e : (DMI : ℝ) / 2 ^ 49 = (|(d2 k : ℝ)| + (dr k : ℝ)) / 2 ^ 49 +
      ((DMI : ℝ) - (|(d2 k : ℝ)| + dr k)) / 2 ^ 49 := by ring
  have : 0 ≤ ((DMI : ℝ) - (|(d2 k : ℝ)| + dr k)) / 2 ^ 49 := div_nonneg (by linarith) (by positivity)
  rw [add_div] at e
  linarith

theorem dr_nonneg (k : Fin 141) : (0 : ℝ) ≤ (dr k : ℝ) / 2 ^ 49 := by
  have hk := k.isLt
  have := (tab_diag (m := Int.natAbs ((k.val : ℤ) - 70)) (by omega)).2.2.2
  exact div_nonneg (by exact_mod_cast this) (by positivity)

theorem tr_bounds (k : Fin 141) : 0 ≤ tr k ∧ tr k ≤ RTI := by
  have hk := k.isLt
  unfold tr
  split_ifs with h
  · exact ⟨le_rfl, by norm_num [RTI]⟩
  · have := tab_tau (m := Int.natAbs ((k.val : ℤ) - 70) - 1) (by omega)
    exact ⟨this.2.2.2.1, this.2.2.2.2⟩

theorem tK_abs (k : Fin 141) : |(tK k : ℝ) / 2 ^ 49| ≤ (TMI : ℝ) / 2 ^ 49 := by
  have hk := k.isLt
  have hz : (tK k).natAbs ≤ TMI := by
    unfold tK
    split_ifs with h1 h2
    · rw [Int.natAbs_neg]; exact (tab_tau (m := 69 - k.val) (by omega)).2.2.1
    · simp
    · exact (tab_tau (m := k.val - 71) (by omega)).2.2.1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 49)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : |tK k| ≤ (TMI : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hz
  rw [← Int.cast_abs]; exact_mod_cast this

theorem C_bounds : 6 / 5 / (2 * Real.pi ^ 2) ≤ (CPI : ℝ) / 2 ^ 64 ∧
    (C2 : ℝ) / (5 * SI) ≤ (CPI : ℝ) / 2 ^ 64 ∧
    |6 / 5 / (2 * Real.pi ^ 2) - (C2 : ℝ) / (5 * SI)| ≤ 3 * (1 / 2 ^ 63) / 405 := by
  obtain ⟨hs, hsh9, hpi9, hCPb⟩ := pi_sq_bounds
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have e1 : 6 / 5 / (2 * Real.pi ^ 2) = 3 / (5 * Real.pi ^ 2) := by field_simp; ring
  have e2 : (C2 : ℝ) / (5 * SI) = 3 / (5 * ((SI : ℝ) / 2 ^ 70)) := by
    rw [show (C2 : ℝ) = 3 * 2 ^ 70 by norm_num [C2]]
    have : (SI : ℝ) ≠ 0 := by norm_num [SI]
    field_simp
  refine ⟨e1 ▸ hCPb, ?_, ?_⟩
  · rw [show (C2 : ℝ) = 3 * 2 ^ 70 by norm_num [C2]]
    norm_num [SI, CPI]
  · rw [e1, e2]
    set sh := (SI : ℝ) / 2 ^ 70
    have hsh : 0 < sh := by linarith
    rw [show 3 / (5 * Real.pi ^ 2) - 3 / (5 * sh) = 3 * (sh - Real.pi ^ 2) / (5 * (Real.pi ^ 2 * sh)) by
      field_simp, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 5 * (Real.pi ^ 2 * sh) by
        positivity), div_le_iff₀ (by positivity), abs_sub_comm]
    have hp : (81 : ℝ) ≤ Real.pi ^ 2 * sh := by nlinarith
    norm_num at hs ⊢
    nlinarith [abs_nonneg (Real.pi ^ 2 - sh)]


/-! ## Consequences of the concrete check `bigCheck = true`

Everything below assumes only the closed Boolean computation `bigCheck = true`
(as an instance of `Fact`); no analytic hypothesis remains. -/

section Check

variable [hc : Fact (bigCheck = true)]
include hc

/-! ## Unpacking the kernel checks -/

theorem bigCheck_parts :
    (∀ m : ℕ, m < 140 → LAM % ((m : ℤ) + 1) = 0) ∧
    (∀ k < 141, (kL k).all (fun x => x.natAbs ≤ B1) = true) ∧
    (∀ i < 139, colOk i = true) ∧
    (∀ i < 139, ∀ j, i ≤ j → j < 139 → entryOk i j = true) := by
  have h := hc.out
  simp only [bigCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun k hk => List.all_eq_true.mpr (h2 k hk), h3, fun i hi j hij hj => h4 i hi j ?_⟩
  simp only [List.mem_range'_1]
  omega

theorem colOk_parts {i : ℕ} (hi : i < 139) :
    (xL i).all (fun x => x.natAbs ≤ XMI) = true ∧ (hL i).all (fun x => x.natAbs ≤ HMI) = true ∧
    (vL i).all (fun x => x.natAbs ≤ B2) = true ∧ (wL i).all (fun x => x.natAbs ≤ B2) = true ∧
    T128 * ((List.range 141).map fun k => dr k * (xI k i * xI k i)).sum ≤
      (AD.getD i 0 : ℤ) * AD.getD i 0 * Q49 ∧
    T128 * ((List.range 141).map fun k => tr k * (xI k i * xI k i)).sum ≤
      (AT.getD i 0 : ℤ) * AT.getD i 0 * Q49 ∧
    T128 * ((List.range 141).map fun k => tr k * (hI k i * hI k i)).sum ≤
      (BT.getD i 0 : ℤ) * BT.getD i 0 * (Q49 * LAM * LAM) := by
  have h := bigCheck_parts.2.2.1 i hi
  simp only [colOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem xI_abs {k i : ℕ} (hk : k < 141) (hi : i < 139) : |(xI k i : ℝ)| ≤ XMI := by
  have h := all_natAbs (colOk_parts hi).1 (xI k i)
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  rw [abs_le]; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem xL_B1 {i : ℕ} (hi : i < 139) : (xL i).all (fun x => x.natAbs ≤ B1) = true := by
  have h := (colOk_parts hi).1
  have hB : XMI ≤ B1 := by norm_num [XMI, B1]
  simp only [List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact fun x hx => (h x hx).trans hB

theorem hI_eq {k i : ℕ} (hk : k < 141) (hi : i < 139) :
    hI k i = ∑ l ∈ range 141, kp k l * xI l i := by
  have hk' : k < kPk.length := by simp [kPk, hk]
  rw [hI, hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk',
    Option.map_some, Option.getD_some]
  have e : kPk[k] = (pack b1 (offRow B1 (kL k)), (kL k).sum) := by simp [kPk]
  rw [e]
  exact gram_range (kp k) (fun l => xI l i) (by norm_num) (bigCheck_parts.2.1 k hk) (xL_B1 hi)
    (by decide +kernel)

theorem hI_abs {k i : ℕ} (hk : k < 141) (hi : i < 139) : |(hI k i : ℝ)| ≤ HMI := by
  have hk' : k < (hL i).length := by simp [hL, kPk, hk]
  have h := all_natAbs (colOk_parts hi).2.1 (hI k i) (by
    rw [hI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact List.getElem_mem hk')
  rw [abs_le]; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem neI_eq {i j : ℕ} (hi : i < 139) (hj : j < 139) :
    neI i j = C1 * ∑ k ∈ range 141, d2 k * xI k i * xI k j +
      C2 * ∑ k ∈ range 141, (tK k * xI k i * hI k j + hI k i * (tK k * xI k j)) := by
  have ci : cols.getD i default = colPk i := getD_map_range colPk default hi
  have cj : cols.getD j default = colPk j := getD_map_range colPk default hj
  rw [neI, ci, cj]
  simp only [colPk, vL, wL]
  rw [gram_range (vI i) (wI j) (by norm_num) (colOk_parts hi).2.2.1 (colOk_parts hj).2.2.2.1
    (by decide +kernel)]
  rw [show (423 : ℕ) = 141 + (141 + 141) from rfl, sum_range_add, sum_range_add, mul_sum, mul_sum,
    ← sum_add_distrib]
  congr 1
  · exact sum_congr rfl fun k hk => by
      have := mem_range.mp hk; simp only [vI, wI, if_pos this]; ring
  · exact sum_congr rfl fun k hk => by
      have := mem_range.mp hk
      simp only [vI, wI, show ¬ 141 + k < 141 by omega, show 141 + k < 282 by omega,
        show ¬ 141 + (141 + k) < 141 by omega, show ¬ 141 + (141 + k) < 282 by omega, if_false,
        if_true, show 141 + k - 141 = k by omega, show 141 + (141 + k) - 282 = k by omega]
      ring

theorem kp_real {k l : ℕ} (hk : k < 141) (hl : l < 141) :
    (kp k l : ℝ) = (LAM : ℝ) / ((k : ℝ) - l) := by
  rcases eq_or_ne k l with rfl | hkl
  · simp [kp]
  · have hd : ((k : ℤ) - l) ∣ LAM := by
      have h := bigCheck_parts.1 (Int.natAbs ((k : ℤ) - l) - 1) (by omega)
      have e : (((Int.natAbs ((k : ℤ) - l) - 1 : ℕ) : ℤ) + 1) = (Int.natAbs ((k : ℤ) - l) : ℤ) := by
        omega
      rw [e] at h
      exact Int.natAbs_dvd.mp (Int.dvd_of_emod_eq_zero h)
    have hne : ((((k : ℤ) - l : ℤ)) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    rw [kp, if_neg hkl, Int.cast_div hd hne]
    push_cast; ring

theorem xh_abs (k : Fin 141) (i : Fin 139) : |(xI k i : ℝ) / sigX| ≤ (XMI : ℝ) / sigX := by
  rw [abs_div, abs_of_pos (show (0 : ℝ) < sigX by norm_num [sigX])]
  exact div_le_div_of_nonneg_right (xI_abs k.isLt i.isLt) (by norm_num [sigX])

theorem hh_abs (k : Fin 141) (i : Fin 139) :
    |(hI k i : ℝ) / (sigX * LAM)| ≤ (HMI : ℝ) / (sigX * LAM) := by
  have hp : (0 : ℝ) < sigX * LAM := by norm_num [sigX, LAM]
  rw [abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right (hI_abs k.isLt i.isLt) hp.le

theorem X_err' (k : Fin 141) (i : Fin 139) :
    |transformedCoeff k i - (xI k i : ℝ) / sigX| ≤ 1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX) :=
  (X_err k i).trans (mul_le_mul_of_nonneg_left (xh_abs k i) (by positivity))

theorem Hh_eq (k : Fin 141) (i : Fin 139) :
    ∑ l : Fin 141, (xI l i : ℝ) / sigX / ((signedFreq k : ℝ) - (signedFreq l : ℝ)) =
      (hI k i : ℝ) / (sigX * LAM) := by
  rw [hI_eq k.isLt i.isLt]
  push_cast
  rw [sum_div, show (∑ l : Fin 141, (xI l i : ℝ) / sigX / ((signedFreq k : ℝ) - (signedFreq l : ℝ)))
      = ∑ l ∈ range 141, (xI l i : ℝ) / sigX / ((signedFreq k : ℝ) - (((l : ℤ) - 70 : ℤ) : ℝ)) from
      Fin.sum_univ_eq_sum_range (fun l => (xI l i : ℝ) / sigX /
        ((signedFreq k : ℝ) - (((l : ℤ) - 70 : ℤ) : ℝ))) 141]
  refine sum_congr rfl fun l hl => ?_
  rw [kp_real k.isLt (mem_range.mp hl)]
  have hLAM : (LAM : ℝ) ≠ 0 := by norm_num [LAM]
  have hsig : (sigX : ℝ) ≠ 0 := by norm_num [sigX]
  simp only [signedFreq]
  push_cast
  rcases eq_or_ne (k.val : ℝ) (l : ℝ) with h | h
  · rw [h]; simp
  · have h' : (k.val : ℝ) - 70 - ((l : ℝ) - 70) ≠ 0 := by intro e; apply h; linarith
    have h'' : (k.val : ℝ) - l ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

theorem H_err (k : Fin 141) (i : Fin 139) :
    |(∑ l, transformedCoeff l i / ((signedFreq k : ℝ) - (signedFreq l : ℝ))) -
        (hI k i : ℝ) / (sigX * LAM)| ≤ 141 * (1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) := by
  rw [← Hh_eq, ← sum_sub_distrib]
  have h := sum_abs_le_card (fun l : Fin 141 =>
    transformedCoeff l i / ((signedFreq k : ℝ) - (signedFreq l : ℝ)) -
      (xI l i : ℝ) / sigX / ((signedFreq k : ℝ) - (signedFreq l : ℝ)))
    (c := 1 / 2 ^ 63 / 9 * ((XMI : ℝ) / sigX)) fun l => by
      rw [← sub_div, show (signedFreq k : ℝ) - (signedFreq l : ℝ) =
        ((signedFreq k - signedFreq l : ℤ) : ℝ) by push_cast; ring]
      exact (abs_div_int_le _ _).trans (X_err' l i)
  simpa using h
/-- `Ê_ij = neI i j / DE`. -/
theorem Ehat_eq (i j : Fin 139) :
    (∑ k : Fin 141, (xI k i : ℝ) / sigX * ((xI k j : ℝ) / sigX) * ((d2 k : ℝ) / 2 ^ 49)) +
      ∑ k : Fin 141, (C2 : ℝ) / (5 * SI) * ((tK k : ℝ) / 2 ^ 49) *
        ((xI k i : ℝ) / sigX * ((hI k j : ℝ) / (sigX * LAM)) +
          (xI k j : ℝ) / sigX * ((hI k i : ℝ) / (sigX * LAM))) =
    (neI i j : ℝ) / DE := by
  rw [neI_eq i.isLt j.isLt, DE_real,
    Fin.sum_univ_eq_sum_range (fun k => (xI k i : ℝ) / sigX * ((xI k j : ℝ) / sigX) *
      ((d2 k : ℝ) / 2 ^ 49)) 141,
    Fin.sum_univ_eq_sum_range (fun k => (C2 : ℝ) / (5 * SI) * ((tK k : ℝ) / 2 ^ 49) *
      ((xI k i : ℝ) / sigX * ((hI k j : ℝ) / (sigX * LAM)) +
        (xI k j : ℝ) / sigX * ((hI k i : ℝ) / (sigX * LAM)))) 141]
  have hsig : (sigX : ℝ) ≠ 0 := by norm_num [sigX]
  have hLAM : (LAM : ℝ) ≠ 0 := by norm_num [LAM]
  have hSI : (SI : ℝ) ≠ 0 := by norm_num [SI]
  simp only [C1]
  push_cast
  rw [add_div, mul_sum, mul_sum, sum_div, sum_div]
  congr 1 <;> exact sum_congr rfl fun k _ => by field_simp

theorem sumD_le (i : Fin 139) :
    ∑ k : Fin 141, (dr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2 ≤
      ((AD.getD i 0 : ℝ) / 2 ^ 64) ^ 2 := by
  have h := (colOk_parts i.isLt).2.2.2.2.1
  rw [lsum_range] at h
  have h' : (T128 : ℝ) * ∑ k ∈ range 141, (dr k : ℝ) * ((xI k i : ℝ) * xI k i) ≤
      (AD.getD i 0 : ℝ) * AD.getD i 0 * Q49 := by exact_mod_cast h
  rw [show (T128 : ℝ) = 2 ^ 128 by norm_num [T128], Q49_real] at h'
  have hQ : (0 : ℝ) < 2 ^ 49 * sigX * sigX := by norm_num [sigX]
  rw [Fin.sum_univ_eq_sum_range (fun k => (dr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2) 141,
    show (∑ k ∈ range 141, (dr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2) =
      (∑ k ∈ range 141, (dr k : ℝ) * ((xI k i : ℝ) * xI k i)) / (2 ^ 49 * sigX * sigX) by
      rw [sum_div]; exact sum_congr rfl fun k _ => by field_simp]
  exact cs_real hQ h'

theorem sumT_le (i : Fin 139) :
    ∑ k : Fin 141, (tr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2 ≤
      ((AT.getD i 0 : ℝ) / 2 ^ 64) ^ 2 := by
  have h := (colOk_parts i.isLt).2.2.2.2.2.1
  rw [lsum_range] at h
  have h' : (T128 : ℝ) * ∑ k ∈ range 141, (tr k : ℝ) * ((xI k i : ℝ) * xI k i) ≤
      (AT.getD i 0 : ℝ) * AT.getD i 0 * Q49 := by exact_mod_cast h
  rw [show (T128 : ℝ) = 2 ^ 128 by norm_num [T128], Q49_real] at h'
  have hQ : (0 : ℝ) < 2 ^ 49 * sigX * sigX := by norm_num [sigX]
  rw [Fin.sum_univ_eq_sum_range (fun k => (tr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2) 141,
    show (∑ k ∈ range 141, (tr k : ℝ) / 2 ^ 49 * ((xI k i : ℝ) / sigX) ^ 2) =
      (∑ k ∈ range 141, (tr k : ℝ) * ((xI k i : ℝ) * xI k i)) / (2 ^ 49 * sigX * sigX) by
      rw [sum_div]; exact sum_congr rfl fun k _ => by field_simp]
  exact cs_real hQ h'

theorem sumH_le (i : Fin 139) :
    ∑ k : Fin 141, (tr k : ℝ) / 2 ^ 49 * ((hI k i : ℝ) / (sigX * LAM)) ^ 2 ≤
      ((BT.getD i 0 : ℝ) / 2 ^ 64) ^ 2 := by
  have h := (colOk_parts i.isLt).2.2.2.2.2.2
  rw [lsum_range] at h
  have h' : (T128 : ℝ) * ∑ k ∈ range 141, (tr k : ℝ) * ((hI k i : ℝ) * hI k i) ≤
      (BT.getD i 0 : ℝ) * BT.getD i 0 * (Q49 * LAM * LAM) := by exact_mod_cast h
  rw [show (T128 : ℝ) = 2 ^ 128 by norm_num [T128], Q49_real] at h'
  have hQ : (0 : ℝ) < 2 ^ 49 * sigX * sigX * LAM * LAM := by norm_num [sigX, LAM]
  rw [Fin.sum_univ_eq_sum_range (fun k => (tr k : ℝ) / 2 ^ 49 * ((hI k i : ℝ) / (sigX * LAM)) ^ 2) 141,
    show (∑ k ∈ range 141, (tr k : ℝ) / 2 ^ 49 * ((hI k i : ℝ) / (sigX * LAM)) ^ 2) =
      (∑ k ∈ range 141, (tr k : ℝ) * ((hI k i : ℝ) * hI k i)) /
        (2 ^ 49 * sigX * sigX * LAM * LAM) by
      rw [sum_div]; exact sum_congr rfl fun k _ => by field_simp]
  exact cs_real hQ (by linarith)

theorem entry_mem_le {M : ℕ} (hM : 3 ≤ M) (i j : Fin 139) (hij : i.val ≤ j.val) :
    (Im certI i j).Mem certQ (projectedEntry M i j) ∧
      (Im certI j i).Mem certQ (projectedEntry M i j) := by
  obtain ⟨hC1, hC2, hdC⟩ := C_bounds
  have herr : |projectedEntry M i j - (neI i j : ℝ) / DE| ≤
      (AD.getD i 0 : ℝ) / 2 ^ 64 * ((AD.getD j 0 : ℝ) / 2 ^ 64) +
        (CPI : ℝ) / 2 ^ 64 * ((AT.getD i 0 : ℝ) / 2 ^ 64 * ((BT.getD j 0 : ℝ) / 2 ^ 64) +
          (AT.getD j 0 : ℝ) / 2 ^ 64 * ((BT.getD i 0 : ℝ) / 2 ^ 64)) + Rpi := by
    rw [projectedEntry_collect, ← Ehat_eq]
    exact entry_error (ι := Fin 141)
      (fun k => transformedCoeff k i) (fun k => transformedCoeff k j)
      (fun k => (xI k i : ℝ) / sigX) (fun k => (xI k j : ℝ) / sigX)
      (fun k => ∑ l, transformedCoeff l i / ((signedFreq k : ℝ) - (signedFreq l : ℝ)))
      (fun k => ∑ l, transformedCoeff l j / ((signedFreq k : ℝ) - (signedFreq l : ℝ)))
      (fun k => (hI k i : ℝ) / (sigX * LAM)) (fun k => (hI k j : ℝ) / (sigX * LAM))
      (fun k => cvsEntry M (6 / 5) (signedFreq k) (signedFreq k)) (fun k => (d2 k : ℝ) / 2 ^ 49)
      (fun k => (dr k : ℝ) / 2 ^ 49) (fun k => tau M (6 / 5) (signedFreq k))
      (fun k => (tK k : ℝ) / 2 ^ 49) (fun k => (tr k : ℝ) / 2 ^ 49)
      (6 / 5 / (2 * Real.pi ^ 2)) ((C2 : ℝ) / (5 * SI))
      (hD := fun k => diag_box hM k) (hT := fun k => tau_box hM k)
      (hX := fun k => X_err' k i) (hY := fun k => X_err' k j)
      (hH := fun k => H_err k i) (hG := fun k => H_err k j)
      (hXm := fun k => xh_abs k i) (hYm := fun k => xh_abs k j)
      (hHm := fun k => hh_abs k i) (hGm := fun k => hh_abs k j)
      (hDm := fun k => D_abs hM k) (hTm := fun k => tK_abs k)
      (hrD := dr_nonneg) (hrT := fun k => div_nonneg (by exact_mod_cast (tr_bounds k).1)
        (by positivity))
      (hRT := fun k => div_le_div_of_nonneg_right (by exact_mod_cast (tr_bounds k).2)
        (by positivity))
      (hRT0 := by norm_num [RTI]) (hC := by positivity) (hCP := hC1)
      (hCh := by norm_num [C2, SI]) (hChP := hC2) (hdC := hdC)
      (hdX := by norm_num [XMI, sigX]) (hdH := by norm_num [XMI, sigX])
      (hXM := by norm_num [XMI, sigX]) (hHM := by norm_num [HMI, sigX, LAM])
      (hTM := by norm_num [TMI]) (haD := by positivity) (hbD := by positivity)
      (haT := by positivity) (hbT := by positivity) (hcH := by positivity) (hcG := by positivity)
      (sD1 := sumD_le i) (sD2 := sumD_le j) (sT1 := sumT_le i) (sT2 := sumT_le j)
      (sH1 := sumH_le i) (sH2 := sumH_le j)
  have hrad : (AD.getD i 0 : ℝ) / 2 ^ 64 * ((AD.getD j 0 : ℝ) / 2 ^ 64) +
        (CPI : ℝ) / 2 ^ 64 * ((AT.getD i 0 : ℝ) / 2 ^ 64 * ((BT.getD j 0 : ℝ) / 2 ^ 64) +
          (AT.getD j 0 : ℝ) / 2 ^ 64 * ((BT.getD i 0 : ℝ) / 2 ^ 64)) + Rpi ≤
      (radI i j : ℝ) / SR := by
    have := Rpi_le
    rw [radI, show (SR : ℝ) = 2 ^ 192 by norm_num [SR]]
    push_cast
    rw [show (T64 : ℝ) = 2 ^ 64 by norm_num [T64]]
    have e : ((AD.getD i 0 : ℝ) * (AD.getD j 0 : ℝ) * 2 ^ 64 +
        (CPI : ℝ) * ((AT.getD i 0 : ℝ) * (BT.getD j 0 : ℝ) + (AT.getD j 0 : ℝ) * (BT.getD i 0 : ℝ)) +
          (RPI : ℝ)) / 2 ^ 192 =
        (AD.getD i 0 : ℝ) / 2 ^ 64 * ((AD.getD j 0 : ℝ) / 2 ^ 64) +
        (CPI : ℝ) / 2 ^ 64 * ((AT.getD i 0 : ℝ) / 2 ^ 64 * ((BT.getD j 0 : ℝ) / 2 ^ 64) +
          (AT.getD j 0 : ℝ) / 2 ^ 64 * ((BT.getD i 0 : ℝ) / 2 ^ 64)) + (RPI : ℝ) / 2 ^ 192 := by
      ring
    rw [e]
    linarith
  have hx := herr.trans hrad
  have h := bigCheck_parts.2.2.2 i i.isLt j hij j.isLt
  simp only [entryOk, Bool.and_eq_true] at h
  exact ⟨ivOk_mem h.1 hx, ivOk_mem h.2 hx⟩

/-- **`hIv` for the packed `139 × 139` certificate at `L = 6/5`**: every projected source entry lies
in its stored interval, for every prime cutoff `M ≥ 3`. -/
theorem projectedEntry_mem_certI_of_check {M : ℕ} (hM : 3 ≤ M) :
    ∀ i j : Fin 139, (Im certI i.val j.val).Mem certQ (projectedEntry M i j) := by
  intro i j
  rcases le_total i.val j.val with h | h
  · exact (entry_mem_le hM i j h).1
  · rw [AEGIS.CvSProjectedSymmetryV1.projectedEntry_symm M i j]
    exact (entry_mem_le hM j i h).2

/-- The packed certificate with its interval hypothesis discharged (given `bigCheck = true`). -/
theorem projected_lower_L12_of_check {M : ℕ} (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    ((certEps - certEta : ℤ) : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤
      2 ^ certQ * (∑ i, ∑ j,
        c i * (starRingEnd ℂ) (c j) * (projectedEntry M i j : ℂ)).re :=
  AEGIS.CvSProjectedSymmetryV1.projected_lower_of_Iv (projectedEntry_mem_certI_of_check hM) c

end Check

end AEGIS.CvSProjectedEntryL12V1

#print axioms AEGIS.CvSProjectedEntryL12V1.cs_bound
#print axioms AEGIS.CvSProjectedEntryL12V1.entry_error
#print axioms AEGIS.CvSProjectedEntryL12V1.gram_range
#print axioms AEGIS.CvSProjectedEntryL12V1.tabOk_true
#print axioms AEGIS.CvSProjectedEntryL12V1.transformedCoeff_eq
#print axioms AEGIS.CvSProjectedEntryL12V1.signedEntry_eq
#print axioms AEGIS.CvSProjectedEntryL12V1.projectedEntry_collect
#print axioms AEGIS.CvSProjectedEntryL12V1.diag_box
#print axioms AEGIS.CvSProjectedEntryL12V1.tau_box
#print axioms AEGIS.CvSProjectedEntryL12V1.pi_sq_bounds
#print axioms AEGIS.CvSProjectedEntryL12V1.X_err
#print axioms AEGIS.CvSProjectedEntryL12V1.Rpi_le
#print axioms AEGIS.CvSProjectedEntryL12V1.ivOk_mem
#print axioms AEGIS.CvSProjectedEntryL12V1.C_bounds
#print axioms AEGIS.CvSProjectedEntryL12V1.hI_eq
#print axioms AEGIS.CvSProjectedEntryL12V1.neI_eq
#print axioms AEGIS.CvSProjectedEntryL12V1.kp_real
#print axioms AEGIS.CvSProjectedEntryL12V1.H_err
#print axioms AEGIS.CvSProjectedEntryL12V1.Ehat_eq
#print axioms AEGIS.CvSProjectedEntryL12V1.entry_mem_le
#print axioms AEGIS.CvSProjectedEntryL12V1.projectedEntry_mem_certI_of_check
#print axioms AEGIS.CvSProjectedEntryL12V1.projected_lower_L12_of_check
