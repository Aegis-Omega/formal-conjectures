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

import CvSTraceGammaV1
import CvSHplusBoundsV1

/-!
# One cell of the trace certificate at L = 4/3

A cell is `|t| ∈ [a, b]` with rational data `(s, ε, α, n₀, n₁)`. `cellOk` checks in exact rational
arithmetic that

* `α² ≥ A⁺`, the Parseval bound on `∫|f_t − P_t|²` over the cell (`fT_tail`, with `cos(tL)`
  enclosed by `sinPi_bounds`);
* `n_s² (a² + 1/4)² ≥` the corner bound of the closed form `num_normSq` for the Cramer
  numerators;
* `s ≥ m + w₂⁺ + w₃⁺ − hpLo(a²)`.

`cell_sound` then gives, for every `t` in the cell, `trialDist(t) ≤ TD c` (via `trialDist_le`,
`gram_eq`, `rhs_eq`, `cramer_pert`) and `m − ScertM 3 t ≤ s`.

Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSTraceCellL43V1

open AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1 AEGIS.CvSDiagL12V1 AEGIS.CvSHplusBoundsV1
open AEGIS.CvSPrimeBlockV1 AEGIS.CvSFourierIntervalV1 AEGIS.CvSTraceCoefV1 AEGIS.CvSTraceCramerV1
open AEGIS.CvSTraceDistV1 AEGIS.CvSTraceGramPertV1 AEGIS.CvSTraceGammaV1 AEGIS.CvSTraceV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-! ### Rational interval products -/

def mlo (x1 x2 y1 y2 : ℚ) : ℚ := min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2))
def mhi (x1 x2 y1 y2 : ℚ) : ℚ := max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2))

theorem lin_le {x y a b : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) : x * y ≤ max (x * a) (x * b) := by
  rcases le_total 0 x with h | h
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left h2 h)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_left h1 h)

theorem le_lin {x y a b : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) : min (x * a) (x * b) ≤ x * y := by
  rcases le_total 0 x with h | h
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_left h1 h)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_left h2 h)

theorem lin_le' {x y a b : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) : y * x ≤ max (a * x) (b * x) := by
  rw [mul_comm y, mul_comm a, mul_comm b]
  exact lin_le h1 h2

theorem le_lin' {x y a b : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) : min (a * x) (b * x) ≤ y * x := by
  rw [mul_comm y, mul_comm a, mul_comm b]
  exact le_lin h1 h2

theorem mul_mem {x y : ℝ} {x1 x2 y1 y2 : ℚ} (hx1 : (x1 : ℝ) ≤ x) (hx2 : x ≤ x2)
    (hy1 : (y1 : ℝ) ≤ y) (hy2 : y ≤ y2) :
    (mlo x1 x2 y1 y2 : ℝ) ≤ x * y ∧ x * y ≤ mhi x1 x2 y1 y2 := by
  simp only [mlo, mhi, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · set T := min (min ((x1 : ℝ) * y1) (x1 * y2)) (min ((x2 : ℝ) * y1) (x2 * y2))
    have t11 : T ≤ (x1 : ℝ) * y1 := (min_le_left _ _).trans (min_le_left _ _)
    have t12 : T ≤ (x1 : ℝ) * y2 := (min_le_left _ _).trans (min_le_right _ _)
    have t21 : T ≤ (x2 : ℝ) * y1 := (min_le_right _ _).trans (min_le_left _ _)
    have t22 : T ≤ (x2 : ℝ) * y2 := (min_le_right _ _).trans (min_le_right _ _)
    have hA := le_lin' (x := (y1 : ℝ)) hx1 hx2
    have hB := le_lin' (x := (y2 : ℝ)) hx1 hx2
    exact (le_min ((le_min t11 t21).trans hA) ((le_min t12 t22).trans hB)).trans (le_lin hy1 hy2)
  · set T := max (max ((x1 : ℝ) * y1) (x1 * y2)) (max ((x2 : ℝ) * y1) (x2 * y2))
    have t11 : (x1 : ℝ) * y1 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
    have t12 : (x1 : ℝ) * y2 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
    have t21 : (x2 : ℝ) * y1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
    have t22 : (x2 : ℝ) * y2 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
    have hA := lin_le' (x := (y1 : ℝ)) hx1 hx2
    have hB := lin_le' (x := (y2 : ℝ)) hx1 hx2
    exact (lin_le hy1 hy2).trans (max_le (hA.trans (max_le t11 t21)) (hB.trans (max_le t12 t22)))

/-! ### Constants -/

def e23Lo : ℚ := 158894902126248433646108355 / 309485009821345068724781056
def e23Hi : ℚ := 635579608504993734584433421 / 1237940039285380274899124224

theorem e23_bounds : (e23Lo : ℝ) ≤ Real.exp (-2 / 3) ∧ Real.exp (-2 / 3) ≤ e23Hi := by
  have h := Real.exp_bound (x := -2 / 3) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e23Lo, e23Hi] <;> push_cast <;> linarith [h.1, h.2]

def xL : ℚ := e23Lo
def xH : ℚ := e23Hi
def yL : ℚ := 1 / e23Hi
def yH : ℚ := 1 / e23Lo
def hL : ℚ := 3 * piLo / 2
def nG00 : ℚ := 1 - xL ^ 2
def nG11 : ℚ := yH ^ 2 - 1
def Dlo : ℚ := xL ^ 2 + yL ^ 2 - 2 - 16 / 9
def tb0 : ℚ := rup ((1 - xL) ^ 2 * (3 / 4) * (2 / (hL * (hL * 70))))
def tb1 : ℚ := rup ((yH - 1) ^ 2 * (3 / 4) * (2 / (hL * (hL * 70))))

structure Consts where
  rho0 : ℚ
  rho1 : ℚ

def Consts.r00 (k : Consts) : ℚ := k.rho0 ^ 2
def Consts.r11 (k : Consts) : ℚ := k.rho1 ^ 2
def Consts.r01 (k : Consts) : ℚ := k.rho0 * k.rho1
def Consts.dd (k : Consts) : ℚ :=
  nG00 * k.r11 + nG11 * k.r00 + 4 / 3 * k.r01 + 4 / 3 * k.r01 + k.r00 * k.r11 + k.r01 * k.r01
def Consts.Den (k : Consts) : ℚ := Dlo - k.dd

def Yb0 : ℚ := 2 * (xH + 1)
def Yb1 : ℚ := 2 * (yH + 1)

def constOk (k : Consts) : Bool :=
  decide (0 ≤ k.rho0) && decide (0 ≤ k.rho1) && decide (tb0 ≤ k.rho0 ^ 2) &&
    decide (tb1 ≤ k.rho1 ^ 2) && decide (0 < k.Den)

/-- Rational enclosures of the closed-form coefficients of one Cramer numerator. -/
structure NC where
  p0 : ℚ
  p2 : ℚ
  q0l : ℚ
  q0h : ℚ
  q2l : ℚ
  q2h : ℚ
  rl : ℚ
  rh : ℚ

def mkNC (u1l u1h u2l u2h v1l v1h v2l v2h : ℚ) : NC :=
  ⟨rup (mhi u1l u1h u1l u1h + mhi v1l v1h v1l v1h), rup (mhi u2l u2h u2l u2h + mhi v2l v2h v2l v2h),
    rdn (mlo u1l u1h v1l v1h), rup (mhi u1l u1h v1l v1h),
    rdn (mlo u2l u2h v2l v2h), rup (mhi u2l u2h v2l v2h),
    rdn (mlo u2l u2h v1l v1h - mhi u1l u1h v2l v2h), rup (mhi u2l u2h v1l v1h - mlo u1l u1h v2l v2h)⟩

def nc0 : NC := mkNC ((7 / 3 * yL - xH) / 2) ((7 / 3 * yH - xL) / 2) (-(1 / 3) * yH - xH)
  (-(1 / 3) * yL - xL) ((yL ^ 2 + 1 / 3) / 2) ((yH ^ 2 + 1 / 3) / 2) (yL ^ 2 - 7 / 3) (yH ^ 2 - 7 / 3)

def nc1 : NC := mkNC ((-(1 / 3) * xH - yH) / 2) ((-(1 / 3) * xL - yL) / 2) (yL - 7 / 3 * xH)
  (yH - 7 / 3 * xL) ((xL ^ 2 - 7 / 3) / 2) ((xH ^ 2 - 7 / 3) / 2) (-(1 / 3) - xH ^ 2)
  (-(1 / 3) - xL ^ 2)

/-! ### Cells -/

structure Cell where
  a : ℚ
  b : ℚ
  s : ℚ
  eps : ℚ
  al : ℚ
  n0 : ℚ
  n1 : ℚ

def Cell.ul (c : Cell) : ℚ := c.a * (4 / 3) / piHi
def Cell.uh (c : Cell) : ℚ := c.b * (4 / 3) / piLo
def Cell.cl (c : Cell) : ℚ := rdn (sinPiLo (c.ul + 1 / 2) (c.uh + 1 / 2))
def Cell.ch (c : Cell) : ℚ := rup (sinPiHi (c.ul + 1 / 2) (c.uh + 1 / 2))
def Cell.sl (c : Cell) : ℚ := rdn (sinPiLo c.ul c.uh)
def Cell.sh (c : Cell) : ℚ := rup (sinPiHi c.ul c.uh)
def Cell.tail (c : Cell) : ℚ := 1 / (hL * (hL * 70 - c.b)) + 1 / (hL * (hL * 70 + c.a))
def Cell.Aup (c : Cell) : ℚ := (2 - 2 * c.cl) * (3 / 4) * c.tail

def Cell.Pup (c : Cell) (k : NC) : ℚ :=
  k.p0 + k.p2 * c.b ^ 2 +
    mhi (-2 * (k.q0h + mhi k.q2l k.q2h (c.a ^ 2) (c.b ^ 2)))
      (-2 * (k.q0l + mlo k.q2l k.q2h (c.a ^ 2) (c.b ^ 2))) c.cl c.ch +
    mhi (2 * mlo k.rl k.rh c.a c.b) (2 * mhi k.rl k.rh c.a c.b) c.sl c.sh

def Cell.d0 (c : Cell) (k : Consts) : ℚ :=
  nG11 * (c.al * k.rho0) + k.r11 * Yb0 + k.r11 * (c.al * k.rho0) + 4 / 3 * (c.al * k.rho1) +
    k.r01 * Yb1 + k.r01 * (c.al * k.rho1)

def Cell.d1 (c : Cell) (k : Consts) : ℚ :=
  nG00 * (c.al * k.rho1) + k.r00 * Yb1 + k.r00 * (c.al * k.rho1) + 4 / 3 * (c.al * k.rho0) +
    k.r01 * Yb0 + k.r01 * (c.al * k.rho0)

def Cell.G2 (c : Cell) (k : Consts) : ℚ :=
  ((c.n0 + c.d0 k) ^ 2 + (c.n1 + c.d1 k) ^ 2) / k.Den ^ 2

def Cell.TD (c : Cell) (k : Consts) : ℚ :=
  rup ((1 + c.eps) * c.Aup + (1 + 1 / c.eps) * c.G2 k * (tb0 + tb1))

def cellOk (m : ℚ) (c : Cell) : Bool :=
  decide (0 ≤ c.a) && decide (c.a < c.b) && decide (c.b < hL * 70) &&
    decide (|thLo c.ul| ≤ 2) && decide (|thLo (c.ul + 1 / 2)| ≤ 2) &&
    decide (0 ≤ c.al) && decide (c.Aup ≤ c.al ^ 2) && decide (0 < c.eps) &&
    decide (0 ≤ c.n0) && decide (c.Pup nc0 ≤ c.n0 ^ 2 * (c.a ^ 2 + 1 / 4) ^ 2) &&
    decide (0 ≤ c.n1) && decide (c.Pup nc1 ≤ c.n1 ^ 2 * (c.a ^ 2 + 1 / 4) ^ 2) &&
    decide (0 ≤ c.s) && logOk (aK ^ 2 + c.a ^ 2) &&
    decide (m + w2Hi + w3Hi - hpLo (c.a ^ 2) (c.a ^ 2) ≤ c.s)

/-! ### Real enclosures of the constants -/

theorem xL_pos : (0 : ℝ) < xL := by norm_num [xL, e23Lo]

theorem x_mem : (xL : ℝ) ≤ Real.exp (-2 / 3) ∧ Real.exp (-2 / 3) ≤ xH := e23_bounds

theorem xy_one : Real.exp (-2 / 3) * Real.exp (2 / 3) = 1 := by
  rw [← Real.exp_add]; norm_num

theorem y_mem : (yL : ℝ) ≤ Real.exp (2 / 3) ∧ Real.exp (2 / 3) ≤ yH := by
  have hx := x_mem
  have hy : Real.exp (2 / 3) = 1 / Real.exp (-2 / 3) := by
    rw [eq_div_iff (Real.exp_pos _).ne', mul_comm, xy_one]
  simp only [yL, yH, Rat.cast_div, Rat.cast_one]
  rw [hy]
  have h0 : (0 : ℝ) < e23Lo := xL_pos
  exact ⟨one_div_le_one_div_of_le (Real.exp_pos _) hx.2, one_div_le_one_div_of_le h0 hx.1⟩

theorem exp43 : Real.exp (4 / 3) = Real.exp (2 / 3) ^ 2 := by
  rw [sq, ← Real.exp_add]; norm_num

theorem expm43 : Real.exp (-(4 / 3)) = Real.exp (-2 / 3) ^ 2 := by
  rw [sq, ← Real.exp_add]; norm_num

theorem x_lt_one : Real.exp (-2 / 3) < 1 := by
  have := Real.exp_strictMono (show (-2 / 3 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this

theorem one_lt_y : 1 < Real.exp (2 / 3) := by
  have := Real.exp_strictMono (show (0 : ℝ) < 2 / 3 by norm_num); rwa [Real.exp_zero] at this

theorem hL_le : (hL : ℝ) ≤ 2 * Real.pi / (4 / 3) := by
  have := pi_bounds.1
  simp only [hL]
  push_cast
  linarith

theorem hL_pos : (0 : ℝ) < hL := by norm_num [hL, piLo]

theorem sq_le_of_mem {u : ℝ} {l h : ℚ} (h1 : (l : ℝ) ≤ u) (h2 : u ≤ h) : u * u ≤ mhi l h l h :=
  (mul_mem h1 h2 h1 h2).2

/-! ### The trigonometric enclosure on a cell -/

theorem trig_mem {c : Cell} (ha : 0 ≤ c.a) (hok0 : |thLo c.ul| ≤ 2)
    (hok1 : |thLo (c.ul + 1 / 2)| ≤ 2) {τ : ℝ} (h1 : (c.a : ℝ) ≤ τ) (h2 : τ ≤ c.b) :
    (c.cl : ℝ) ≤ Real.cos (τ * (4 / 3)) ∧ Real.cos (τ * (4 / 3)) ≤ c.ch ∧
      (c.sl : ℝ) ≤ Real.sin (τ * (4 / 3)) ∧ Real.sin (τ * (4 / 3)) ≤ c.sh := by
  have hπ := pi_bounds
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have hlo0 : (0 : ℝ) < piLo := by norm_num [piLo]
  set u := τ * (4 / 3) / Real.pi
  have hu : Real.pi * u = τ * (4 / 3) := by simp only [u]; field_simp
  have hul : ((c.ul : ℚ) : ℝ) ≤ u := by
    simp only [Cell.ul, u]
    push_cast
    calc (c.a : ℝ) * (4 / 3) / piHi ≤ c.a * (4 / 3) / Real.pi :=
          div_le_div_of_nonneg_left (by positivity) hpi0 hπ.2.le
      _ ≤ τ * (4 / 3) / Real.pi := by gcongr
  have huh : u ≤ ((c.uh : ℚ) : ℝ) := by
    simp only [Cell.uh, u]
    push_cast
    calc τ * (4 / 3) / Real.pi ≤ c.b * (4 / 3) / Real.pi := by gcongr
      _ ≤ c.b * (4 / 3) / piLo :=
          div_le_div_of_nonneg_left (by nlinarith) hlo0 hπ.1.le
  have hs := sinPi_bounds hul huh hok0
  have hc := sinPi_bounds (ul := c.ul + 1 / 2) (uh := c.uh + 1 / 2) (u := u + 1 / 2)
    (by push_cast; linarith) (by push_cast; linarith) hok1
  rw [hu] at hs
  have e : Real.sin (Real.pi * (u + 1 / 2)) = Real.cos (τ * (4 / 3)) := by
    rw [show Real.pi * (u + 1 / 2) = Real.pi * u + Real.pi / 2 by ring, Real.sin_add_pi_div_two, hu]
  rw [e] at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rdn_le _).trans hc.1
  · exact hc.2.trans (le_rup _)
  · exact (rdn_le _).trans hs.1
  · exact hs.2.trans (le_rup _)

/-! ### The Parseval tails on a cell -/

theorem tail_le {h τ a b hl : ℝ} (hl0 : 0 < hl) (hlh : hl ≤ h) (ha0 : 0 ≤ a) (ha : a ≤ τ)
    (hb : τ ≤ b) (hb70 : b < hl * 70) :
    1 / (h * (h * 70 - τ)) + 1 / (h * (h * 70 + τ)) ≤
      1 / (hl * (hl * 70 - b)) + 1 / (hl * (hl * 70 + a)) := by
  have h0 : 0 < h := hl0.trans_le hlh
  have e1 : 0 < hl * 70 - b := by linarith
  have e2 : 0 < hl * 70 + a := by linarith
  gcongr

theorem normSq_exp_sub_one (w : ℝ) : ‖cexp ((w : ℂ) * I) - 1‖ ^ 2 = 2 - 2 * Real.cos w := by
  rw [Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im]
  have := Real.cos_sq_add_sin_sq w
  nlinarith

theorem A_cell {c : Cell} (ha : 0 ≤ c.a) (hb70 : c.b < hL * 70) (hok0 : |thLo c.ul| ≤ 2)
    (hok1 : |thLo (c.ul + 1 / 2)| ≤ 2) {t : ℝ} (h1 : (c.a : ℝ) ≤ |t|) (h2 : |t| ≤ c.b) :
    ∫ x, ‖fT (4 / 3) t x - trigPoly (4 / 3) (K 70) (cT (by norm_num : (0 : ℝ) < 4 / 3) t) x‖ ^ 2 ≤
      c.Aup := by
  have h43 : (0 : ℝ) < 4 / 3 := by norm_num
  have hb70' : (c.b : ℝ) < hL * 70 := by exact_mod_cast hb70
  have hht : |t| < 2 * Real.pi / (4 / 3) * (70 : ℕ) := by
    push_cast; nlinarith [hL_le]
  have hT := fT_tail h43 (N := 70) hht
  have hc := (trig_mem ha hok0 hok1 h1 h2).1
  have ecos : Real.cos (t * (4 / 3)) = Real.cos (|t| * (4 / 3)) := by
    rw [← Real.cos_abs (t * (4 / 3)), abs_mul, abs_of_pos h43]
  have enorm : ‖cexp ((t : ℂ) * I * ((4 / 3 : ℝ) : ℂ)) - 1‖ ^ 2 = 2 - 2 * Real.cos (|t| * (4 / 3)) := by
    rw [show (t : ℂ) * I * ((4 / 3 : ℝ) : ℂ) = ((t * (4 / 3) : ℝ) : ℂ) * I by push_cast; ring,
      normSq_exp_sub_one, ecos]
  have htail : 1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * (70 : ℕ) - t)) +
      1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * (70 : ℕ) + t)) ≤ c.tail := by
    have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
    simp only [Cell.tail]
    push_cast
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at h1 h2
      exact tail_le hL_pos hL_le ha' h1 h2 hb70'
    · rw [abs_of_nonpos ht] at h1 h2
      have := tail_le hL_pos hL_le ha' h1 h2 hb70'
      rw [show (2 * Real.pi / (4 / 3) * 70 - t) = 2 * Real.pi / (4 / 3) * 70 + -t by ring,
        show (2 * Real.pi / (4 / 3) * 70 + t) = 2 * Real.pi / (4 / 3) * 70 - -t by ring, add_comm]
      exact this
  have htail0 : 0 ≤ 1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * (70 : ℕ) - t)) +
      1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * (70 : ℕ) + t)) := by
    have hh := hL_pos.trans_le hL_le
    have := abs_lt.mp hht
    push_cast at this ⊢
    have p1 : 0 < 2 * Real.pi / (4 / 3) * 70 - t := by linarith
    have p2 : 0 < 2 * Real.pi / (4 / 3) * 70 + t := by linarith
    positivity
  have hcos1 := Real.cos_le_one (|t| * (4 / 3))
  refine hT.trans ?_
  rw [enorm]
  simp only [Cell.Aup]
  push_cast
  have : (2 - 2 * Real.cos (|t| * (4 / 3))) / (4 / 3) ≤ (2 - 2 * (c.cl : ℝ)) * (3 / 4) := by
    rw [div_eq_mul_inv]; norm_num; linarith
  calc (2 - 2 * Real.cos (|t| * (4 / 3))) / (4 / 3) * _ ≤ (2 - 2 * (c.cl : ℝ)) * (3 / 4) * _ :=
        mul_le_mul_of_nonneg_right this htail0
    _ ≤ (2 - 2 * (c.cl : ℝ)) * (3 / 4) * c.tail := by
        refine mul_le_mul_of_nonneg_left htail ?_
        have := hc.trans hcos1
        nlinarith

/-! ### Moment tails and the exact pairings -/

theorem h43 : (0 : ℝ) < 4 / 3 := by norm_num

theorem le_of_sq_le' {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  by_contra hc
  have := not_le.mp hc
  nlinarith

theorem utail_le {e el : ℝ} (he : (e - 1) ^ 2 ≤ el) :
    (e - 1) ^ 2 / (4 / 3) * (1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * ((70 : ℕ) : ℝ) - 0)) +
      1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * ((70 : ℕ) : ℝ) + 0))) ≤
      el * (3 / 4) * (2 / (hL * (hL * 70))) := by
  have hl := hL_pos
  have hh := hL_le
  have h1 : 1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * 70)) ≤ 1 / (hL * (hL * 70)) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hel : 0 ≤ el := (sq_nonneg _).trans he
  push_cast
  simp only [sub_zero, add_zero]
  have h2 : 0 ≤ 1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * 70)) := by positivity
  calc (e - 1) ^ 2 / (4 / 3) * (1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * 70)) +
        1 / (2 * Real.pi / (4 / 3) * (2 * Real.pi / (4 / 3) * 70)))
      ≤ el / (4 / 3) * (1 / (hL * (hL * 70)) + 1 / (hL * (hL * 70))) := by gcongr
    _ = _ := by ring

def tbOf (s : Fin 2) : ℚ := if s = 0 then tb0 else tb1
def rhoOf (k : Consts) (s : Fin 2) : ℚ := if s = 0 then k.rho0 else k.rho1

theorem tau_le (s : Fin 2) : ∫ x, ‖du h43 70 s x‖ ^ 2 ≤ tbOf s := by
  have h := uS_tail h43 (σ := sig s) (sig_ne_zero s) (N := 70) (by norm_num)
  have hx := x_mem
  have hy := y_mem
  have hx1 := x_lt_one
  have hy1 := one_lt_y
  refine h.trans ?_
  fin_cases s
  · have e : Real.exp (sig 0 * (4 / 3)) = Real.exp (-2 / 3) := by norm_num [sig]
    simp only [Fin.zero_eta, Fin.isValue] at e ⊢
    rw [e]
    have hsq : (Real.exp (-2 / 3) - 1) ^ 2 ≤ (1 - (xL : ℝ)) ^ 2 := by nlinarith
    refine (utail_le hsq).trans ?_
    simp only [tbOf, tb0]
    refine le_trans (le_of_eq ?_) (le_rup _)
    push_cast; ring
  · have e : Real.exp (sig 1 * (4 / 3)) = Real.exp (2 / 3) := by norm_num [sig]
    simp only [Fin.mk_one, Fin.isValue] at e ⊢
    rw [e]
    have hsq : (Real.exp (2 / 3) - 1) ^ 2 ≤ ((yH : ℝ) - 1) ^ 2 := by nlinarith
    refine (utail_le hsq).trans ?_
    simp only [tbOf, Fin.one_eq_zero_iff, tb1]
    refine le_trans (le_of_eq ?_) (le_rup _)
    push_cast; ring

theorem tau_nonneg (s : Fin 2) : 0 ≤ ∫ x, ‖du h43 70 s x‖ ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

theorem const_facts {k : Consts} (hk : constOk k = true) :
    0 ≤ k.rho0 ∧ 0 ≤ k.rho1 ∧ tb0 ≤ k.rho0 ^ 2 ∧ tb1 ≤ k.rho1 ^ 2 ∧ 0 < k.Den := by
  simp only [constOk, Bool.and_eq_true, decide_eq_true_eq] at hk
  tauto

theorem rho_nonneg {k : Consts} (hk : constOk k = true) (s : Fin 2) : (0 : ℝ) ≤ rhoOf k s := by
  have := const_facts hk
  fin_cases s <;> simp [rhoOf] <;> exact_mod_cast (by tauto)

theorem tau_le_rho {k : Consts} (hk : constOk k = true) (s : Fin 2) :
    ∫ x, ‖du h43 70 s x‖ ^ 2 ≤ (rhoOf k s : ℝ) ^ 2 := by
  have := const_facts hk
  refine (tau_le s).trans ?_
  fin_cases s
  · simp only [tbOf, rhoOf, Fin.zero_eta, Fin.isValue]; exact_mod_cast this.2.2.1
  · simp only [tbOf, rhoOf, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff]
    exact_mod_cast this.2.2.2.1

theorem Eg_le {k : Consts} (hk : constOk k = true) (s r : Fin 2) :
    ‖Eg h43 70 s r‖ ≤ (rhoOf k r : ℝ) * rhoOf k s := by
  have h := Eg_sq_le h43 70 s r
  have hr := tau_le_rho hk r
  have hs := tau_le_rho hk s
  have h0 := rho_nonneg hk r
  have h1 := rho_nonneg hk s
  refine le_of_sq_le' (mul_nonneg h0 h1) (h.trans ?_)
  rw [mul_pow]
  exact mul_le_mul hr hs (tau_nonneg s) (sq_nonneg _)

theorem Ys_le (t : ℝ) (s : Fin 2) : ‖Ys (LT := 4 / 3) t s‖ ≤ 2 * (Real.exp (sig s * (4 / 3)) + 1) := by
  rw [Ys_eq h43, norm_div]
  have hnum : ‖cexp (((t : ℂ) * I + sig s) * ((4 / 3 : ℝ) : ℂ)) - 1‖ ≤ Real.exp (sig s * (4 / 3)) + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, norm_one]
    simp
  have hden : (1 / 2 : ℝ) ≤ ‖(t : ℂ) * I + sig s‖ := by
    have := Complex.abs_re_le_norm ((t : ℂ) * I + sig s)
    have hre : ((t : ℂ) * I + sig s).re = sig s := by simp
    rw [hre] at this
    fin_cases s <;> norm_num [sig] at this ⊢ <;> linarith
  have hpos : 0 ≤ Real.exp (sig s * (4 / 3)) + 1 := by positivity
  calc ‖cexp (((t : ℂ) * I + sig s) * ((4 / 3 : ℝ) : ℂ)) - 1‖ / ‖(t : ℂ) * I + sig s‖
      ≤ (Real.exp (sig s * (4 / 3)) + 1) / (1 / 2) :=
        div_le_div₀ hpos hnum (by norm_num) hden
    _ = _ := by ring

theorem Yb_le (t : ℝ) (s : Fin 2) : ‖Ys (LT := 4 / 3) t s‖ ≤ (if s = 0 then (Yb0 : ℝ) else Yb1) := by
  refine (Ys_le t s).trans ?_
  have hx := x_mem
  have hy := y_mem
  fin_cases s
  · simp only [Fin.zero_eta, Fin.isValue, Yb0]
    have e : Real.exp (sig 0 * (4 / 3)) = Real.exp (-2 / 3) := by norm_num [sig]
    rw [e]; push_cast; linarith
  · simp only [Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, Yb1]
    have e : Real.exp (sig 1 * (4 / 3)) = Real.exp (2 / 3) := by norm_num [sig]
    rw [e]; push_cast; linarith

theorem Gs00_eq : Gs (LT := 4 / 3) 0 0 = ((1 - Real.exp (-2 / 3) ^ 2 : ℝ) : ℂ) := by
  rw [Gs_00 h43, expm43]; push_cast; ring

theorem Gs11_eq : Gs (LT := 4 / 3) 1 1 = ((Real.exp (2 / 3) ^ 2 - 1 : ℝ) : ℂ) := by
  rw [Gs_11 h43, exp43]; push_cast; ring

theorem nG00_le : ‖Gs (LT := 4 / 3) 0 0‖ ≤ nG00 := by
  rw [Gs00_eq, Complex.norm_real, Real.norm_eq_abs]
  have hx := x_mem; have hx1 := x_lt_one; have hx0 := Real.exp_pos (-2 / 3); have hl := xL_pos
  simp only [nG00]; push_cast
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

theorem nG11_le : ‖Gs (LT := 4 / 3) 1 1‖ ≤ nG11 := by
  rw [Gs11_eq, Complex.norm_real, Real.norm_eq_abs]
  have hy := y_mem; have hy1 := one_lt_y
  simp only [nG11]; push_cast
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

theorem nG01_le : ‖Gs (LT := 4 / 3) 0 1‖ ≤ 4 / 3 := by
  rw [Gs_01 h43, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h43]

theorem nG10_le : ‖Gs (LT := 4 / 3) 1 0‖ ≤ 4 / 3 := by
  rw [Gs_10 h43, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h43]

theorem D_le : (Dlo : ℝ) ≤
    ‖Gs (LT := 4 / 3) 0 0 * Gs (LT := 4 / 3) 1 1 - Gs (LT := 4 / 3) 0 1 * Gs (LT := 4 / 3) 1 0‖ := by
  rw [Gs00_eq, Gs11_eq, Gs_01 h43, Gs_10 h43]
  have hx := x_mem; have hy := y_mem; have hxy := xy_one; have hl := xL_pos
  have hyl : (0 : ℝ) < yL := by norm_num [yL, e23Hi]
  have e : ((1 - Real.exp (-2 / 3) ^ 2 : ℝ) : ℂ) * ((Real.exp (2 / 3) ^ 2 - 1 : ℝ) : ℂ) -
      ((4 / 3 : ℝ) : ℂ) * ((4 / 3 : ℝ) : ℂ) =
      ((Real.exp (-2 / 3) ^ 2 + Real.exp (2 / 3) ^ 2 - 2 - 16 / 9 : ℝ) : ℂ) := by
    have : (1 - Real.exp (-2 / 3) ^ 2) * (Real.exp (2 / 3) ^ 2 - 1) - 4 / 3 * (4 / 3) =
        Real.exp (-2 / 3) ^ 2 + Real.exp (2 / 3) ^ 2 - 2 - 16 / 9 := by
      linear_combination (-(Real.exp (-2 / 3) * Real.exp (2 / 3)) - 1) * hxy
    rw [← this]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  simp only [Dlo]; push_cast
  nlinarith

/-! ### The closed form of the Cramer numerators on a cell -/

theorem closed_le {u1l u1h u2l u2h v1l v1h v2l v2h : ℚ} {u1 u2 v1 v2 : ℝ}
    (h1 : (u1l : ℝ) ≤ u1 ∧ u1 ≤ u1h) (h2 : (u2l : ℝ) ≤ u2 ∧ u2 ≤ u2h)
    (h3 : (v1l : ℝ) ≤ v1 ∧ v1 ≤ v1h) (h4 : (v2l : ℝ) ≤ v2 ∧ v2 ≤ v2h)
    {c : Cell} {τ cs sn : ℝ} (ha0 : 0 ≤ (c.a : ℝ)) (ha : (c.a : ℝ) ≤ τ) (hb : τ ≤ c.b)
    (hc1 : (c.cl : ℝ) ≤ cs) (hc2 : cs ≤ c.ch) (hs1 : (c.sl : ℝ) ≤ sn) (hs2 : sn ≤ c.sh) :
    u1 ^ 2 + v1 ^ 2 + (u2 ^ 2 + v2 ^ 2) * τ ^ 2 - 2 * cs * (u1 * v1 + u2 * v2 * τ ^ 2) +
      2 * sn * (τ * (u2 * v1 - u1 * v2)) ≤ c.Pup (mkNC u1l u1h u2l u2h v1l v1h v2l v2h) := by
  have p0 : u1 ^ 2 + v1 ^ 2 ≤ ((mkNC u1l u1h u2l u2h v1l v1h v2l v2h).p0 : ℝ) := by
    have a := sq_le_of_mem h1.1 h1.2
    have b := sq_le_of_mem h3.1 h3.2
    have r := le_rup (mhi u1l u1h u1l u1h + mhi v1l v1h v1l v1h)
    rw [Rat.cast_add] at r
    simp only [mkNC]
    rw [sq, sq]
    linarith
  have p2 : u2 ^ 2 + v2 ^ 2 ≤ ((mkNC u1l u1h u2l u2h v1l v1h v2l v2h).p2 : ℝ) := by
    have a := sq_le_of_mem h2.1 h2.2
    have b := sq_le_of_mem h4.1 h4.2
    have r := le_rup (mhi u2l u2h u2l u2h + mhi v2l v2h v2l v2h)
    rw [Rat.cast_add] at r
    simp only [mkNC]
    rw [sq, sq]
    linarith
  set k := mkNC u1l u1h u2l u2h v1l v1h v2l v2h with hk
  have hτ0 : 0 ≤ τ := ha0.trans ha
  have tq : (((c.a ^ 2 : ℚ)) : ℝ) ≤ τ ^ 2 ∧ τ ^ 2 ≤ ((c.b ^ 2 : ℚ) : ℝ) := by
    push_cast
    constructor <;> nlinarith
  have p2b : (u2 ^ 2 + v2 ^ 2) * τ ^ 2 ≤ (k.p2 : ℝ) * ((c.b ^ 2 : ℚ) : ℝ) :=
    mul_le_mul p2 tq.2 (sq_nonneg _) ((add_nonneg (sq_nonneg _) (sq_nonneg _)).trans p2)
  have q0 : (k.q0l : ℝ) ≤ u1 * v1 ∧ u1 * v1 ≤ k.q0h := by
    have m := mul_mem h1.1 h1.2 h3.1 h3.2
    simp only [k, mkNC]
    exact ⟨(rdn_le _).trans m.1, m.2.trans (le_rup _)⟩
  have q2 : (k.q2l : ℝ) ≤ u2 * v2 ∧ u2 * v2 ≤ k.q2h := by
    have m := mul_mem h2.1 h2.2 h4.1 h4.2
    simp only [k, mkNC]
    exact ⟨(rdn_le _).trans m.1, m.2.trans (le_rup _)⟩
  have qq := mul_mem q2.1 q2.2 tq.1 tq.2
  have hQ1 : (((-2 * (k.q0h + mhi k.q2l k.q2h (c.a ^ 2) (c.b ^ 2)) : ℚ)) : ℝ) ≤
      -2 * (u1 * v1 + u2 * v2 * τ ^ 2) := by
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_neg, Rat.cast_ofNat]
    linarith [q0.2, qq.2]
  have hQ2 : -2 * (u1 * v1 + u2 * v2 * τ ^ 2) ≤
      (((-2 * (k.q0l + mlo k.q2l k.q2h (c.a ^ 2) (c.b ^ 2)) : ℚ)) : ℝ) := by
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_neg, Rat.cast_ofNat]
    linarith [q0.1, qq.1]
  have hQc := (mul_mem hQ1 hQ2 hc1 hc2).2
  have r1 := mul_mem h2.1 h2.2 h3.1 h3.2
  have r2 := mul_mem h1.1 h1.2 h4.1 h4.2
  have hR : (k.rl : ℝ) ≤ u2 * v1 - u1 * v2 ∧ u2 * v1 - u1 * v2 ≤ k.rh := by
    simp only [k, mkNC]
    constructor
    · refine (rdn_le _).trans ?_
      rw [Rat.cast_sub]
      linarith [r1.1, r2.2]
    · refine le_trans ?_ (le_rup _)
      rw [Rat.cast_sub]
      linarith [r1.2, r2.1]
  have hRt := mul_mem hR.1 hR.2 ha hb
  have h2R1 : (((2 * mlo k.rl k.rh c.a c.b : ℚ)) : ℝ) ≤ 2 * ((u2 * v1 - u1 * v2) * τ) := by
    simp only [Rat.cast_mul, Rat.cast_ofNat]
    linarith [hRt.1]
  have h2R2 : 2 * ((u2 * v1 - u1 * v2) * τ) ≤ (((2 * mhi k.rl k.rh c.a c.b : ℚ)) : ℝ) := by
    simp only [Rat.cast_mul, Rat.cast_ofNat]
    linarith [hRt.2]
  have hRs := (mul_mem h2R1 h2R2 hs1 hs2).2
  have e : u1 ^ 2 + v1 ^ 2 + (u2 ^ 2 + v2 ^ 2) * τ ^ 2 - 2 * cs * (u1 * v1 + u2 * v2 * τ ^ 2) +
      2 * sn * (τ * (u2 * v1 - u1 * v2)) =
      (u1 ^ 2 + v1 ^ 2) + (u2 ^ 2 + v2 ^ 2) * τ ^ 2 + -2 * (u1 * v1 + u2 * v2 * τ ^ 2) * cs +
        2 * ((u2 * v1 - u1 * v2) * τ) * sn := by ring
  rw [e]
  simp only [Cell.Pup, Rat.cast_add, Rat.cast_mul]
  linarith [p0, p2b, hQc, hRs]

theorem sin_abs_mul (t R : ℝ) :
    2 * Real.sin (t * (4 / 3)) * (t * R) = 2 * Real.sin (|t| * (4 / 3)) * (|t| * R) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_mul, Real.sin_neg]; ring

theorem cos_abs_mul (t : ℝ) : Real.cos (t * (4 / 3)) = Real.cos (|t| * (4 / 3)) := by
  rw [← Real.cos_abs (t * (4 / 3)), abs_mul, abs_of_pos h43]

theorem Ys0_form (t : ℝ) : Ys (LT := 4 / 3) t 0 =
    (cexp (((t : ℂ) * I - 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I - 1 / 2) := by
  have e : ((sig 0 : ℝ) : ℂ) = -(1 / 2) := by norm_num [sig]
  rw [Ys_eq h43, e, ← sub_eq_add_neg]

theorem Ys1_form (t : ℝ) : Ys (LT := 4 / 3) t 1 =
    (cexp (((t : ℂ) * I + 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I + 1 / 2) := by
  have e : ((sig 1 : ℝ) : ℂ) = 1 / 2 := by norm_num [sig]
  rw [Ys_eq h43, e]

/-- From the closed form and the cell check to a norm bound. -/
theorem num_le {cA cB u1 u2 v1 v2 : ℝ} (hu1 : u1 = (cA * Real.exp (-(4 / 3) / 2) - cB * Real.exp ((4 / 3) / 2)) / 2)
    (hu2 : u2 = cA * Real.exp (-(4 / 3) / 2) + cB * Real.exp ((4 / 3) / 2))
    (hv1 : v1 = (cA - cB) / 2) (hv2 : v2 = cA + cB) {c : Cell} {n : ℚ} {P : ℝ} (hn : 0 ≤ n)
    (hP : P ≤ (n : ℝ) ^ 2 * ((c.a : ℝ) ^ 2 + 1 / 4) ^ 2) (ha0 : 0 ≤ (c.a : ℝ)) {t : ℝ}
    (h1 : (c.a : ℝ) ≤ |t|)
    (hcl : u1 ^ 2 + v1 ^ 2 + (u2 ^ 2 + v2 ^ 2) * |t| ^ 2 -
      2 * Real.cos (|t| * (4 / 3)) * (u1 * v1 + u2 * v2 * |t| ^ 2) +
        2 * Real.sin (|t| * (4 / 3)) * (|t| * (u2 * v1 - u1 * v2)) ≤ P) :
    ‖(cA : ℂ) * ((cexp (((t : ℂ) * I - 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I - 1 / 2)) +
        (cB : ℂ) * ((cexp (((t : ℂ) * I + 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I + 1 / 2))‖ ≤
      n := by
  have h := num_normSq (4 / 3) t cA cB u1 u2 v1 v2 hu1 hu2 hv1 hv2
  rw [cos_abs_mul, sin_abs_mul] at h
  rw [sq_abs] at hcl
  have hpos : 0 < (t ^ 2 + 1 / 4) ^ 2 := by positivity
  have hat : ((c.a : ℝ) ^ 2 + 1 / 4) ^ 2 ≤ (t ^ 2 + 1 / 4) ^ 2 := by
    have : (c.a : ℝ) ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; nlinarith
    gcongr
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_of_sq_le' hn' ?_
  have key : ‖(cA : ℂ) * ((cexp (((t : ℂ) * I - 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I - 1 / 2)) +
        (cB : ℂ) * ((cexp (((t : ℂ) * I + 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I + 1 / 2))‖ ^ 2 *
        (t ^ 2 + 1 / 4) ^ 2 ≤ (n : ℝ) ^ 2 * (t ^ 2 + 1 / 4) ^ 2 := by
    rw [h]
    exact hcl.trans (hP.trans (mul_le_mul_of_nonneg_left hat (sq_nonneg _)))
  exact le_of_mul_le_mul_right key hpos

/-! ### Soundness of one cell -/

theorem cellOk_facts {m : ℚ} {c : Cell} (hc : cellOk m c = true) :
    0 ≤ c.a ∧ c.a < c.b ∧ c.b < hL * 70 ∧ |thLo c.ul| ≤ 2 ∧ |thLo (c.ul + 1 / 2)| ≤ 2 ∧
      0 ≤ c.al ∧ c.Aup ≤ c.al ^ 2 ∧ 0 < c.eps ∧ 0 ≤ c.n0 ∧
      c.Pup nc0 ≤ c.n0 ^ 2 * (c.a ^ 2 + 1 / 4) ^ 2 ∧ 0 ≤ c.n1 ∧
      c.Pup nc1 ≤ c.n1 ^ 2 * (c.a ^ 2 + 1 / 4) ^ 2 ∧ 0 ≤ c.s ∧ logOk (aK ^ 2 + c.a ^ 2) = true ∧
      m + w2Hi + w3Hi - hpLo (c.a ^ 2) (c.a ^ 2) ≤ c.s := by
  simp only [cellOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  tauto

theorem N0_le {m : ℚ} {c : Cell} (hc : cellOk m c = true) {t : ℝ} (h1 : (c.a : ℝ) ≤ |t|)
    (h2 : |t| ≤ c.b) :
    ‖Gs (LT := 4 / 3) 1 1 * Ys (LT := 4 / 3) t 0 - Gs (LT := 4 / 3) 0 1 * Ys (LT := 4 / 3) t 1‖ ≤
      c.n0 := by
  obtain ⟨ha, -, -, hok0, hok1, -, -, -, hn0, hP0, -⟩ := cellOk_facts hc
  have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have hx := x_mem; have hy := y_mem; have hxy := xy_one
  have hyl : (0 : ℝ) < yL := by norm_num [yL, e23Hi]
  have tr := trig_mem ha hok0 hok1 h1 (le_trans h2 le_rfl)
  have e : Gs (LT := 4 / 3) 1 1 * Ys (LT := 4 / 3) t 0 - Gs (LT := 4 / 3) 0 1 * Ys (LT := 4 / 3) t 1 =
      ((Real.exp (2 / 3) ^ 2 - 1 : ℝ) : ℂ) *
          ((cexp (((t : ℂ) * I - 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I - 1 / 2)) +
        ((-(4 / 3) : ℝ) : ℂ) *
          ((cexp (((t : ℂ) * I + 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I + 1 / 2)) := by
    rw [Gs11_eq, Gs_01 h43, Ys0_form, Ys1_form]; push_cast; ring
  rw [e]
  have ex1 : Real.exp (-(4 / 3 : ℝ) / 2) = Real.exp (-2 / 3) := by norm_num
  have ex2 : Real.exp ((4 / 3 : ℝ) / 2) = Real.exp (2 / 3) := by norm_num
  refine num_le (u1 := (7 / 3 * Real.exp (2 / 3) - Real.exp (-2 / 3)) / 2)
    (u2 := -(1 / 3) * Real.exp (2 / 3) - Real.exp (-2 / 3)) (v1 := (Real.exp (2 / 3) ^ 2 + 1 / 3) / 2)
    (v2 := Real.exp (2 / 3) ^ 2 - 7 / 3)
    (by rw [ex1, ex2]; linear_combination (-(Real.exp (2 / 3)) / 2) * hxy)
    (by rw [ex1, ex2]; linear_combination (-(Real.exp (2 / 3))) * hxy) (by ring) (by ring) hn0
    (P := c.Pup nc0)
    (by have := (Rat.cast_le (K := ℝ)).mpr hP0; push_cast at this; exact this) ha' h1 ?_
  unfold nc0
  refine closed_le ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ha' h1 h2 tr.1 tr.2.1 tr.2.2.1 tr.2.2.2
  all_goals push_cast
  all_goals nlinarith

theorem N1_le {m : ℚ} {c : Cell} (hc : cellOk m c = true) {t : ℝ} (h1 : (c.a : ℝ) ≤ |t|)
    (h2 : |t| ≤ c.b) :
    ‖Gs (LT := 4 / 3) 0 0 * Ys (LT := 4 / 3) t 1 - Gs (LT := 4 / 3) 1 0 * Ys (LT := 4 / 3) t 0‖ ≤
      c.n1 := by
  obtain ⟨ha, -, -, hok0, hok1, -, -, -, -, -, hn1, hP1, -⟩ := cellOk_facts hc
  have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
  have hx := x_mem; have hy := y_mem; have hxy := xy_one
  have hxl := xL_pos
  have tr := trig_mem ha hok0 hok1 h1 (le_trans h2 le_rfl)
  have e : Gs (LT := 4 / 3) 0 0 * Ys (LT := 4 / 3) t 1 - Gs (LT := 4 / 3) 1 0 * Ys (LT := 4 / 3) t 0 =
      ((-(4 / 3) : ℝ) : ℂ) *
          ((cexp (((t : ℂ) * I - 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I - 1 / 2)) +
        ((1 - Real.exp (-2 / 3) ^ 2 : ℝ) : ℂ) *
          ((cexp (((t : ℂ) * I + 1 / 2) * ((4 / 3 : ℝ) : ℂ)) - 1) / ((t : ℂ) * I + 1 / 2)) := by
    rw [Gs00_eq, Gs_10 h43, Ys0_form, Ys1_form]; push_cast; ring
  rw [e]
  have ex1 : Real.exp (-(4 / 3 : ℝ) / 2) = Real.exp (-2 / 3) := by norm_num
  have ex2 : Real.exp ((4 / 3 : ℝ) / 2) = Real.exp (2 / 3) := by norm_num
  refine num_le (u1 := (-(1 / 3) * Real.exp (-2 / 3) - Real.exp (2 / 3)) / 2)
    (u2 := Real.exp (2 / 3) - 7 / 3 * Real.exp (-2 / 3)) (v1 := (Real.exp (-2 / 3) ^ 2 - 7 / 3) / 2)
    (v2 := -(1 / 3) - Real.exp (-2 / 3) ^ 2)
    (by rw [ex1, ex2]; linear_combination (-(Real.exp (-2 / 3)) / 2) * hxy)
    (by rw [ex1, ex2]; linear_combination (Real.exp (-2 / 3)) * hxy) (by ring) (by ring) hn1
    (P := c.Pup nc1)
    (by have := (Rat.cast_le (K := ℝ)).mpr hP1; push_cast at this; exact this) ha' h1 ?_
  unfold nc1
  refine closed_le ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ha' h1 h2 tr.1 tr.2.1 tr.2.2.1 tr.2.2.2
  all_goals push_cast
  all_goals nlinarith

/-- **One cell.** For `|t|` in the cell: `trialDist(t) ≤ TD` and `m − ScertM 3 t ≤ s`. -/
theorem cell_sound {m : ℚ} {k : Consts} (hk : constOk k = true) {c : Cell} (hc : cellOk m c = true)
    {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V) (hVc : ∀ i, Continuous (V i))
    {t : ℝ} (h1 : (c.a : ℝ) ≤ |t|) (h2 : |t| ≤ c.b) :
    trialDist 0 (4 / 3) V (cfC h43) t ≤ c.TD k ∧ (m : ℝ) - ScertM 3 t ≤ c.s := by
  obtain ⟨ha, -, hb70, hok0, hok1, hal, hA, heps, hn0, -, hn1, -, -, hlog, hsl⟩ := cellOk_facts hc
  obtain ⟨hr0, hr1, -, -, hDen⟩ := const_facts hk
  have hr0' : (0 : ℝ) ≤ k.rho0 := by exact_mod_cast hr0
  have hr1' : (0 : ℝ) ≤ k.rho1 := by exact_mod_cast hr1
  have hal' : (0 : ℝ) ≤ c.al := by exact_mod_cast hal
  constructor
  swap
  · -- the slack
    have ha' : (0 : ℝ) ≤ c.a := by exact_mod_cast ha
    have hq : ((c.a ^ 2 : ℚ) : ℝ) ≤ t ^ 2 := by push_cast; rw [← sq_abs t]; nlinarith
    have hh := hplus_ge_of_sq (q := c.a ^ 2) (by positivity) hlog hq
    have hS := scertM_three_ge t
    have hs := (Rat.cast_le (K := ℝ)).mpr hsl
    push_cast at hs
    linarith
  -- the trace
  have hAc := A_cell ha hb70 hok0 hok1 h1 h2
  have hAal : ∫ x, ‖dfT h43 70 t x‖ ^ 2 ≤ (c.al : ℝ) ^ 2 := by
    refine hAc.trans ?_
    have := (Rat.cast_le (K := ℝ)).mpr hA
    push_cast at this
    exact this
  have hA0 : 0 ≤ ∫ x, ‖dfT h43 70 t x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hea : ∀ s : Fin 2, ‖ea h43 70 t s‖ ≤ (c.al : ℝ) * rhoOf k s := fun s => by
    have h := ea_sq_le h43 70 t s
    refine le_of_sq_le' (mul_nonneg hal' (rho_nonneg hk s)) (h.trans ?_)
    rw [mul_pow]
    exact mul_le_mul hAal (tau_le_rho hk s) (tau_nonneg s) (sq_nonneg _)
  have he0 : ‖ea h43 70 t 0‖ ≤ (c.al : ℝ) * k.rho0 := by simpa [rhoOf] using hea 0
  have he1 : ‖ea h43 70 t 1‖ ≤ (c.al : ℝ) * k.rho1 := by simpa [rhoOf] using hea 1
  have hE00 : ‖Eg h43 70 0 0‖ ≤ (k.rho0 : ℝ) * k.rho0 := by simpa [rhoOf] using Eg_le hk 0 0
  have hE01 : ‖Eg h43 70 0 1‖ ≤ (k.rho1 : ℝ) * k.rho0 := by simpa [rhoOf] using Eg_le hk 0 1
  have hE10 : ‖Eg h43 70 1 0‖ ≤ (k.rho0 : ℝ) * k.rho1 := by simpa [rhoOf] using Eg_le hk 1 0
  have hE11 : ‖Eg h43 70 1 1‖ ≤ (k.rho1 : ℝ) * k.rho1 := by simpa [rhoOf] using Eg_le hk 1 1
  have hY0 : ‖Ys (LT := 4 / 3) t 0‖ ≤ (Yb0 : ℝ) := by simpa using Yb_le t 0
  have hY1 : ‖Ys (LT := 4 / 3) t 1‖ ≤ (Yb1 : ℝ) := by simpa using Yb_le t 1
  have hDen' : (0 : ℝ) < Dlo - ((nG00 : ℝ) * (k.rho1 * k.rho1) + nG11 * (k.rho0 * k.rho0) +
      4 / 3 * (k.rho0 * k.rho1) + 4 / 3 * (k.rho1 * k.rho0) + k.rho0 * k.rho0 * (k.rho1 * k.rho1) +
      k.rho1 * k.rho0 * (k.rho0 * k.rho1)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hDen
    simp only [Consts.Den, Consts.dd, Consts.r00, Consts.r11, Consts.r01] at this
    push_cast at this
    linarith
  have hD := D_le
  have hdet : detG h43 70 ≠ 0 := by
    have hge := det_pert_ge nG00_le nG01_le nG10_le nG11_le hE00 hE01 hE10 hE11 hD
    intro h0
    have e : detG h43 70 = (Gs (LT := 4 / 3) 0 0 - Eg h43 70 0 0) * (Gs (LT := 4 / 3) 1 1 - Eg h43 70 1 1) -
        (Gs (LT := 4 / 3) 0 1 - Eg h43 70 0 1) * (Gs (LT := 4 / 3) 1 0 - Eg h43 70 1 0) := by
      simp only [detG, gram_eq]
    rw [e] at h0
    rw [h0, norm_zero] at hge
    linarith
  have hDd : (Dlo : ℝ) - ((nG00 : ℝ) * (k.rho1 * k.rho1) + nG11 * (k.rho0 * k.rho0) +
      4 / 3 * (k.rho0 * k.rho1) + 4 / 3 * (k.rho1 * k.rho0) + k.rho0 * k.rho0 * (k.rho1 * k.rho1) +
      k.rho1 * k.rho0 * (k.rho0 * k.rho1)) = ((k.Den : ℚ) : ℝ) := by
    simp only [Consts.Den, Consts.dd, Consts.r00, Consts.r11, Consts.r01]; push_cast; ring
  -- γ₀
  have hg0 : ‖gam h43 70 t 0‖ ≤ ((c.n0 : ℝ) + c.d0 k) / k.Den := by
    have e : gam h43 70 t 0 = ((Gs (LT := 4 / 3) 1 1 - Eg h43 70 1 1) * (Ys (LT := 4 / 3) t 0 - ea h43 70 t 0) -
        (Gs (LT := 4 / 3) 0 1 - Eg h43 70 0 1) * (Ys (LT := 4 / 3) t 1 - ea h43 70 t 1)) /
        ((Gs (LT := 4 / 3) 0 0 - Eg h43 70 0 0) * (Gs (LT := 4 / 3) 1 1 - Eg h43 70 1 1) -
          (Gs (LT := 4 / 3) 0 1 - Eg h43 70 0 1) * (Gs (LT := 4 / 3) 1 0 - Eg h43 70 1 0)) := by
      rw [gam_zero]; simp only [detG, gram_eq, rhs_eq]
    rw [e]
    have hc0 := cramer_pert nG00_le nG01_le nG10_le nG11_le hE00 hE01 hE10 hE11 hY0 hY1 he0 he1 hD
      hDen'
    have hn := N0_le hc h1 h2
    have hδ : (nG11 : ℝ) * (c.al * k.rho0) + k.rho1 * k.rho1 * Yb0 + k.rho1 * k.rho1 * (c.al * k.rho0) +
        4 / 3 * (c.al * k.rho1) + k.rho1 * k.rho0 * Yb1 + k.rho1 * k.rho0 * (c.al * k.rho1) =
        ((c.d0 k : ℚ) : ℝ) := by
      simp only [Cell.d0, Consts.r11, Consts.r01]; push_cast; ring
    rw [hδ, hDd] at hc0
    have hD0 : (0 : ℝ) < k.Den := by exact_mod_cast hDen
    exact hc0.trans (div_le_div_of_nonneg_right (by linarith) hD0.le)
  -- γ₁
  have hg1 : ‖gam h43 70 t 1‖ ≤ ((c.n1 : ℝ) + c.d1 k) / k.Den := by
    have e : gam h43 70 t 1 = ((Gs (LT := 4 / 3) 0 0 - Eg h43 70 0 0) * (Ys (LT := 4 / 3) t 1 - ea h43 70 t 1) -
        (Gs (LT := 4 / 3) 1 0 - Eg h43 70 1 0) * (Ys (LT := 4 / 3) t 0 - ea h43 70 t 0)) /
        ((Gs (LT := 4 / 3) 1 1 - Eg h43 70 1 1) * (Gs (LT := 4 / 3) 0 0 - Eg h43 70 0 0) -
          (Gs (LT := 4 / 3) 1 0 - Eg h43 70 1 0) * (Gs (LT := 4 / 3) 0 1 - Eg h43 70 0 1)) := by
      rw [gam_one]; simp only [detG, gram_eq, rhs_eq]; ring
    rw [e]
    have hD' : (Dlo : ℝ) ≤ ‖Gs (LT := 4 / 3) 1 1 * Gs (LT := 4 / 3) 0 0 -
        Gs (LT := 4 / 3) 1 0 * Gs (LT := 4 / 3) 0 1‖ := by
      rw [show Gs (LT := 4 / 3) 1 1 * Gs (LT := 4 / 3) 0 0 - Gs (LT := 4 / 3) 1 0 * Gs (LT := 4 / 3) 0 1 =
        Gs (LT := 4 / 3) 0 0 * Gs (LT := 4 / 3) 1 1 - Gs (LT := 4 / 3) 0 1 * Gs (LT := 4 / 3) 1 0 by ring]
      exact hD
    have hpos : (0 : ℝ) < Dlo - ((nG11 : ℝ) * (k.rho0 * k.rho0) + nG00 * (k.rho1 * k.rho1) +
        4 / 3 * (k.rho1 * k.rho0) + 4 / 3 * (k.rho0 * k.rho1) + k.rho1 * k.rho1 * (k.rho0 * k.rho0) +
        k.rho0 * k.rho1 * (k.rho1 * k.rho0)) := by
      have h := hDen'; ring_nf at h ⊢; linarith
    have hc1 := cramer_pert nG11_le nG10_le nG01_le nG00_le hE11 hE10 hE01 hE00 hY1 hY0 he1 he0 hD' hpos
    have hn := N1_le hc h1 h2
    have hδ : (nG00 : ℝ) * (c.al * k.rho1) + k.rho0 * k.rho0 * Yb1 + k.rho0 * k.rho0 * (c.al * k.rho1) +
        4 / 3 * (c.al * k.rho0) + k.rho0 * k.rho1 * Yb0 + k.rho0 * k.rho1 * (c.al * k.rho0) =
        ((c.d1 k : ℚ) : ℝ) := by
      simp only [Cell.d1, Consts.r00, Consts.r01]; push_cast; ring
    have hDd' : (Dlo : ℝ) - ((nG11 : ℝ) * (k.rho0 * k.rho0) + nG00 * (k.rho1 * k.rho1) +
        4 / 3 * (k.rho1 * k.rho0) + 4 / 3 * (k.rho0 * k.rho1) + k.rho1 * k.rho1 * (k.rho0 * k.rho0) +
        k.rho0 * k.rho1 * (k.rho1 * k.rho0)) = ((k.Den : ℚ) : ℝ) := by
      rw [← hDd]; ring
    rw [hδ, hDd'] at hc1
    have hD0 : (0 : ℝ) < k.Den := by exact_mod_cast hDen
    exact hc1.trans (div_le_div_of_nonneg_right (by linarith) hD0.le)
  -- assembling
  have hD0 : (0 : ℝ) < k.Den := by exact_mod_cast hDen
  have hG2 : ‖gam h43 70 t 0‖ ^ 2 + ‖gam h43 70 t 1‖ ^ 2 ≤ ((c.G2 k : ℚ) : ℝ) := by
    have p0 := pow_le_pow_left₀ (norm_nonneg _) hg0 2
    have p1 := pow_le_pow_left₀ (norm_nonneg _) hg1 2
    simp only [Cell.G2]
    push_cast
    rw [add_div, ← div_pow, ← div_pow]
    linarith
  have hG20 : (0 : ℝ) ≤ ((c.G2 k : ℚ) : ℝ) := (by positivity : (0 : ℝ) ≤ _).trans hG2
  have ht0 : ∫ x, ‖uS (4 / 3) (sig 0) x - trigPoly (4 / 3) (K 70) (q h43 0) x‖ ^ 2 ≤ (tb0 : ℝ) := by
    exact (tau_le 0).trans (by simp [tbOf])
  have ht1 : ∫ x, ‖uS (4 / 3) (sig 1) x - trigPoly (4 / 3) (K 70) (q h43 1) x‖ ^ 2 ≤ (tb1 : ℝ) := by
    exact (tau_le 1).trans (by simp [tbOf])
  have hτ0 : 0 ≤ (∫ x, ‖uS (4 / 3) (sig 0) x - trigPoly (4 / 3) (K 70) (q h43 0) x‖ ^ 2) +
      ∫ x, ‖uS (4 / 3) (sig 1) x - trigPoly (4 / 3) (K 70) (q h43 1) x‖ ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have heps' : (0 : ℝ) < c.eps := by exact_mod_cast heps
  have htd := trialDist_le h43 hdet hV hVc t heps'
  refine htd.trans ?_
  have hX : (1 + (c.eps : ℝ)) * (∫ x, ‖fT (4 / 3) t x - trigPoly (4 / 3) (K 70) (cT h43 t) x‖ ^ 2) +
      (1 + 1 / (c.eps : ℝ)) * ((‖gam h43 70 t 0‖ ^ 2 + ‖gam h43 70 t 1‖ ^ 2) *
        ((∫ x, ‖uS (4 / 3) (sig 0) x - trigPoly (4 / 3) (K 70) (q h43 0) x‖ ^ 2) +
          ∫ x, ‖uS (4 / 3) (sig 1) x - trigPoly (4 / 3) (K 70) (q h43 1) x‖ ^ 2)) ≤
      (1 + (c.eps : ℝ)) * c.Aup + (1 + 1 / (c.eps : ℝ)) * ((c.G2 k : ℚ) * ((tb0 : ℝ) + tb1)) := by
    refine add_le_add (mul_le_mul_of_nonneg_left hAc (by linarith)) ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul hG2 (add_le_add ht0 ht1) hτ0 hG20) (by positivity)
  refine hX.trans ?_
  simp only [Cell.TD]
  refine le_trans (le_of_eq ?_) (le_rup _)
  push_cast
  ring

end AEGIS.CvSTraceCellL43V1

#print axioms AEGIS.CvSTraceCellL43V1.e23_bounds
#print axioms AEGIS.CvSTraceCellL43V1.mul_mem
#print axioms AEGIS.CvSTraceCellL43V1.trig_mem
#print axioms AEGIS.CvSTraceCellL43V1.A_cell
#print axioms AEGIS.CvSTraceCellL43V1.tau_le
#print axioms AEGIS.CvSTraceCellL43V1.closed_le
#print axioms AEGIS.CvSTraceCellL43V1.N0_le
#print axioms AEGIS.CvSTraceCellL43V1.N1_le
#print axioms AEGIS.CvSTraceCellL43V1.cell_sound
