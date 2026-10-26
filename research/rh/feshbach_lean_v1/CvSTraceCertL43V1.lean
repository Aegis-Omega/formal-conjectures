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

import CvSTraceIntegralL43V1

/-!
# The trace certificate at L = 4/3

1430 cells cover `|t| ∈ [0, 295)`: width `1/100` on `[0, 4]`, `1/20` on `[4, 20]`, `1/4` on
`[20, 100]` and `1/2` on `[100, 295]`. `mkCell` fills in the data of a cell (square roots rounded
up, `s` from `hpLo`); every value is then re-checked by `cellOk`, so `mkCell` itself needs no proof.
All checks run in the kernel (`decide +kernel`, no `native_decide`), in 34 chunks.

`trace_premises_L43` gives, for every trace family `V` (the 139 atoms and the two exponentials),
the premises `hsm`, `hsB`, `hs0`, `hcert` (with `M = 3`, `m = 8/5`, no `H` and no `d`), `hR`, `hT`
and `hk` (with `κ = 44`) of the window theorem at `L = 4/3`, with `T = 7/2`.

Not RH.
-/

open MeasureTheory

noncomputable section

namespace AEGIS.CvSTraceCertL43V1

open AEGIS.CvSTraceCellL43V1 AEGIS.CvSTraceIntegralL43V1 AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1
open AEGIS.CvSDiagL12V1 AEGIS.CvSTraceDistV1 AEGIS.CvSTraceV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

def nsqrtAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if (x + n / x) / 2 < x then nsqrtAux n f ((x + n / x) / 2) else x

def nsqrt (n : ℕ) : ℕ := nsqrtAux n 256 n

/-- A rational near `√q` from above (only used to propose data; `cellOk` checks it). -/
def sqrtUp (q : ℚ) : ℚ := ((nsqrt (⌈q * 2 ^ 64⌉).toNat + 1 : ℕ) : ℚ) / 2 ^ 32

def m0 : ℚ := 8 / 5

def K0 : Consts := ⟨sqrtUp tb0, sqrtUp tb1⟩

def mkCell (a b : ℚ) : Cell :=
  let c0 : Cell := ⟨a, b, 0, 1, 0, 0, 0⟩
  let al := sqrtUp c0.Aup
  let n0 := sqrtUp (c0.Pup nc0) / (a ^ 2 + 1 / 4)
  let n1 := sqrtUp (c0.Pup nc1) / (a ^ 2 + 1 / 4)
  let c1 : Cell := ⟨a, b, 0, 1, al, n0, n1⟩
  let eps := sqrtUp (c1.G2 K0 * (tb0 + tb1) / c0.Aup) + 1 / 2 ^ 20
  ⟨a, b, rup (max 0 (m0 + w2Hi + w3Hi - hpLo (a ^ 2) (a ^ 2))), eps, al, n0, n1⟩

def segR (lo h : ℚ) (s n : ℕ) : List Cell :=
  (List.range' s n).map fun i => mkCell (lo + i * h) (lo + (i + 1) * h)

def ch0 : List Cell := segR 0 (1 / 100) 0 50
def ch1 : List Cell := segR 0 (1 / 100) 50 50
def ch2 : List Cell := segR 0 (1 / 100) 100 50
def ch3 : List Cell := segR 0 (1 / 100) 150 50
def ch4 : List Cell := segR 0 (1 / 100) 200 50
def ch5 : List Cell := segR 0 (1 / 100) 250 50
def ch6 : List Cell := segR 0 (1 / 100) 300 50
def ch7 : List Cell := segR 0 (1 / 100) 350 50
def ch8 : List Cell := segR 4 (1 / 20) 0 40
def ch9 : List Cell := segR 4 (1 / 20) 40 40
def ch10 : List Cell := segR 4 (1 / 20) 80 40
def ch11 : List Cell := segR 4 (1 / 20) 120 40
def ch12 : List Cell := segR 4 (1 / 20) 160 40
def ch13 : List Cell := segR 4 (1 / 20) 200 40
def ch14 : List Cell := segR 4 (1 / 20) 240 40
def ch15 : List Cell := segR 4 (1 / 20) 280 40
def ch16 : List Cell := segR 20 (1 / 4) 0 40
def ch17 : List Cell := segR 20 (1 / 4) 40 40
def ch18 : List Cell := segR 20 (1 / 4) 80 40
def ch19 : List Cell := segR 20 (1 / 4) 120 40
def ch20 : List Cell := segR 20 (1 / 4) 160 40
def ch21 : List Cell := segR 20 (1 / 4) 200 40
def ch22 : List Cell := segR 20 (1 / 4) 240 40
def ch23 : List Cell := segR 20 (1 / 4) 280 40
def ch24 : List Cell := segR 100 (1 / 2) 0 39
def ch25 : List Cell := segR 100 (1 / 2) 39 39
def ch26 : List Cell := segR 100 (1 / 2) 78 39
def ch27 : List Cell := segR 100 (1 / 2) 117 39
def ch28 : List Cell := segR 100 (1 / 2) 156 39
def ch29 : List Cell := segR 100 (1 / 2) 195 39
def ch30 : List Cell := segR 100 (1 / 2) 234 39
def ch31 : List Cell := segR 100 (1 / 2) 273 39
def ch32 : List Cell := segR 100 (1 / 2) 312 39
def ch33 : List Cell := segR 100 (1 / 2) 351 39

def cells : List Cell :=
  ch0 ++ ch1 ++ ch2 ++ ch3 ++ ch4 ++ ch5 ++ ch6 ++ ch7 ++ ch8 ++ ch9 ++
    ch10 ++ ch11 ++ ch12 ++ ch13 ++ ch14 ++ ch15 ++ ch16 ++ ch17 ++ ch18 ++ ch19 ++ ch20 ++
    ch21 ++ ch22 ++ ch23 ++ ch24 ++ ch25 ++ ch26 ++ ch27 ++ ch28 ++ ch29 ++ ch30 ++ ch31 ++
    ch32 ++ ch33

def Tq : ℚ := 7 / 2

set_option maxRecDepth 100000

theorem K0_ok : constOk K0 = true := by decide +kernel
theorem chain_ok : chainOk 0 cells 295 = true := by decide +kernel
theorem tail_log : logOk (aK ^ 2 + 295 ^ 2) = true := by decide +kernel
theorem tail_ok : m0 + w2Hi + w3Hi ≤ hpLo (295 ^ 2) (295 ^ 2) := by decide +kernel

theorem c0_ok : ch0.all (cellOk m0) = true ∧ total K0 ch0 ≤ 301 / 1000 := by
  decide +kernel
theorem c1_ok : ch1.all (cellOk m0) = true ∧ total K0 ch1 ≤ 115 / 1000 := by
  decide +kernel
theorem c2_ok : ch2.all (cellOk m0) = true ∧ total K0 ch2 ≤ 87 / 1000 := by
  decide +kernel
theorem c3_ok : ch3.all (cellOk m0) = true ∧ total K0 ch3 ≤ 107 / 1000 := by
  decide +kernel
theorem c4_ok : ch4.all (cellOk m0) = true ∧ total K0 ch4 ≤ 124 / 1000 := by
  decide +kernel
theorem c5_ok : ch5.all (cellOk m0) = true ∧ total K0 ch5 ≤ 125 / 1000 := by
  decide +kernel
theorem c6_ok : ch6.all (cellOk m0) = true ∧ total K0 ch6 ≤ 109 / 1000 := by
  decide +kernel
theorem c7_ok : ch7.all (cellOk m0) = true ∧ total K0 ch7 ≤ 82 / 1000 := by
  decide +kernel
theorem c8_ok : ch8.all (cellOk m0) = true ∧ total K0 ch8 ≤ 144 / 1000 := by
  decide +kernel
theorem c9_ok : ch9.all (cellOk m0) = true ∧ total K0 ch9 ≤ 101 / 1000 := by
  decide +kernel
theorem c10_ok : ch10.all (cellOk m0) = true ∧ total K0 ch10 ≤ 64 / 1000 := by
  decide +kernel
theorem c11_ok : ch11.all (cellOk m0) = true ∧ total K0 ch11 ≤ 63 / 1000 := by
  decide +kernel
theorem c12_ok : ch12.all (cellOk m0) = true ∧ total K0 ch12 ≤ 54 / 1000 := by
  decide +kernel
theorem c13_ok : ch13.all (cellOk m0) = true ∧ total K0 ch13 ≤ 36 / 1000 := by
  decide +kernel
theorem c14_ok : ch14.all (cellOk m0) = true ∧ total K0 ch14 ≤ 53 / 1000 := by
  decide +kernel
theorem c15_ok : ch15.all (cellOk m0) = true ∧ total K0 ch15 ≤ 21 / 1000 := by
  decide +kernel
theorem c16_ok : ch16.all (cellOk m0) = true ∧ total K0 ch16 ≤ 198 / 1000 := by
  decide +kernel
theorem c17_ok : ch17.all (cellOk m0) = true ∧ total K0 ch17 ≤ 157 / 1000 := by
  decide +kernel
theorem c18_ok : ch18.all (cellOk m0) = true ∧ total K0 ch18 ≤ 132 / 1000 := by
  decide +kernel
theorem c19_ok : ch19.all (cellOk m0) = true ∧ total K0 ch19 ≤ 113 / 1000 := by
  decide +kernel
theorem c20_ok : ch20.all (cellOk m0) = true ∧ total K0 ch20 ≤ 98 / 1000 := by
  decide +kernel
theorem c21_ok : ch21.all (cellOk m0) = true ∧ total K0 ch21 ≤ 86 / 1000 := by
  decide +kernel
theorem c22_ok : ch22.all (cellOk m0) = true ∧ total K0 ch22 ≤ 78 / 1000 := by
  decide +kernel
theorem c23_ok : ch23.all (cellOk m0) = true ∧ total K0 ch23 ≤ 72 / 1000 := by
  decide +kernel
theorem c24_ok : ch24.all (cellOk m0) = true ∧ total K0 ch24 ≤ 160 / 1000 := by
  decide +kernel
theorem c25_ok : ch25.all (cellOk m0) = true ∧ total K0 ch25 ≤ 140 / 1000 := by
  decide +kernel
theorem c26_ok : ch26.all (cellOk m0) = true ∧ total K0 ch26 ≤ 123 / 1000 := by
  decide +kernel
theorem c27_ok : ch27.all (cellOk m0) = true ∧ total K0 ch27 ≤ 106 / 1000 := by
  decide +kernel
theorem c28_ok : ch28.all (cellOk m0) = true ∧ total K0 ch28 ≤ 92 / 1000 := by
  decide +kernel
theorem c29_ok : ch29.all (cellOk m0) = true ∧ total K0 ch29 ≤ 79 / 1000 := by
  decide +kernel
theorem c30_ok : ch30.all (cellOk m0) = true ∧ total K0 ch30 ≤ 67 / 1000 := by
  decide +kernel
theorem c31_ok : ch31.all (cellOk m0) = true ∧ total K0 ch31 ≤ 55 / 1000 := by
  decide +kernel
theorem c32_ok : ch32.all (cellOk m0) = true ∧ total K0 ch32 ≤ 41 / 1000 := by
  decide +kernel
theorem c33_ok : ch33.all (cellOk m0) = true ∧ total K0 ch33 ≤ 18 / 1000 := by
  decide +kernel

theorem all_app {l1 l2 : List Cell} (h1 : l1.all (cellOk m0) = true)
    (h2 : l2.all (cellOk m0) = true) : (l1 ++ l2).all (cellOk m0) = true := by
  rw [List.all_append, h1, h2]; rfl

theorem total_app_le {l1 l2 : List Cell} {x y : ℚ} (h1 : total K0 l1 ≤ x)
    (h2 : total K0 l2 ≤ y) : total K0 (l1 ++ l2) ≤ x + y := by
  rw [total_append]; exact add_le_add h1 h2

theorem all_ok : ∀ c ∈ cells, cellOk m0 c = true := by
  have a0 := c0_ok.1
  have a1 := all_app a0 c1_ok.1
  have a2 := all_app a1 c2_ok.1
  have a3 := all_app a2 c3_ok.1
  have a4 := all_app a3 c4_ok.1
  have a5 := all_app a4 c5_ok.1
  have a6 := all_app a5 c6_ok.1
  have a7 := all_app a6 c7_ok.1
  have a8 := all_app a7 c8_ok.1
  have a9 := all_app a8 c9_ok.1
  have a10 := all_app a9 c10_ok.1
  have a11 := all_app a10 c11_ok.1
  have a12 := all_app a11 c12_ok.1
  have a13 := all_app a12 c13_ok.1
  have a14 := all_app a13 c14_ok.1
  have a15 := all_app a14 c15_ok.1
  have a16 := all_app a15 c16_ok.1
  have a17 := all_app a16 c17_ok.1
  have a18 := all_app a17 c18_ok.1
  have a19 := all_app a18 c19_ok.1
  have a20 := all_app a19 c20_ok.1
  have a21 := all_app a20 c21_ok.1
  have a22 := all_app a21 c22_ok.1
  have a23 := all_app a22 c23_ok.1
  have a24 := all_app a23 c24_ok.1
  have a25 := all_app a24 c25_ok.1
  have a26 := all_app a25 c26_ok.1
  have a27 := all_app a26 c27_ok.1
  have a28 := all_app a27 c28_ok.1
  have a29 := all_app a28 c29_ok.1
  have a30 := all_app a29 c30_ok.1
  have a31 := all_app a30 c31_ok.1
  have a32 := all_app a31 c32_ok.1
  have a33 := all_app a32 c33_ok.1
  have h : cells.all (cellOk m0) = true := a33
  exact fun c hc => List.all_eq_true.mp h c hc

theorem total_le : total K0 cells ≤ Tq := by
  have t0 := c0_ok.2
  have t1 := total_app_le t0 c1_ok.2
  have t2 := total_app_le t1 c2_ok.2
  have t3 := total_app_le t2 c3_ok.2
  have t4 := total_app_le t3 c4_ok.2
  have t5 := total_app_le t4 c5_ok.2
  have t6 := total_app_le t5 c6_ok.2
  have t7 := total_app_le t6 c7_ok.2
  have t8 := total_app_le t7 c8_ok.2
  have t9 := total_app_le t8 c9_ok.2
  have t10 := total_app_le t9 c10_ok.2
  have t11 := total_app_le t10 c11_ok.2
  have t12 := total_app_le t11 c12_ok.2
  have t13 := total_app_le t12 c13_ok.2
  have t14 := total_app_le t13 c14_ok.2
  have t15 := total_app_le t14 c15_ok.2
  have t16 := total_app_le t15 c16_ok.2
  have t17 := total_app_le t16 c17_ok.2
  have t18 := total_app_le t17 c18_ok.2
  have t19 := total_app_le t18 c19_ok.2
  have t20 := total_app_le t19 c20_ok.2
  have t21 := total_app_le t20 c21_ok.2
  have t22 := total_app_le t21 c22_ok.2
  have t23 := total_app_le t22 c23_ok.2
  have t24 := total_app_le t23 c24_ok.2
  have t25 := total_app_le t24 c25_ok.2
  have t26 := total_app_le t25 c26_ok.2
  have t27 := total_app_le t26 c27_ok.2
  have t28 := total_app_le t27 c28_ok.2
  have t29 := total_app_le t28 c29_ok.2
  have t30 := total_app_le t29 c30_ok.2
  have t31 := total_app_le t30 c31_ok.2
  have t32 := total_app_le t31 c32_ok.2
  have t33 := total_app_le t32 c33_ok.2
  refine le_trans t33 ?_
  norm_num [Tq]

/-- **The trace and Krein premises at L = 4/3** (`M = 3`, `m = 8/5`, `T = 7/2`, `κ = 44`), for every
trace family `V` of the 139 atoms and the two exponentials. -/
theorem trace_premises_L43 {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (4 / 3) V)
    (hVc : ∀ i, Continuous (V i)) :
    Measurable (sFun cells) ∧ (∀ t, |sFun cells t| ≤ (sMax cells : ℝ)) ∧ (∀ t, 0 ≤ sFun cells t) ∧
      (∀ t : ℝ, 0 ≤ Wt t * (ScertM 3 t - 8 / 5) + Wt t * sFun cells t) ∧
      Integrable (fun t => sFun cells t * trialDist 0 (4 / 3) V (cfC h43) t) ∧
      (∫ t, sFun cells t * trialDist 0 (4 / 3) V (cfC h43) t) ≤ (Tq : ℝ) ∧
      44 ≤ (2 * Real.pi) ^ 2 * (4 / 3 : ℝ) * (8 / 5 - (Tq : ℝ) / (2 * Real.pi)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := premises_of_cells K0_ok all_ok (by norm_num) chain_ok tail_log
    tail_ok total_le hV hVc
  refine ⟨h1, h2, h3, fun t => ?_, h5, h6, gap_of_T (by norm_num [Tq])⟩
  have := h4 t
  simpa [m0] using this

end AEGIS.CvSTraceCertL43V1

#print axioms AEGIS.CvSTraceCertL43V1.all_ok
#print axioms AEGIS.CvSTraceCertL43V1.total_le
#print axioms AEGIS.CvSTraceCertL43V1.trace_premises_L43
