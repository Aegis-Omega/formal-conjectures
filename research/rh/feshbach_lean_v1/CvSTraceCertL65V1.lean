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

import CvSTraceIntegralV1

/-!
# The trace certificate at L = 6/5 (CvS step K3e, part 5)

687 cells cover `|t| ∈ [0, 267)`: width `1/50` on `[0, 4]`, `1/10` on `[4, 20]`, `1/2` on
`[20, 100]` and `1` on `[100, 267]`. `mkCell` fills in the data of a cell (square roots rounded
up, `s` from `hpLo`); every value is then re-checked by `cellOk`, so `mkCell` itself needs no proof.
All checks run in the kernel (`decide +kernel`, no `native_decide`), in 16 chunks.

`trace_premises_L65` gives, for every trace family `V` (the 139 atoms and the two exponentials),
the premises `hsm`, `hsB`, `hs0`, `hcert` (with `M = 3`, `m = 3/2`, no `H` and no `d`), `hR`, `hT`
and `hk` of `window_of_actual_rows_moment`, with `T = 3625/1000`.

Not RH.
-/

open MeasureTheory

noncomputable section

namespace AEGIS.CvSTraceCertL65V1

open AEGIS.CvSTraceCellL65V1 AEGIS.CvSTraceIntegralV1 AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1
open AEGIS.CvSDiagL12V1 AEGIS.CvSTraceDistV1 AEGIS.CvSTraceV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

def nsqrtAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if (x + n / x) / 2 < x then nsqrtAux n f ((x + n / x) / 2) else x

def nsqrt (n : ℕ) : ℕ := nsqrtAux n 256 n

/-- A rational near `√q` from above (only used to propose data; `cellOk` checks it). -/
def sqrtUp (q : ℚ) : ℚ := ((nsqrt (⌈q * 2 ^ 64⌉).toNat + 1 : ℕ) : ℚ) / 2 ^ 32

def m0 : ℚ := 3 / 2

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

def ch0 : List Cell := segR 0 (1 / 50) 0 50
def ch1 : List Cell := segR 0 (1 / 50) 50 50
def ch2 : List Cell := segR 0 (1 / 50) 100 50
def ch3 : List Cell := segR 0 (1 / 50) 150 50
def ch4 : List Cell := segR 4 (1 / 10) 0 40
def ch5 : List Cell := segR 4 (1 / 10) 40 40
def ch6 : List Cell := segR 4 (1 / 10) 80 40
def ch7 : List Cell := segR 4 (1 / 10) 120 40
def ch8 : List Cell := segR 20 (1 / 2) 0 40
def ch9 : List Cell := segR 20 (1 / 2) 40 40
def ch10 : List Cell := segR 20 (1 / 2) 80 40
def ch11 : List Cell := segR 20 (1 / 2) 120 40
def ch12 : List Cell := segR 100 (1) 0 42
def ch13 : List Cell := segR 100 (1) 42 42
def ch14 : List Cell := segR 100 (1) 84 42
def ch15 : List Cell := segR 100 (1) 126 41

def cells : List Cell :=
  ch0 ++ ch1 ++ ch2 ++ ch3 ++ ch4 ++ ch5 ++ ch6 ++ ch7 ++ ch8 ++ ch9 ++ ch10 ++ ch11 ++ ch12 ++
    ch13 ++ ch14 ++ ch15

def Tq : ℚ := 3625 / 1000

set_option maxRecDepth 100000

theorem K0_ok : constOk K0 = true := by decide +kernel
theorem chain_ok : chainOk 0 cells 267 = true := by decide +kernel
theorem tail_log : logOk (aK ^ 2 + 267 ^ 2) = true := by decide +kernel
theorem tail_ok : m0 + w2Hi + w3Hi ≤ hpLo (267 ^ 2) (267 ^ 2) := by decide +kernel

theorem c0_ok : ch0.all (cellOk m0) = true ∧ total K0 ch0 ≤ 799 / 1000 := by
  decide +kernel
theorem c1_ok : ch1.all (cellOk m0) = true ∧ total K0 ch1 ≤ 172 / 1000 := by
  decide +kernel
theorem c2_ok : ch2.all (cellOk m0) = true ∧ total K0 ch2 ≤ 205 / 1000 := by
  decide +kernel
theorem c3_ok : ch3.all (cellOk m0) = true ∧ total K0 ch3 ≤ 186 / 1000 := by
  decide +kernel
theorem c4_ok : ch4.all (cellOk m0) = true ∧ total K0 ch4 ≤ 267 / 1000 := by
  decide +kernel
theorem c5_ok : ch5.all (cellOk m0) = true ∧ total K0 ch5 ≤ 128 / 1000 := by
  decide +kernel
theorem c6_ok : ch6.all (cellOk m0) = true ∧ total K0 ch6 ≤ 96 / 1000 := by
  decide +kernel
theorem c7_ok : ch7.all (cellOk m0) = true ∧ total K0 ch7 ≤ 82 / 1000 := by
  decide +kernel
theorem c8_ok : ch8.all (cellOk m0) = true ∧ total K0 ch8 ≤ 370 / 1000 := by
  decide +kernel
theorem c9_ok : ch9.all (cellOk m0) = true ∧ total K0 ch9 ≤ 242 / 1000 := by
  decide +kernel
theorem c10_ok : ch10.all (cellOk m0) = true ∧ total K0 ch10 ≤ 188 / 1000 := by
  decide +kernel
theorem c11_ok : ch11.all (cellOk m0) = true ∧ total K0 ch11 ≤ 155 / 1000 := by
  decide +kernel
theorem c12_ok : ch12.all (cellOk m0) = true ∧ total K0 ch12 ≤ 328 / 1000 := by
  decide +kernel
theorem c13_ok : ch13.all (cellOk m0) = true ∧ total K0 ch13 ≤ 221 / 1000 := by
  decide +kernel
theorem c14_ok : ch14.all (cellOk m0) = true ∧ total K0 ch14 ≤ 136 / 1000 := by
  decide +kernel
theorem c15_ok : ch15.all (cellOk m0) = true ∧ total K0 ch15 ≤ 50 / 1000 := by
  decide +kernel

theorem all_ok : ∀ c ∈ cells, cellOk m0 c = true := by
  have h : cells.all (cellOk m0) = true := by
    simp only [cells, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0_ok.1, c1_ok.1⟩, c2_ok.1⟩, c3_ok.1⟩, c4_ok.1⟩, c5_ok.1⟩, c6_ok.1⟩,
      c7_ok.1⟩, c8_ok.1⟩, c9_ok.1⟩, c10_ok.1⟩, c11_ok.1⟩, c12_ok.1⟩, c13_ok.1⟩, c14_ok.1⟩, c15_ok.1⟩
  exact fun c hc => List.all_eq_true.mp h c hc

theorem total_le : total K0 cells ≤ Tq := by
  simp only [cells, total_append]
  have := c0_ok.2; have := c1_ok.2; have := c2_ok.2; have := c3_ok.2; have := c4_ok.2
  have := c5_ok.2; have := c6_ok.2; have := c7_ok.2; have := c8_ok.2; have := c9_ok.2
  have := c10_ok.2; have := c11_ok.2; have := c12_ok.2; have := c13_ok.2; have := c14_ok.2
  have := c15_ok.2
  simp only [Tq]
  linarith

/-- **The trace and Krein premises at L = 6/5** (`M = 3`, `m = 3/2`, `T = 3625/1000`), for every
trace family `V` of the 139 atoms and the two exponentials. -/
theorem trace_premises_L65 {V : Fin 141 → ℝ → ℂ} (hV : TraceFamily (6 / 5) V)
    (hVc : ∀ i, Continuous (V i)) :
    Measurable (sFun cells) ∧ (∀ t, |sFun cells t| ≤ (sMax cells : ℝ)) ∧ (∀ t, 0 ≤ sFun cells t) ∧
      (∀ t : ℝ, 0 ≤ Wt t * (ScertM 3 t - 3 / 2) + Wt t * sFun cells t) ∧
      Integrable (fun t => sFun cells t * trialDist 0 (6 / 5) V (cfC h65) t) ∧
      (∫ t, sFun cells t * trialDist 0 (6 / 5) V (cfC h65) t) ≤ (Tq : ℝ) ∧
      40 ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) * (3 / 2 - (Tq : ℝ) / (2 * Real.pi)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := premises_of_cells K0_ok all_ok (by norm_num) chain_ok tail_log
    tail_ok total_le hV hVc
  refine ⟨h1, h2, h3, fun t => ?_, h5, h6, gap_of_T (by norm_num [Tq])⟩
  have := h4 t
  simpa [m0] using this

end AEGIS.CvSTraceCertL65V1

#print axioms AEGIS.CvSTraceCertL65V1.all_ok
#print axioms AEGIS.CvSTraceCertL65V1.total_le
#print axioms AEGIS.CvSTraceCertL65V1.trace_premises_L65
