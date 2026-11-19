"""Writes CvSTraceCertL118V1.lean (or, with --eval, a scratch file that #evals the chunk checks).
Layout: width 1/150 on [0, 4], 1/30 on [4, 20], 1/6 on [20, 100], 1/3 on [100, 315]; m = 33/20.
usage: python3 gen_cert118.py OUT.lean [--eval] [totals.json]
With --eval, compiling OUT.lean prints the chunk totals (times 10^5, rounded up) as its last #eval;
that list is cert118_totals.json. The bounds are re-checked by the kernel.
Untrusted: it only proposes data."""
import json
import sys

OUT = sys.argv[1]
EVAL = '--eval' in sys.argv
tot = json.load(open(sys.argv[-1])) if sys.argv[-1].endswith('.json') else None
segs = [('0', '1 / 150', 600, 50), ('4', '1 / 30', 480, 40), ('20', '1 / 6', 480, 40), ('100', '1 / 3', 645, 43)]
chunks = []
for lo, h, n, k in segs:
    for s in range(0, n, k):
        chunks.append((lo, h, s, min(k, n - s)))
N = len(chunks)
ncells = sum(c[3] for c in chunks)
TOP = 315
LICENSE = '''/-
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
'''
defs = '\n'.join(f'def ch{i} : List Cell := segR {lo} ({h}) {s} {n}' for i, (lo, h, s, n) in enumerate(chunks))
words = [f'ch{i} ++' for i in range(N - 1)] + [f'ch{N - 1}']
lines, cur = [], '  '
for w in words:
    if len(cur) + len(w) + 1 > 98:
        lines.append(cur.rstrip())
        cur = '    '
    cur += w + ' '
lines.append(cur.rstrip())
cat = '\n'.join(lines)
head = f'''{LICENSE}import CvSTraceIntegralL118V1

/-!
# The trace certificate at L = 11/8

{ncells} cells cover `|t| ∈ [0, {TOP})`: width `1/150` on `[0, 4]`, `1/30` on `[4, 20]`, `1/6` on
`[20, 100]` and `1/3` on `[100, {TOP}]`. `mkCell` fills in the data of a cell (square roots rounded
up, `s` from `hpLo`); every value is then re-checked by `cellOk`, so `mkCell` itself needs no proof.
All checks run in the kernel (`decide +kernel`, no `native_decide`), in {N} chunks.

`trace_premises_L118` gives, for every trace family `V` (the 139 atoms and the two exponentials),
the premises `hsm`, `hsB`, `hs0`, `hcert` (with `M = 3`, `m = 33/20`, no `H` and no `d`), `hR`,
`hT` and `hk` (with `κ = 58`) of the window theorem at `L = 11/8`, with `T = 7/2`.

Not RH.
-/

open MeasureTheory

noncomputable section

namespace AEGIS.CvSTraceCertL118V1

open AEGIS.CvSTraceCellL118V1 AEGIS.CvSTraceIntegralL118V1 AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1
open AEGIS.CvSDiagL12V1 AEGIS.CvSTraceDistV1 AEGIS.CvSTraceV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

def nsqrtAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if (x + n / x) / 2 < x then nsqrtAux n f ((x + n / x) / 2) else x

def nsqrt (n : ℕ) : ℕ := nsqrtAux n 256 n

/-- A rational near `√q` from above (only used to propose data; `cellOk` checks it). -/
def sqrtUp (q : ℚ) : ℚ := ((nsqrt (⌈q * 2 ^ 64⌉).toNat + 1 : ℕ) : ℚ) / 2 ^ 32

def m0 : ℚ := 33 / 20

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

{defs}

def cells : List Cell :=
{cat}

def Tq : ℚ := 7 / 2
'''
if EVAL:
    body = head.replace('noncomputable section\n', '') + '\n'
    body += f'#eval decide (constOk K0 = true)\n#eval chainOk 0 cells {TOP}\n#eval logOk (aK ^ 2 + {TOP} ^ 2)\n'
    body += f'#eval decide (m0 + w2Hi + w3Hi ≤ hpLo ({TOP} ^ 2) ({TOP} ^ 2))\n'
    body += '#eval (List.range ' + str(N) + ').map fun i => ((' + '[' + ', '.join(f'ch{i}' for i in range(N)) + '].getD i []).all (cellOk m0))\n'
    body += '#eval (List.range ' + str(N) + ').map fun i => ((total K0 (([' + ', '.join(f'ch{i}' for i in range(N)) + '].getD i [])) * 100000).ceil)\n'
    body += 'end AEGIS.CvSTraceCertL118V1\n'
    open(OUT, 'w').write(body)
    sys.exit()
bounds = [tot[i] for i in range(N)]
thm = '\n'.join(f'''theorem c{i}_ok : ch{i}.all (cellOk m0) = true ∧ total K0 ch{i} ≤ {b} / 100000 := by
  decide +kernel''' for i, b in enumerate(bounds))
apps = '\n'.join(f'  have a{i} := all_app a{i - 1} c{i}_ok.1' for i in range(1, N))
tots = '\n'.join(f'  have t{i} := total_app_le t{i - 1} c{i}_ok.2' for i in range(1, N))
body = head + f'''
set_option maxRecDepth 100000

theorem K0_ok : constOk K0 = true := by decide +kernel
theorem chain_ok : chainOk 0 cells {TOP} = true := by decide +kernel
theorem tail_log : logOk (aK ^ 2 + {TOP} ^ 2) = true := by decide +kernel
theorem tail_ok : m0 + w2Hi + w3Hi ≤ hpLo ({TOP} ^ 2) ({TOP} ^ 2) := by decide +kernel

{thm}

theorem all_app {{l1 l2 : List Cell}} (h1 : l1.all (cellOk m0) = true)
    (h2 : l2.all (cellOk m0) = true) : (l1 ++ l2).all (cellOk m0) = true := by
  rw [List.all_append, h1, h2]; rfl

theorem total_app_le {{l1 l2 : List Cell}} {{x y : ℚ}} (h1 : total K0 l1 ≤ x)
    (h2 : total K0 l2 ≤ y) : total K0 (l1 ++ l2) ≤ x + y := by
  rw [total_append]; exact add_le_add h1 h2

theorem all_ok : ∀ c ∈ cells, cellOk m0 c = true := by
  have a0 := c0_ok.1
{apps}
  have h : cells.all (cellOk m0) = true := a{N - 1}
  exact fun c hc => List.all_eq_true.mp h c hc

theorem total_le : total K0 cells ≤ Tq := by
  have t0 := c0_ok.2
{tots}
  refine le_trans t{N - 1} ?_
  norm_num [Tq]

/-- **The trace and Krein premises at L = 11/8** (`M = 3`, `m = 33/20`, `T = 7/2`, `κ = 58`), for
every trace family `V` of the 139 atoms and the two exponentials. -/
theorem trace_premises_L118 {{V : Fin 141 → ℝ → ℂ}} (hV : TraceFamily (11 / 8) V)
    (hVc : ∀ i, Continuous (V i)) :
    Measurable (sFun cells) ∧ (∀ t, |sFun cells t| ≤ (sMax cells : ℝ)) ∧ (∀ t, 0 ≤ sFun cells t) ∧
      (∀ t : ℝ, 0 ≤ Wt t * (ScertM 3 t - 33 / 20) + Wt t * sFun cells t) ∧
      Integrable (fun t => sFun cells t * trialDist 0 (11 / 8) V (cfC h118) t) ∧
      (∫ t, sFun cells t * trialDist 0 (11 / 8) V (cfC h118) t) ≤ (Tq : ℝ) ∧
      58 ≤ (2 * Real.pi) ^ 2 * (11 / 8 : ℝ) * (33 / 20 - (Tq : ℝ) / (2 * Real.pi)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := premises_of_cells K0_ok all_ok (by norm_num) chain_ok tail_log
    tail_ok total_le hV hVc
  refine ⟨h1, h2, h3, fun t => ?_, h5, h6, gap_of_T (by norm_num [Tq])⟩
  have := h4 t
  simpa [m0] using this

end AEGIS.CvSTraceCertL118V1

#print axioms AEGIS.CvSTraceCertL118V1.all_ok
#print axioms AEGIS.CvSTraceCertL118V1.total_le
#print axioms AEGIS.CvSTraceCertL118V1.trace_premises_L118
'''
open(OUT, 'w').write(body)
print(N, 'chunks', ncells, 'cells')
