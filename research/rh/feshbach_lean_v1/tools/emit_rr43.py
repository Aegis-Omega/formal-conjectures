"""Emit the Lean data modules of the L = 4/3 relative row certificate from rr43_data.pkl and
cert43_64.pkl (output of gen_rr43.py and cert43.py). Untrusted: the kernel re-checks every table.
usage: python3 emit_rr43.py OUTDIR
"""
import pickle
import sys
import textwrap
from pathlib import Path

OUT = Path(sys.argv[1])
d = pickle.load(open('rr43_data.pkl', 'rb'))
c = pickle.load(open('cert43_64.pkl', 'rb'))

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


def lst(name, xs, typ='ℤ', doc=None):
    body = '\n'.join(textwrap.wrap('[' + ', '.join(str(x) for x in xs) + ']', 98, initial_indent='  ',
                                   subsequent_indent='   ', break_long_words=False))
    head = f'/-- {doc} -/\n' if doc else ''
    return f'{head}def {name} : List {typ} :=\n{body}\n'


def lst2(name, rows, doc=None):
    rs = ['\n'.join(textwrap.wrap('[' + ', '.join(str(x) for x in r) + ']', 98, initial_indent='  ',
                                  subsequent_indent='   ', break_long_words=False)) for r in rows]
    head = f'/-- {doc} -/\n' if doc else ''
    return f'{head}def {name} : List (List ℤ) := [\n' + ',\n'.join(rs) + ']\n'


data = LICENSE + '''import CvSTauR1PrimeL43V1
import CvSDiagL43V1

/-!
# Integer data of the relative row certificate at `L = 4/3`

Midpoints and radii of the kernel-checked boxes (`tLit`, `rtLit`: `2^49 τ̂_k`, `2^49 ρ_k` for
`τ_k`, `k ≤ 200`; `dLit`, `rdLit` for the diagonal `cvsEntry M (4/3) n n`, `n ≤ 70`), the
fixed-point tables of the outside rows (`SLit`, `TLit`: `Σ_{70<|m|≤200} 2^128 τ̂_m^j/(m-n)` and
`.../(m-n)²`, every term rounded by `Int./`), the harmonic numbers `hLit` at `2^-128`, the dyadic
vector `g1Lit ≈ 2^100/f_n` and the projected rows `VLit`. Every table is recomputed by the kernel
(`*_ok`); the data come from `tools/gen_rr43.py` (untrusted). Not RH.
-/

open AEGIS.CvSTauPrimeL43V1 (tauFLo tauFHi)
open AEGIS.CvSTauR1PrimeL43V1 (tauFLoExtra tauFHiExtra)
open AEGIS.CvSDiagL43V1 (diagLo diagHi)

namespace AEGIS.CvSRelRowDataL43V1

set_option maxRecDepth 100000
set_option Elab.async false

'''
data += lst('tLit', d['tLit'], doc='`2^49 τ̂_k = 2^48 (lo_k + hi_k)`, `k = 0, …, 200`.') + '\n'
data += lst('rtLit', d['rtLit'], doc='`2^48 (hi_k - lo_k)`.') + '\n'
data += lst('dLit', d['dLit'], doc='`2^48 (diagLo_n + diagHi_n)`, `n = 0, …, 70`.') + '\n'
data += lst('rdLit', d['rdLit'], doc='`2^48 (diagHi_n - diagLo_n)`.') + '\n'
data += '''/-- The box ends as functions of `k`. -/
def boxLo (k : ℕ) : ℚ := if k = 0 then 0 else if k ≤ 70 then tauFLo.getD (k - 1) 0 else
  tauFLoExtra.getD (k - 71) 0
def boxHi (k : ℕ) : ℚ := if k = 0 then 0 else if k ≤ 70 then tauFHi.getD (k - 1) 0 else
  tauFHiExtra.getD (k - 71) 0

theorem boxes_ok : ((List.range 201).all fun k =>
    decide (((tLit.getD k 0 : ℤ) : ℚ) = (boxLo k + boxHi k) * 2 ^ 48) &&
      decide (((rtLit.getD k 0 : ℤ) : ℚ) = (boxHi k - boxLo k) * 2 ^ 48)) &&
    ((List.range 71).all fun n =>
      decide (((dLit.getD n 0 : ℤ) : ℚ) = (diagLo.getD n 0 + diagHi.getD n 0) * 2 ^ 48) &&
        decide (((rdLit.getD n 0 : ℤ) : ℚ) = (diagHi.getD n 0 - diagLo.getD n 0) * 2 ^ 48)) = true := by
  decide +kernel

/-- `2^49 τ̂_k` for `k ∈ ℤ` (odd extension). -/
def tq (k : ℤ) : ℤ := if 0 ≤ k then tLit.getD k.toNat 0 else -tLit.getD (-k).toNat 0

/-- `2^49 D̂_n`. -/
def dq (n : ℤ) : ℤ := dLit.getD n.natAbs 0

/-- `round(π² 2^70)`. -/
def SI : ℤ := 11651972255721781414236

/-- `2^72 f̂_n` with `f̂_n = -(9/4)(SI/2^70) n² - 1/4 ≈ -(3πn/2)² - 1/4`. -/
def phi (n : ℤ) : ℤ := -(9 * SI * n * n + 2 ^ 70)

/-- The outside rows `70 < |m| ≤ 200`. -/
def HL : List ℤ :=
  ((List.range 130).map fun k => (k : ℤ) + 71) ++ (List.range 130).map fun k => -((k : ℤ) + 71)

/-- `2^128 τ̂_m^j`. -/
def pw (j : ℕ) (m : ℤ) : ℤ :=
  match j with
  | 0 => 2 ^ 128
  | 1 => tq m * 2 ^ 79
  | _ => tq m * tq m * 2 ^ 30

def Sraw (j : ℕ) (n : ℤ) : ℤ := (HL.map fun m => pw j m / (m - n)).sum
def Traw (j : ℕ) (n : ℤ) : ℤ := (HL.map fun m => pw j m / ((m - n) * (m - n))).sum

'''
data += lst2('SLit', d['S'], doc='`Sraw j n`, `j < 3`, `n = -70, …, 70`.') + '\n'
data += lst2('TLit', d['T'], doc='`Traw j n`.') + '\n'
data += '''def Sq (j : ℕ) (n : ℤ) : ℤ := (SLit.getD j []).getD (n + 70).toNat 0
def Tq (j : ℕ) (n : ℤ) : ℤ := (TLit.getD j []).getD (n + 70).toNat 0

'''
for nm in ['S', 'T']:
    for j in range(3):
        data += f'''theorem {nm}_ok{j} : (List.range 141).all (fun (i : ℕ) =>
    decide ({nm}q {j} ((i : ℤ) - 70) = {nm}raw {j} ((i : ℤ) - 70))) = true := by
  decide +kernel

'''
data += lst('hLit', d['hLit'], doc='`Σ_{k ≤ u} 2^128 / k`, `u = 0, …, 271`.') + '\n'
data += '''theorem h_ok : (hLit.getD 0 0 = 0) ∧ (List.range 271).all (fun k =>
    decide (hLit.getD (k + 1) 0 = hLit.getD k 0 + 2 ^ 128 / ((k : ℤ) + 1))) = true := by
  constructor
  · decide +kernel
  · decide +kernel

def hq (u : ℤ) : ℤ := hLit.getD u.toNat 0

'''
data += lst('g1Lit', d['g1'], doc='`2^172 / φ_m`, `m = -70, …, 70` (`g̃₁ = 2^100/f̂`).') + '\n'
data += '''def g1 (m : ℤ) : ℤ := g1Lit.getD (m + 70).toNat 0

theorem g_ok : (List.range 141).all (fun (i : ℕ) =>
    decide (g1 ((i : ℤ) - 70) = 2 ^ 172 / phi ((i : ℤ) - 70))) = true := by
  decide +kernel

/-- `g̃₁`, `g̃₂ = m g̃₁` at `2^-100`. -/
def gv (jj : ℕ) (m : ℤ) : ℤ := if jj = 0 then g1 m else m * g1 m

'''
consts = dict(Cq=d['Cq'], piq=d['piq'], LPq=d['LPq'], T1q=d['T1q'], T2q=d['T2q'], Kq=d['Kq'],
              G1q=d['Gam'][0], G2q=d['Gam'][1])
docs = dict(Cq='`Ĉ = Cq/2^64 ≈ 2/(3π²)`.', piq='`π̂ = piq/2^64`.',
            LPq='`LPq/2^64 ≥ (1 + 1/1000) (L/π)²`.', T1q='`T1q/2^64 ≥ (1 + 1/1000) (1 + ε) (L/π)²`.',
            T2q='`T2q/2^64 ≥ (1 + 1/1000) (1 + 1/ε) 13² (L/π)²`.', Kq="`K' = Kq/2^64`.",
            G1q='`γ₁ = G1q/2^64`.', G2q='`γ₂ = G2q/2^64`.')
for k, v in consts.items():
    data += f'/-- {docs[k]} -/\ndef {k} : ℤ := {v}\n'
data += '''
/-- `2^128 Ê`: the CvS matrix with midpoints, off the diagonal rounded (larger index first). -/
def Et (n m : ℤ) : ℤ :=
  if n = m then dq n * 2 ^ 79 else if m < n then Cq * (tq n - tq m) * 2 ^ 15 / (n - m)
  else Cq * (tq m - tq n) * 2 ^ 15 / (m - n)

def Kj (j : ℕ) (n m : ℤ) : ℤ :=
  if n = m then Tq j n else if m < n then (Sq j n - Sq j m) / (n - m) else (Sq j m - Sq j n) / (m - n)

/-- `2^128 K̂`, `K̂(n,n') = Σ_m (τ̂_m - τ̂_n)(τ̂_m - τ̂_n')/((m-n)(m-n'))`. -/
def Kt (n m : ℤ) : ℤ :=
  Kj 2 n m - (tq n + tq m) * Kj 1 n m / 2 ^ 49 + tq n * tq m * Kj 0 n m / 2 ^ 98

/-- `2^128 gramUp 200`. -/
def Gt (n m : ℤ) : ℤ :=
  if n = m then 2 ^ 129 / (401 - 2 * n) + 2 ^ 129 / (401 + 2 * n)
  else if m < n then (hq (200 - m) - hq (200 - n) + (hq (200 + n) - hq (200 + m))) / (n - m)
  else (hq (200 - n) - hq (200 - m) + (hq (200 + m) - hq (200 + n))) / (m - n)

/-- `2^128 Z`, the kernel of the check in the coefficients `â`. -/
def Zt (n m : ℤ) : ℤ :=
  52 * Et n m - LPq * Kt n m / 2 ^ 64 - T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 -
    T2q * Gt n m / 2 ^ 64 - if n = m then Kq * 2 ^ 64 else 0

def Vraw (jj : ℕ) (n : ℤ) : ℤ :=
  2 * piq * ((List.range 141).map fun (b : ℕ) => Et n ((b : ℤ) - 70) * gv jj ((b : ℤ) - 70)).sum / 2 ^ 154

'''
data += lst2('VLit', d['Vt'], doc='`Vraw jj n`, `jj < 2`, `n = -70, …, 70`.') + '\n'
data += '''def Vq (jj : ℕ) (n : ℤ) : ℤ := (VLit.getD jj []).getD (n + 70).toNat 0

theorem V_ok0 : (List.range 141).all (fun (i : ℕ) =>
    decide (Vq 0 ((i : ℤ) - 70) = Vraw 0 ((i : ℤ) - 70))) = true := by
  decide +kernel

theorem V_ok1 : (List.range 141).all (fun (i : ℕ) =>
    decide (Vq 1 ((i : ℤ) - 70) = Vraw 1 ((i : ℤ) - 70))) = true := by
  decide +kernel

end AEGIS.CvSRelRowDataL43V1
'''
names = ['boxes_ok'] + [f'{a}_ok{j}' for a in 'ST' for j in range(3)] + ['h_ok', 'g_ok', 'V_ok0', 'V_ok1']
data += '\n' + '\n'.join(f'#print axioms AEGIS.CvSRelRowDataL43V1.{x}' for x in names) + '\n'
(OUT / 'CvSRelRowDataL43V1.lean').write_text(data)
print('data', len(data) // 1024, 'KB')

cert = LICENSE + '''import CvSPackedGramV1

/-!
# The packed factor of the relative row check at `L = 4/3`

`certL` (`139 × 139`, entries of at most 33 bits) with `2^64 P̃ = certL certLᵀ + certEps·Id + E`
for the scaled check matrix `P̃ = D P D`, `D = diag(2^-certD_i)` (`CvSRelRowCheckL43V1`).
Untrusted output of `tools/gen_rr43.py`; the kernel checks it. Not RH.
-/

namespace AEGIS.CvSRelRowCertL43V1

'''
cert += lst('certD', c['dd'], typ='ℕ', doc='Scaling exponents `d_i ≥ 0`.') + '\n'
for i, r in enumerate(c['L']):
    cert += lst(f'certLRow{i}', r) + '\n'
cert += '/-- The packed lower factor at `2^32`. -/\ndef certL : List (List ℤ) :=\n' + '\n'.join(
    textwrap.wrap('[' + ', '.join(f'certLRow{i}' for i in range(len(c['L']))) + ']', 98,
                  initial_indent='  ', subsequent_indent='   ')) + '\n\n'
cert += f'''def certEps : ℤ := {c['eps']}
def certEta : ℤ := {c['eta']}
def certB : ℕ := {c['B']}
def certBase : ℕ := 2 ^ {c['K']}

end AEGIS.CvSRelRowCertL43V1
'''
(OUT / 'CvSRelRowCertL43V1.lean').write_text(cert)
print('cert', len(cert) // 1024, 'KB')
