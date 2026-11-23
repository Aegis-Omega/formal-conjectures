"""Untrusted exact mirror of CvSTauFast2L85V1.tauF2 (L = 8/5, second-order tail): picks J, computes
the integer heads, the second-order tail box, the prime part and the outward-rounded tau box (2^48).
The kernel re-checks every box; this script only proposes them.
usage: gen_tau2_85.py K1 K2 [module]   (prints a summary; with 'module' writes the Lean data module)"""
import math, sys
from fractions import Fraction as F
from math import floor, ceil
import gen_tau85f as g

def atLo(x, K): return g.atP(x, 2 * K) if x < 1 else g.piLo / 2 - g.atP(1 / x, 2 * K + 1)
def atHi(x, K): return g.atP(x, 2 * K + 1) if x < 1 else g.piHi / 2 - g.atP(1 / x, 2 * K)
def dq(J): return g.cw(J) - 1
def src2(k, J, K):
    a, b = 10 * g.pLoN * k, 10 * g.pHiN * k
    d, ol, oh = dq(J), g.omLo(k), g.omHi(k)
    ah = atHi(oh / d, K)
    p2lo = atLo(ol / d, K) - d * oh / (3 * (d ** 2 + ol ** 2) ** 2)
    p2hi = ah - d * ol / (3 * (d ** 2 + oh ** 2) ** 2)
    eps = 5 * ah / (g.cw(J) ** 2 + ol ** 2) ** 2
    lo = F(g.hLo(a, b, J), g.S64) + p2lo - eps - 2 * g.Ehi(g.j0) * ah
    hi = F(g.hHi(a, b, J), g.S64) + p2hi + eps
    ok = (1 <= ol and g.j0 <= J and 2 <= g.cw(J) and ol / d != 1 and oh / d != 1 and 0 <= lo and 0 <= hi)
    return ok, lo, hi
def pickJ2(k, tgt):
    w = 5 * math.pi * k / 4
    c2 = max(0.0, math.sqrt(10 * math.pi / tgt) - w * w)
    J = max(g.j0, math.ceil((math.sqrt(c2) - 0.5) / 2))
    while 0.6 <= w / (2 * J - 0.5) <= 1 / 0.6:
        J += 1
    return J
def box2(k, tgt, K=20):
    J = pickJ2(k, tgt)
    ok, sl, sh = src2(k, J, K)
    assert ok, k
    assert all(abs(g.thLo(ul)) <= 2 for ul, _, _, _ in g.args(k))
    a, b = g.piLo * sl + g.primeLo(k), g.piHi * sh + g.primeHi(k)
    lo, hi = F(floor(a * g.S48), g.S48), F(ceil(b * g.S48), g.S48)
    assert lo <= a and b <= hi
    return J, lo, hi

if __name__ == '__main__':
    k1, k2 = int(sys.argv[1]), int(sys.argv[2])
    import mpmath as mp
    mp.mp.dps = 40
    rows = []
    for k in range(k1, k2 + 1):
        J, lo, hi = box2(k, g.tgt_of(k))
        w = 5 * mp.pi * k / 4; L = mp.mpf(8) / 5
        s = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * w / 2)) - mp.fsum(2 * w * mp.e ** (-(2 * j + mp.mpf(1) / 2) * L) / ((2 * j + mp.mpf(1) / 2) ** 2 + w ** 2) for j in range(80))
        p = (mp.sqrt(2) * mp.log(2) * mp.sin(mp.pi * 5 * k * mp.log(2) / 4) + 2 * mp.log(3) / mp.sqrt(3) * mp.sin(mp.pi * 5 * k * mp.log(3) / 4)
             + mp.log(2) * mp.sin(mp.pi * 5 * k * mp.log(2) / 2))
        v = mp.pi * s + mp.pi * p
        inside = lo <= F(mp.nstr(v, 25)) <= hi
        Jold = g.pickJ(k, g.tgt_of(k))
        print(f'k={k} J={J} (old {Jold}) width={float(hi - lo):.3e} inside={inside}')
        assert inside
        rows.append((k, J, lo, hi))
    if len(sys.argv) > 3:
        name = f'CvSTau2L85K{k1}V1'
        Js = ', '.join(str(r[1]) for r in rows)
        def ql(xs): return ',\n'.join(f'  {x.numerator} / {x.denominator}' for x in xs)
        n = len(rows); nb = (n + 4) // 5
        bats = '\n'.join(f'set_option maxRecDepth 100000 in\ntheorem bat_{5*i} : bat {5*i} {min(5, n-5*i)} = true := by decide +kernel\n' for i in range(nb))
        cases = '\n'.join(f'  by_cases h{5*i} : i < {5*i+5}\n  · exact H {5*i} {min(5,n-5*i)} bat_{5*i} (by omega) (by omega)' for i in range(nb - 1))
        last = f'  exact H {5*(nb-1)} {n-5*(nb-1)} bat_{5*(nb-1)} (by omega) (by omega)'
        src = f'''/-
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
import CvSTauFast2L85V1

/-!
# `τ_k` at `L = 8/5`, `k = {k1}, …, {k2}`, second-order tail

Boxes from the untrusted mirror `gen_tau2_85.py` (worst width `{max(float(r[3]-r[2]) for r in rows):.3e}`), checked in batches of
five by `CvSTauFast2L85V1.tauF2` with `decide +kernel`; `tau_mem` encloses `τ_k` for every prime
cutoff `M ≥ 4`. Not RH.
-/

namespace AEGIS.{name}

open AEGIS.CvSTauFast2L85V1 AEGIS.CvSRowTailV1

def k0 : ℕ := {k1}

def tJ : List ℕ := [{Js}]

def tLo : List ℚ := [
{ql([r[2] for r in rows])}]

def tHi : List ℚ := [
{ql([r[3] for r in rows])}]

def bat (s len : ℕ) : Bool :=
  (List.range' s len).all fun i => tauF2 (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0)

{bats}
theorem ok {{i : ℕ}} (hi : i < {n}) :
    tauF2 (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0) = true := by
  have H : ∀ s len, bat s len = true → s ≤ i → i < s + len →
      tauF2 (k0 + i) (tJ.getD i 0) 20 (tLo.getD i 0) (tHi.getD i 0) = true := by
    intro s len h h1 h2
    simp only [bat, List.all_eq_true] at h
    exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)
{cases}
{last}

/-- **`τ_k` for `k = {k1}, …, {k2}`**, every prime cutoff `M ≥ 4`. -/
theorem tau_mem {{M : ℕ}} (hM : 4 ≤ M) {{i : ℕ}} (hi : i < {n}) :
    ((tLo.getD i 0 : ℚ) : ℝ) ≤ tau M (8 / 5) ((k0 + i : ℕ) : ℤ) ∧
      tau M (8 / 5) ((k0 + i : ℕ) : ℤ) ≤ ((tHi.getD i 0 : ℚ) : ℝ) :=
  tauF2_sound hM (ok hi)

end AEGIS.{name}

#print axioms AEGIS.{name}.tau_mem
'''
        open(name + '.lean', 'w').write(src)
        print('wrote', name)
