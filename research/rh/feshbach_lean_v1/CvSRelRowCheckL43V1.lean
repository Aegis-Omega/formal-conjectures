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
import CvSRelRowDataL43V1
import CvSRelRowCertL43V1
import FastKronV1

/-!
# The check matrix of the relative row certificate at `L = 4/3` is positive

`Pm i j` (scale `2^-488`) is the second difference in both indices of `φ_n φ_m Zt n m`, minus the
rank-two part `γ_j U_j Uⱼᵀ`. The kernel computes its rows in seven chunks (`Pchunk`, with the
`Zt` rows forced once per chunk by `FastKronV1.fLL`), rounds them to intervals at `2^-64` after
the scaling `2^-(certD_i + certD_j)`, and checks the packed factor `certL` row by row
(`chunk*_ok`). `Pm_psd`: `0 ≤ Re Σ c_i conj(c_j) Pm i j` for every `c`. Not RH.
-/

open Finset
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowCertL43V1 AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1
  AEGIS.FastKronV1

namespace AEGIS.CvSRelRowCheckL43V1

set_option maxRecDepth 100000
set_option Elab.async false

/-! ## The matrix -/

def wq (s : ℕ) : ℤ := if s = 1 then 2 else -1

def Zf (n m : ℤ) : ℤ := phi n * phi m * Zt n m

def U (jj i : ℕ) : ℤ := ∑ s ∈ range 3, wq s * (phi ((i : ℤ) - 70 + s) * Vq jj ((i : ℤ) - 70 + s))

/-- The check matrix at `2^-488`. -/
def Pm (i j : ℕ) : ℤ :=
  2 ^ 212 * (∑ s ∈ range 3, ∑ t ∈ range 3, wq s * wq t * Zf ((i : ℤ) - 70 + s) ((j : ℤ) - 70 + t)) -
    (G1q * U 0 i * U 0 j + G2q * U 1 i * U 1 j)

/-! ## Column data and one entry of `Zt` without table lookups -/

/-- Per index `m`: `m, 2^49 τ̂_m, φ_m, S_j(m), h(200 - m), h(200 + m)`. -/
structure Col where
  m : ℤ
  t : ℤ
  ph : ℤ
  s0 : ℤ
  s1 : ℤ
  s2 : ℤ
  hm : ℤ
  hp : ℤ

/-- Per row `n`: the column data plus `T_j(n)` and `2^49 D̂_n`. -/
structure RowC where
  c : Col
  t0 : ℤ
  t1 : ℤ
  t2 : ℤ
  d : ℤ

def col (m : ℤ) : Col := ⟨m, tq m, phi m, Sq 0 m, Sq 1 m, Sq 2 m, hq (200 - m), hq (200 + m)⟩

def rowc (n : ℤ) : RowC := ⟨col n, Tq 0 n, Tq 1 n, Tq 2 n, dq n⟩

/-- `Zt n m` from the row and column data (the same expression as `Zt` with the lookups done). -/
def zent (r : RowC) (q : Col) : ℤ :=
  let n := r.c.m
  let m := q.m
  let kj := fun (tj sn sm : ℤ) => if n = m then tj else if m < n then (sn - sm) / (n - m) else
    (sm - sn) / (m - n)
  let kt := kj r.t2 r.c.s2 q.s2 - (r.c.t + q.t) * kj r.t1 r.c.s1 q.s1 / 2 ^ 49 +
    r.c.t * q.t * kj r.t0 r.c.s0 q.s0 / 2 ^ 98
  let et := if n = m then r.d * 2 ^ 79 else if m < n then Cq * (r.c.t - q.t) * 2 ^ 15 / (n - m)
    else Cq * (q.t - r.c.t) * 2 ^ 15 / (m - n)
  let gt := if n = m then 2 ^ 129 / (401 - 2 * n) + 2 ^ 129 / (401 + 2 * n)
    else if m < n then (q.hm - r.c.hm + (r.c.hp - q.hp)) / (n - m)
    else (r.c.hm - q.hm + (q.hp - r.c.hp)) / (m - n)
  52 * et - LPq * kt / 2 ^ 64 - T1q * (r.c.t * q.t * gt / 2 ^ 98) / 2 ^ 64 - T2q * gt / 2 ^ 64 -
    if n = m then Kq * 2 ^ 64 else 0

/-! ## Strict evaluation of the column data -/

def fC {α : Sort _} (q : Col) (k : Col → α) : α :=
  fI q.m fun a => fI q.t fun b => fI q.ph fun c => fI q.s0 fun d => fI q.s1 fun e =>
  fI q.s2 fun f => fI q.hm fun g => fI q.hp fun h => k ⟨a, b, c, d, e, f, g, h⟩

def fCL {α : Sort _} : List Col → (List Col → α) → α
  | [], k => k []
  | a :: l, k => fC a fun a' => fCL l fun l' => k (a' :: l')

theorem fC_eq {α : Sort _} (q : Col) (k : Col → α) : fC q k = k q := by
  cases q; simp only [fC, fI_eq]

theorem fCL_eq {α : Sort _} (l : List Col) (k : List Col → α) : fCL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp only [fCL, fC_eq, ih]

/-! ## The kernel pipeline -/

def cols141 : List Col := (List.range 141).map fun (b : ℕ) => col ((b : ℤ) - 70)

def zrowC (cl : List Col) (n : ℤ) : List ℤ :=
  let r := rowc n
  cl.map fun q => r.c.ph * q.ph * zent r q

def sd3 (x y z : ℤ) : ℤ := -x + 2 * y - z

def Ul (jj : ℕ) : List ℤ := (List.range 139).map (U jj)

def Prow (z0 z1 z2 u1 u2 : List ℤ) (i : ℕ) : List ℤ :=
  List.zipWith3 (fun p v1 v2 => 2 ^ 212 * p - (G1q * u1.getD i 0 * v1 + G2q * u2.getD i 0 * v2))
    (List.zipWith3 sd3 (List.zipWith3 sd3 z0 z1 z2) (List.zipWith3 sd3 z0 z1 z2).tail
      (List.zipWith3 sd3 z0 z1 z2).tail.tail) u1 u2

def Ivrow (i : ℕ) (r : List ℤ) : List Iv :=
  List.zipWith (fun (dj : ℕ) (x : ℤ) =>
      (⟨x >>> (424 + certD.getD i 0 + dj), (x >>> (424 + certD.getD i 0 + dj)) + 1⟩ : Iv)) certD r

def Pchunk (a k : ℕ) : List (List ℤ) :=
  fL (Ul 0) fun u1 => fL (Ul 1) fun u2 => fCL cols141 fun cl =>
  fLL ((List.range (k + 2)).map fun r => zrowC cl (((a + r : ℕ) : ℤ) - 70)) fun Z =>
  (List.range k).map fun r => Prow (Z.getD r []) (Z.getD (r + 1) []) (Z.getD (r + 2) []) u1 u2 (a + r)

def Ichunk (a k : ℕ) : List (List Iv) :=
  List.zipWith Ivrow ((List.range k).map (a + ·)) (Pchunk a k)

def Itab : List (List Iv) :=
  Ichunk 0 20 ++ Ichunk 20 20 ++ Ichunk 40 20 ++ Ichunk 60 20 ++ Ichunk 80 20 ++ Ichunk 100 20 ++
    Ichunk 120 19

def cols : List (ℕ × ℤ) := certL.map fun r => (pack certBase (offRow certB r).reverse, r.sum)

/-! ## The kernel checks, one chunk of rows at a time -/

theorem chunk0_ok : rowsOk certBase certB 139 certEps certEta cols 0
    ((certL.drop 0).take 20) (Ichunk 0 20) = true := by decide +kernel
theorem chunk1_ok : rowsOk certBase certB 139 certEps certEta cols 20
    ((certL.drop 20).take 20) (Ichunk 20 20) = true := by decide +kernel
theorem chunk2_ok : rowsOk certBase certB 139 certEps certEta cols 40
    ((certL.drop 40).take 20) (Ichunk 40 20) = true := by decide +kernel
theorem chunk3_ok : rowsOk certBase certB 139 certEps certEta cols 60
    ((certL.drop 60).take 20) (Ichunk 60 20) = true := by decide +kernel
theorem chunk4_ok : rowsOk certBase certB 139 certEps certEta cols 80
    ((certL.drop 80).take 20) (Ichunk 80 20) = true := by decide +kernel
theorem chunk5_ok : rowsOk certBase certB 139 certEps certEta cols 100
    ((certL.drop 100).take 20) (Ichunk 100 20) = true := by decide +kernel
theorem chunk6_ok : rowsOk certBase certB 139 certEps certEta cols 120
    ((certL.drop 120).take 19) (Ichunk 120 19) = true := by decide +kernel

theorem certL_ok : (decide (0 < 139) && decide (139 * 139 * (2 * certB * (2 * certB)) < certBase) &&
    decide (certL.length = 139) && certL.all (rowBounded certB 139)) = true := by decide +kernel

/-! ## List lemmas -/

theorem length_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) :
    ∀ (a : List α) (b : List β) (c : List γ),
      (List.zipWith3 f a b c).length = min a.length (min b.length c.length)
  | [], _, _ => by simp [List.zipWith3]
  | _ :: _, [], _ => by simp [List.zipWith3]
  | _ :: _, _ :: _, [] => by simp [List.zipWith3]
  | _ :: a, _ :: b, _ :: c => by
    simp only [List.zipWith3, List.length_cons, length_zipWith3 f a b c]
    omega

theorem getD_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (da : α) (db : β) (dc : γ) (dd : δ) :
    ∀ (a : List α) (b : List β) (c : List γ) (k : ℕ), k < a.length → k < b.length → k < c.length →
      (List.zipWith3 f a b c).getD k dd = f (a.getD k da) (b.getD k db) (c.getD k dc)
  | [], _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp at h
  | x :: a, y :: b, z :: c, 0, _, _, _ => by simp [List.zipWith3]
  | x :: a, y :: b, z :: c, k + 1, ha, hb, hc => by
    simp only [List.zipWith3, List.getD_cons_succ]
    exact getD_zipWith3 f da db dc dd a b c k (by simpa using ha) (by simpa using hb)
      (by simpa using hc)

theorem getD_tail {α : Type*} (l : List α) (k : ℕ) (d : α) : l.tail.getD k d = l.getD (k + 1) d := by
  cases l <;> simp

theorem getD_map_range' {α : Type*} {n k : ℕ} (f : ℕ → α) (d : α) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem length_certD : certD.length = 139 := by decide

end AEGIS.CvSRelRowCheckL43V1

#print axioms AEGIS.CvSRelRowCheckL43V1.chunk0_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk1_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk2_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk3_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk4_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk5_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.chunk6_ok
#print axioms AEGIS.CvSRelRowCheckL43V1.certL_ok
