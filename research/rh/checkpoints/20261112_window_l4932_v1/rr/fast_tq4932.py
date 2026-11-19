"""A faster `tLit` lookup for the outside-row checks at L = 49/32 (the kernel check of `Sraw 1` walks
`tLit` 3688 times per row and runs out of memory). Adds `tLitC` (rows of 50), `tget` (kernel-checked
against `tLit`), `tq2`, `pwv`, `Sraw2`/`Traw2` with `Sraw_eq`/`Traw_eq`, and re-proves `S_ok1`, `S_ok2`,
`T_ok1`, `T_ok2` (same statements) from chunked checks of `Sraw2`/`Traw2`.
usage: fast_tq4932.py DIR test|apply"""
import re
import sys
from pathlib import Path
d, mode = Path(sys.argv[1]), sys.argv[2]
A0 = (d / 'CvSRelRowDataA0L4932V1.lean').read_text()
i = A0.index('def tLit : List ℤ :=')
tl = [int(x) for x in re.findall(r'-?\d+', A0[A0.index('[', i):A0.index(']', i)])]
assert len(tl) == 2001
rows = [tl[a:a + 50] for a in range(0, 2001, 50)]
assert len(rows) == 41 and len(rows[-1]) == 1
def lst(xs, ind):
    out, line = [], ''
    for x in xs:
        s = f'{x}, '
        if len(line) + len(s) > 96:
            out.append(line.rstrip()); line = ''
        line += s
    out.append(line.rstrip().rstrip(','))
    return ('\n' + ind).join(out)
ch = [(a, 50) for a in range(0, 2000, 50)] + [(2000, 1)]
alts = ' | '.join(['rfl'] * len(ch))
F = '''/-! ## A faster lookup of `tLit` for the kernel

`tLit.getD k 0` walks `k` cells, and the outside sums `Sraw 1`, `Sraw 2` look up `3688` boxes for
each row (one such kernel check runs out of memory). `tget k` reads the same value from rows of
`50` (`tget_ok`, kernel-checked against `tLit`), and `Sraw2` is `Sraw` with this lookup
(`Sraw_eq`). -/

/-- `tLit` in rows of `50`. -/
def tLitC : List (List ℤ) := [
''' + ',\n'.join('  [' + lst(r, '   ') + ']' for r in rows) + ''']

/-- `tLit.getD k 0` read from the rows. -/
def tget (k : ℕ) : ℤ := (tLitC.getD (k / 50) []).getD (k % 50) 0

def chunksT : List (ℕ × ℕ) := [''' + ', '.join(f'({a}, {k})' for a, k in ch) + ''']

theorem chunksT_cov : ∀ i < 2001, ∃ c ∈ chunksT, c.1 ≤ i ∧ i < c.1 + c.2 := by decide

''' + ''.join(f"theorem tget_c{a} : (List.range' {a} {k}).all (fun (k : ℕ) => decide (tLit.getD k 0 = tget k)) = true := by\n  decide +kernel\n\n" for a, k in ch) + f'''theorem tget_ok : (List.range 2001).all (fun (k : ℕ) => decide (tLit.getD k 0 = tget k)) = true :=
  all_of_chunks chunksT (fun c hc => by
    simp only [chunksT, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with {alts}
    exacts [{', '.join(f'tget_c{a}' for a, _ in ch)}]) chunksT_cov

theorem tLit_eq_tget {{k : ℕ}} (hk : k < 2001) : tLit.getD k 0 = tget k := by
  have h := tget_ok
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h k (List.mem_range.mpr hk))

/-- `tq` with the row lookup. -/
def tq2 (k : ℤ) : ℤ := if 0 ≤ k then tget k.toNat else -tget (-k).toNat

theorem tq_eq {{m : ℤ}} (h1 : -2000 ≤ m) (h2 : m ≤ 2000) : tq m = tq2 m := by
  unfold tq tq2
  split_ifs with h
  · rw [tLit_eq_tget (k := m.toNat) (by omega)]
  · rw [tLit_eq_tget (k := (-m).toNat) (by omega)]

/-- `pw j m` as a function of `τ̂_m`. -/
def pwv (j : ℕ) (t : ℤ) : ℤ :=
  match j with
  | 0 => 2 ^ 128
  | 1 => t * 2 ^ 79
  | _ => t * t * 2 ^ 30

theorem pw_pwv (j : ℕ) (m : ℤ) : pw j m = pwv j (tq m) := by
  rcases j with _ | _ | j <;> rfl

theorem HL_all : HL.all (fun m => decide (-2000 ≤ m ∧ m ≤ 2000)) = true := by decide +kernel

theorem HL_bound {{m : ℤ}} (h : m ∈ HL) : -2000 ≤ m ∧ m ≤ 2000 :=
  of_decide_eq_true (List.all_eq_true.mp HL_all m h)

/-- `Sraw` with the row lookup. -/
def Sraw2 (j : ℕ) (n : ℤ) : ℤ := (HL.map fun m => pwv j (tq2 m) / (m - n)).sum

theorem Sraw_eq (j : ℕ) (n : ℤ) : Sraw j n = Sraw2 j n := by
  have h : HL.map (fun m => pw j m / (m - n)) = HL.map (fun m => pwv j (tq2 m) / (m - n)) :=
    List.map_congr_left fun m hm => by
      obtain ⟨h1, h2⟩ := HL_bound hm
      rw [pw_pwv, tq_eq h1 h2]
  rw [Sraw, Sraw2, h]

'''
TF = '''/-- `Traw` with the row lookup. -/
def Traw2 (j : ℕ) (n : ℤ) : ℤ := (HL.map fun m => pwv j (tq2 m) / ((m - n) * (m - n))).sum

theorem Traw_eq (j : ℕ) (n : ℤ) : Traw j n = Traw2 j n := by
  have h : HL.map (fun m => pw j m / ((m - n) * (m - n))) = HL.map (fun m => pwv j (tq2 m) / ((m - n) * (m - n))) :=
    List.map_congr_left fun m hm => by
      obtain ⟨h1, h2⟩ := HL_bound hm
      rw [pw_pwv, tq_eq h1 h2]
  rw [Traw, Traw2, h]

'''
A1p = d / 'CvSRelRowDataA1L4932V1.lean'
A1 = A1p.read_text()
if mode == 'test':
    j = A1.index('def SLit')
    v = int(re.search(r'-?\d+', A1[A1.index('[', A1.index('[', j) + 1, ) + 0:][1:]).group()) if False else None
    sl = re.findall(r'-?\d+', A1[A1.index('[', j) + 1:A1.index('def Sq')])
    v10 = int(sl[313])  # SLit[1][0] = Sraw 1 (-156)
    lic = A0[:A0.index('import ')]
    T = (lic + 'import CvSRelRowDataA0L4932V1\n\nnamespace AEGIS.CvSRelRowDataL4932V1\n\nset_option maxRecDepth 100000\n'
         'set_option Elab.async false\nset_option maxHeartbeats 0\n\n' + F +
         TF + f'def sl1 : List ℤ := [{", ".join(sl[313:321])}]\n\n' +
         "theorem test_S8 : (List.range' 0 8).all (fun (i : ℕ) => decide (sl1.getD i 0 = Sraw2 1 ((i : ℤ) - 156))) = true := by\n  decide +kernel\n\n"
         'end AEGIS.CvSRelRowDataL4932V1\n')
    (d / 'TestFastL4932.lean').write_text(T)
    print('test written; SLit[1][0] =', v10)
    sys.exit(0)
def reprove(t, X, raw, j):
    nm = f'{X}_ok{j}'
    stmt = f"(List.range 313).all (fun (i : ℕ) => decide ({X}q {j} ((i : ℤ) - 156) = {raw} {j} ((i : ℤ) - 156))) = true"
    a = t.index(f'theorem {nm}_c0 :'); b = t.index(f'theorem {nm} : ')
    e = t.index('chunks313_cov\n', b) + len('chunks313_cov\n')
    blk = t[a:e]
    assert blk.count(f'{raw} {j} ') == 41, blk.count(f'{raw} {j} ')
    blk = blk.replace(f'{raw} {j} ', f'{raw}2 {j} ').replace(f'{nm}_c', f'{X}2_ok{j}_c').replace(f'theorem {nm} :', f'theorem {X}2_ok{j} :')
    blk += f"\ntheorem {nm} : {stmt} := by\n  simp only [{raw}_eq]\n  exact {X}2_ok{j}\n"
    return t[:a] + blk + t[e:]
assert 'def tLitC' not in A1
k = A1.index('theorem S_ok0_c0')
A1 = A1[:k] + F + A1[k:]
for j in (1, 2):
    A1 = reprove(A1, 'S', 'Sraw', j)
A1p.write_text(A1)
Ap = d / 'CvSRelRowDataAL4932V1.lean'
A = Ap.read_text()
k = A.index('theorem T_ok0_c0')
A = A[:k] + TF + A[k:]
for j in (1, 2):
    A = reprove(A, 'T', 'Traw', j)
Ap.write_text(A)
print('applied: A1', len(A1) // 1024, 'KB, A', len(A) // 1024, 'KB')
