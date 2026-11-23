"""Row lookup for hLit (2158 values) in the column data of CvSRelRowCheckL3120V1: `hget` reads
`hLit` in rows of 50; the kernel checks `hLit.getD k 0 = hget k` in 44 chunks, `colF_eq` and
`cols313F_eq` transfer it, and `Pchunk` reads `cols313F`. Psd gets `cols313F_eq` in `Pchunk_eq`.
usage: python3 fast_hq3120.py DIR   (DIR holds Data B, Check and Psd)"""
import re
import sys
from pathlib import Path
D = Path(sys.argv[1])
b = (D / 'CvSRelRowDataL3120V1.lean').read_text()
i = b.index('def hLit : List ℤ :=')
body = b[b.index('[', i) + 1:b.index(']', i)]
h = [int(x) for x in re.findall(r'-?\d+', body)]
assert len(h) == 2158, len(h)
rows = [h[a:a + 50] for a in range(0, 2158, 50)]
CH = [(a, min(50, 2158 - a)) for a in range(0, 2158, 50)]
F = '\n/-! ## `hLit` in rows of 50 -/\n\n'
F += 'def hLitC : List (List ℤ) := [\n' + ',\n'.join('  [' + ', '.join(map(str, r)) + ']' for r in rows) + ']\n\n'
F += 'def hget (k : ℕ) : ℤ := (hLitC.getD (k / 50) []).getD (k % 50) 0\n\n'
F += 'def chunksG : List (ℕ × ℕ) := [' + ', '.join(f'({a}, {k})' for a, k in CH) + ']\n\n'
F += 'theorem chunksG_cov : ∀ i < 2158, ∃ c ∈ chunksG, c.1 ≤ i ∧ i < c.1 + c.2 := by decide\n\n'
f = 'fun (k : ℕ) => decide (hLit.getD k 0 = hget k)'
for a, k in CH:
    F += f"theorem hget_c{a} : (List.range' {a} {k}).all ({f}) = true := by\n  decide +kernel\n\n"
F += f'theorem hget_ok : (List.range 2158).all ({f}) = true :=\n  all_of_chunks chunksG (fun c hc => by\n'
F += '    simp only [chunksG, List.mem_cons, List.mem_nil_iff, or_false] at hc\n'
F += '    rcases hc with ' + ' | '.join(['rfl'] * len(CH)) + '\n'
F += '    exacts [' + ', '.join(f'hget_c{a}' for a, _ in CH) + ']) chunksG_cov\n\n'
F += '''theorem hq_eq {u : ℤ} (h0 : 0 ≤ u) (h1 : u ≤ 2157) : hq u = hget u.toNat := by
  have h := hget_ok
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h u.toNat (List.mem_range.mpr (by omega)))

/-- `col` with the row lookup for `h`. -/
def colF (m : ℤ) : Col := ⟨m, tq m, phi m, Sq 0 m, Sq 1 m, Sq 2 m, hget (2000 - m).toNat, hget (2000 + m).toNat⟩

theorem colF_eq {m : ℤ} (h1 : -156 ≤ m) (h2 : m ≤ 156) : colF m = col m := by
  have a := hq_eq (u := 2000 - m) (by omega) (by omega)
  have b := hq_eq (u := 2000 + m) (by omega) (by omega)
  simp only [colF, col, a, b]

'''
G = '''def cols313F : List Col := (List.range 313).map fun (b : ℕ) => colF ((b : ℤ) - 156)

theorem cols313F_eq : cols313F = cols313 := by
  have h : ((List.range 313).map fun (b : ℕ) => colF ((b : ℤ) - 156)) =
      (List.range 313).map fun (b : ℕ) => col ((b : ℤ) - 156) :=
    List.map_congr_left fun b hb => by
      have := List.mem_range.mp hb
      exact colF_eq (by omega) (by omega)
  rw [cols313F, cols313, h]

'''
c = (D / 'CvSRelRowCheckL3120V1.lean').read_text()
def sub(t, x, y):
    assert t.count(x) == 1, (x, t.count(x))
    return t.replace(x, y)
c = sub(c, '/-! ## Strict evaluation of the column data -/', F.lstrip('\n') + '/-! ## Strict evaluation of the column data -/')
c = sub(c, 'def zrowC (cl : List Col)', G + 'def zrowC (cl : List Col)')
c = sub(c, 'fCL cols313 fun cl =>', 'fCL cols313F fun cl =>')
c = sub(c, "`Zt` rows forced once per chunk by `FastKronV1.fLL`)", "`Zt` rows forced once per chunk by `FastKronV1.fLL`; `h` read through the row lookup `hget`)")
(D / 'CvSRelRowCheckL3120V1.lean').write_text(c)
p = (D / 'CvSRelRowPsdL3120V1.lean').read_text()
p = sub(p, '  simp only [Pchunk, fL_eq, fCL_eq, fLL_eq]\n', '  simp only [Pchunk, fL_eq, fCL_eq, fLL_eq, cols313F_eq]\n')
(D / 'CvSRelRowPsdL3120V1.lean').write_text(p)
print('Check +', F.count('\n') + G.count('\n'), 'lines;', len(CH), 'chunks; Psd patched')
