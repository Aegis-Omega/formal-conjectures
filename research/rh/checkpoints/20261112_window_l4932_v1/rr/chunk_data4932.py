"""Split the big kernel checks of CvSRelRowDataL4932V1 (S_ok*, T_ok*, V_ok*) into chunks of 8 indices,
one `decide +kernel` each; the theorems keep their statements (assembled by `all_of_chunks`).
usage: chunk_data4932.py IN.lean OUT.lean
(derived from ../20261112_window_l32_rowcert_v1/chunk_data.py)"""
import re
import sys
src = open(sys.argv[1]).read()
N, C = 313, 8
chunks = [(a, min(C, N - a)) for a in range(0, N, C)]
lemma = '''/-- A `List.range` check from checks on chunks covering it. -/
theorem all_of_chunks {f : ℕ → Bool} {n : ℕ} (cs : List (ℕ × ℕ))
    (hc : ∀ c ∈ cs, (List.range' c.1 c.2).all f = true)
    (hcov : ∀ i < n, ∃ c ∈ cs, c.1 ≤ i ∧ i < c.1 + c.2) : (List.range n).all f = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨c, hc', h1, h2⟩ := hcov i hi
  have h := hc c hc'
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

def chunks313 : List (ℕ × ℕ) := [''' + ', '.join(f'({a}, {k})' for a, k in chunks) + ''']

theorem chunks313_cov : ∀ i < 313, ∃ c ∈ chunks313, c.1 ≤ i ∧ i < c.1 + c.2 := by decide

'''
pat = re.compile(r"theorem (([ST])_ok(\d)|V_ok(\d)) : \(List\.range 313\)\.all \(fun \(i : ℕ\) =>\n    decide \((.*?)\)\) = true := by\n  decide \+kernel\n", re.S)
count = 0
def rep(m):
    global count
    count += 1
    name, body = m.group(1), m.group(5)
    f = f'(fun (i : ℕ) => decide ({body}))'
    out = ''
    for a, k in chunks:
        out += f"theorem {name}_c{a} : (List.range' {a} {k}).all {f} = true := by\n  decide +kernel\n\n"
    alts = ' | '.join(['rfl'] * len(chunks))
    out += (f"theorem {name} : (List.range 313).all {f} = true :=\n  all_of_chunks chunks313 (fun c hc => by\n"
            f"    simp only [chunks313, List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
            f"    rcases hc with {alts}\n    exacts [{', '.join(f'{name}_c{a}' for a, _ in chunks)}]) chunks313_cov\n")
    return out
out = pat.sub(rep, src)
assert count == 8, count
# ---- boxes_ok: 40 chunks of k (one `decide +kernel` over all 2001 boxes runs out of memory)
bstmt = ('theorem boxes_ok : ((List.range 2001).all fun k =>\n'
         '    decide (((tLit.getD k 0 : ℤ) : ℚ) = (boxLo k + boxHi k) * 2 ^ 48) &&\n'
         '      decide (((rtLit.getD k 0 : ℤ) : ℚ) = (boxHi k - boxLo k) * 2 ^ 48)) &&\n'
         '    ((List.range 157).all fun n =>\n'
         '      decide (((dLit.getD n 0 : ℤ) : ℚ) = (diagLo.getD n 0 + diagHi.getD n 0) * 2 ^ 48) &&\n'
         '        decide (((rdLit.getD n 0 : ℤ) : ℚ) = (diagHi.getD n 0 - diagLo.getD n 0) * 2 ^ 48)) = true := by\n'
         '  decide +kernel\n')
assert out.count(bstmt) == 1
fB = ('(fun (k : ℕ) => decide (((tLit.getD k 0 : ℤ) : ℚ) = (boxLo k + boxHi k) * 2 ^ 48) &&\n'
      '      decide (((rtLit.getD k 0 : ℤ) : ℚ) = (boxHi k - boxLo k) * 2 ^ 48))')
fD = ('(fun (n : ℕ) => decide (((dLit.getD n 0 : ℤ) : ℚ) = (diagLo.getD n 0 + diagHi.getD n 0) * 2 ^ 48) &&\n'
      '      decide (((rdLit.getD n 0 : ℤ) : ℚ) = (diagHi.getD n 0 - diagLo.getD n 0) * 2 ^ 48))')
bch = [(0, 51)] + [(a, 50) for a in range(51, 2001, 50)]
assert bch[-1][0] + bch[-1][1] == 2001
bnew = ("def chunks2001 : List (ℕ × ℕ) := [" + ', '.join(f'({a}, {k})' for a, k in bch) + "]\n\n"
        "theorem chunks2001_cov : ∀ i < 2001, ∃ c ∈ chunks2001, c.1 ≤ i ∧ i < c.1 + c.2 := by decide\n\n")
for a, k in bch:
    bnew += f"theorem boxes_c{a} : (List.range' {a} {k}).all {fB} = true := by\n  decide +kernel\n\n"
bnew += f"theorem dboxes_ok : (List.range 157).all {fD} = true := by\n  decide +kernel\n\n"
bnew += bstmt.replace('  decide +kernel\n', '') + (
    "  rw [Bool.and_eq_true]\n"
    "  refine ⟨all_of_chunks chunks2001 (fun c hc => by\n"
    "    simp only [chunks2001, List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
    f"    rcases hc with {' | '.join(['rfl'] * len(bch))}\n"
    f"    exacts [{', '.join(f'boxes_c{a}' for a, _ in bch)}]) chunks2001_cov, decide_eq_true dboxes_ok⟩\n")
first = out.index('/-- The box ends as functions of `k`. -/')
out = out[:first] + lemma + out[first:]
out = out.replace(bstmt, bnew)
open(sys.argv[2], 'w').write(out)
print('chunked', count, 'checks into', len(chunks), 'pieces each')
# ---- split into A (box lists, S/T tables and their chunked checks) and B (the rest), same namespace
t = open(sys.argv[2]).read()
t = t.replace('set_option Elab.async false\n', 'set_option Elab.async false\nset_option maxHeartbeats 0\n', 1)
cut = t.index('/-- `Σ_{k ≤ u} 2^128 / k`')
head_end = t.index('namespace AEGIS.CvSRelRowDataL4932V1')
lic = t[:t.index('import ')]
A = t[:cut] + 'end AEGIS.CvSRelRowDataL4932V1\n'
A = A.replace('# Integer data of the relative row certificate at `L = 49/32`', '# Integer data of the relative row certificate at `L = 49/32`, part A (boxes, outside-row tables)', 1)
B = (lic + 'import CvSRelRowDataAL4932V1\n\n/-!\n# Integer data of the relative row certificate at `L = 49/32`, part B\n\n'
     'Harmonic numbers, the vector `g1`, the constants, `Et`, `Kt`, `Gt`, `Zt` and the projected rows `VLit`\n'
     '(part A: boxes and the outside-row tables). Every table is recomputed by the kernel. Not RH.\n-/\n\n'
     'namespace AEGIS.CvSRelRowDataL4932V1\n\nset_option maxRecDepth 100000\nset_option Elab.async false\nset_option maxHeartbeats 0\n\n' + t[cut:])
open(sys.argv[2].replace('CvSRelRowDataL4932V1.lean', 'CvSRelRowDataAL4932V1.lean'), 'w').write(A)
open(sys.argv[2], 'w').write(B)
print('split: A', len(A) // 1024, 'KB, B', len(B) // 1024, 'KB')
