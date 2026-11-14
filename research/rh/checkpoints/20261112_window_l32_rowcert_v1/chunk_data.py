"""Split the big kernel checks of CvSRelRowDataL32V1 (S_ok*, T_ok*, V_ok*) into chunks of 20 indices,
one `decide +kernel` each; the theorems keep their statements (assembled by `all_of_chunks`).
usage: chunk_data.py IN.lean OUT.lean"""
import re
import sys
src = open(sys.argv[1]).read()
N, C = 301, 20
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

def chunks301 : List (ℕ × ℕ) := [''' + ', '.join(f'({a}, {k})' for a, k in chunks) + ''']

theorem chunks301_cov : ∀ i < 301, ∃ c ∈ chunks301, c.1 ≤ i ∧ i < c.1 + c.2 := by decide

'''
pat = re.compile(r"theorem (([ST])_ok(\d)|V_ok(\d)) : \(List\.range 301\)\.all \(fun \(i : ℕ\) =>\n    decide \((.*?)\)\) = true := by\n  decide \+kernel\n", re.S)
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
    out += (f"theorem {name} : (List.range 301).all {f} = true :=\n  all_of_chunks chunks301 (fun c hc => by\n"
            f"    simp only [chunks301, List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
            f"    rcases hc with {alts}\n    exacts [{', '.join(f'{name}_c{a}' for a, _ in chunks)}]) chunks301_cov\n")
    return out
out = pat.sub(rep, src)
assert count == 8, count
first = out.index('theorem S_ok0_c0')
out = out[:first] + lemma + out[first:]
open(sys.argv[2], 'w').write(out)
print('chunked', count, 'checks into', len(chunks), 'pieces each')
# ---- split into A (box lists, S/T tables and their chunked checks) and B (the rest), same namespace
t = open(sys.argv[2]).read()
t = t.replace('set_option Elab.async false\n', 'set_option Elab.async false\nset_option maxHeartbeats 0\n', 1)
cut = t.index('/-- `Σ_{k ≤ u} 2^128 / k`')
head_end = t.index('namespace AEGIS.CvSRelRowDataL32V1')
lic = t[:t.index('import ')]
A = t[:cut] + 'end AEGIS.CvSRelRowDataL32V1\n'
A = A.replace('# Integer data of the relative row certificate at `L = 3/2`', '# Integer data of the relative row certificate at `L = 3/2`, part A (boxes, outside-row tables)', 1)
B = (lic + 'import CvSRelRowDataAL32V1\n\n/-!\n# Integer data of the relative row certificate at `L = 3/2`, part B\n\n'
     'Harmonic numbers, the vector `g1`, the constants, `Et`, `Kt`, `Gt`, `Zt` and the projected rows `VLit`\n'
     '(part A: boxes and the outside-row tables). Every table is recomputed by the kernel. Not RH.\n-/\n\n'
     'namespace AEGIS.CvSRelRowDataL32V1\n\nset_option maxRecDepth 100000\nset_option Elab.async false\nset_option maxHeartbeats 0\n\n' + t[cut:])
open(sys.argv[2].replace('CvSRelRowDataL32V1.lean', 'CvSRelRowDataAL32V1.lean'), 'w').write(A)
open(sys.argv[2], 'w').write(B)
print('split: A', len(A) // 1024, 'KB, B', len(B) // 1024, 'KB')
