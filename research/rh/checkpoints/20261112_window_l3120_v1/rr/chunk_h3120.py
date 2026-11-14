"""Chunk h_ok of CvSRelRowDataL3120V1 (2157 steps) into 44 kernel checks of <= 50 steps.
usage: python3 chunk_h3120.py FILE"""
import sys
from pathlib import Path
p = Path(sys.argv[1]); t = p.read_text()
old = '''theorem h_ok : (hLit.getD 0 0 = 0) ∧ (List.range 2157).all (fun k =>
    decide (hLit.getD (k + 1) 0 = hLit.getD k 0 + 2 ^ 128 / ((k : ℤ) + 1))) = true := by
  constructor
  · decide +kernel
  · decide +kernel
'''
assert t.count(old) == 1
CH = [(a, min(50, 2157 - a)) for a in range(0, 2157, 50)]
f = 'fun k => decide (hLit.getD (k + 1) 0 = hLit.getD k 0 + 2 ^ 128 / ((k : ℤ) + 1))'
new = 'def chunksH : List (ℕ × ℕ) := [' + ', '.join(f'({a}, {k})' for a, k in CH) + ']\n\n'
new += 'theorem chunksH_cov : ∀ i < 2157, ∃ c ∈ chunksH, c.1 ≤ i ∧ i < c.1 + c.2 := by decide\n\n'
for a, k in CH:
    new += f'theorem h_c{a} : (List.range\' {a} {k}).all ({f}) = true := by\n  decide +kernel\n\n'
new += old.split(':= by')[0] + ':= by\n  refine ⟨by decide +kernel, all_of_chunks chunksH (fun c hc => by\n'
new += '    simp only [chunksH, List.mem_cons, List.mem_nil_iff, or_false] at hc\n'
new += '    rcases hc with ' + ' | '.join(['rfl'] * len(CH)) + '\n'
new += '    exacts [' + ', '.join(f'h_c{a}' for a, _ in CH) + ']) chunksH_cov⟩\n'
t = t.replace(old, new)
p.write_text(t)
print(len(CH), 'chunks')
