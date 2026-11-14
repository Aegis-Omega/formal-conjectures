"""Chunk the range-2001 part of CvSRelRowBoxL4932V1.maxima_ok into the 40 chunks `chunks2001`
of the data module (statement unchanged). usage: python3 chunk_box4932.py FILE"""
import sys
from pathlib import Path
p = Path(sys.argv[1]); t = p.read_text()
old = '''      |tLit.getD k 0| ≤ max tmq tmHq)) = true := by
  decide +kernel
'''
assert t.count(old) == 1
CH = [(0, 51)] + [(a, 50) for a in range(51, 2001, 50)]
assert sum(k for _, k in CH) == 2001 and len(CH) == 40
f = ('fun k => decide (0 ≤ rtLit.getD k 0 ∧ rtLit.getD k 0 ≤ max rhoq rhoHq ∧\n'
     '      |tLit.getD k 0| ≤ max tmq tmHq)')
pre = ''.join(f"theorem max_c{a} : (List.range' {a} {k}).all ({f}) = true := by\n  decide +kernel\n\n" for a, k in CH)
new = '''      |tLit.getD k 0| ≤ max tmq tmHq)) = true := by
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, decide_eq_true (all_of_chunks chunks2001 (fun c hc => by
    simp only [chunks2001, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with ''' + ' | '.join(['rfl'] * len(CH)) + '''
    exacts [''' + ', '.join(f'max_c{a}' for a, _ in CH) + ''']) chunks2001_cov)⟩
'''
t = t.replace(old, new)
a = t.index('theorem maxima_ok')
t = t[:a] + pre + t[a:]
p.write_text(t)
print(len(CH), 'chunks')
