"""Write a timed copy of a blocks script: only print lines are inserted (before top-level anchors)."""
import sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')
anchors = [('Qb = acb_mat(', 'seqs+rows'), ('# tail |n| > NP', 'RR'), ('Zh = Z.conjugate()', 'terms'),
           ('def mid(M)', 'A11G11'), ('assert sum(pw)', 'weights'), ("print('K2'", 'Tail'), ('U2 = acb_mat(', 'Ib'),
           ('X = RR + Tail + Ib', 'Woodbury'), ('CB = ', 'preCB'), ('blocks = {', 'CB')]
out = []; hit = set()
for ln in lines:
    for a, lab in anchors:
        if ln.startswith(a) and lab not in hit:
            out.append(f"tick('{lab}')"); hit.add(lab)
    out.append(ln)
    if ln.startswith('import sys, math, json'):
        out.append("import time as _tm; _T0 = _tm.perf_counter()\ndef tick(s): print('T', s, round(_tm.perf_counter() - _T0, 2), flush=True)")
out.append("tick('end')")
open(dst, 'w').write('\n'.join(out))
print(dst, sorted(hit))
