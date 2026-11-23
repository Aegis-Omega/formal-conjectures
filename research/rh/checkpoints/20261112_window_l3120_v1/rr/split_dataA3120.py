"""Split CvSRelRowDataAL3120V1 (one process ran out of memory) into a chain of three modules in the
same namespace: A0 (box lists, boxes_ok, tq ... Traw), A1 (SLit, Sq, S_ok*), A (TLit, Tq, T_ok*).
Statements unchanged; CvSRelRowDataL3120V1 still imports CvSRelRowDataAL3120V1.
usage: split_dataA3120.py DIR   (rewrites DIR/CvSRelRowDataAL3120V1.lean, writes A0 and A1)"""
import sys
from pathlib import Path
d = Path(sys.argv[1]); t = (d / 'CvSRelRowDataAL3120V1.lean').read_text()
lic = t[:t.index('import ')]
ns = 'namespace AEGIS.CvSRelRowDataL3120V1\n'
hs = t.index(ns) + len(ns)
opts = '\nset_option maxRecDepth 100000\nset_option Elab.async false\nset_option maxHeartbeats 0\n\n'
assert t[hs:].startswith(opts)
body = t[hs + len(opts):t.rindex('end AEGIS.CvSRelRowDataL3120V1')]
iS, iT = body.index('/-- `Sraw j n`'), body.index('/-- `Traw j n`. -/')
iSq = body.index('def Sq (j : ℕ)'); iTq = body.index('def Tq (j : ℕ)'); iE = body.index('\n', iTq) + 1
iTo = body.index('theorem T_ok0_c0')
p0, pS, pT = body[:iS], body[iS:iT] + body[iSq:iTq] + body[iE:iTo], body[iT:iSq] + body[iTq:iE] + body[iTo:]
assert 'TLit' not in pS and 'theorem T_ok' not in pS and 'theorem S_ok' not in pT
end = 'end AEGIS.CvSRelRowDataL3120V1\n'
A0 = t[:hs] + opts + p0 + end
A0 = A0.replace('part A (boxes, outside-row tables)', 'part A0 (boxes, outside-row definitions)', 1)
def mod(imp, title, part):
    return (lic + f'import {imp}\n\n/-!\n# Integer data of the relative row certificate at `L = 31/20`, {title}\n\n'
            'Kernel-checked table of the outside rows (data from `gen_rr3120.py`, untrusted). Not RH.\n-/\n\n'
            + ns + opts + part + end)
A1 = mod('CvSRelRowDataA0L3120V1', 'part A1 (`SLit`)', pS)
A = mod('CvSRelRowDataA1L3120V1', 'part A (`TLit`)', pT)
(d / 'CvSRelRowDataA0L3120V1.lean').write_text(A0)
(d / 'CvSRelRowDataA1L3120V1.lean').write_text(A1)
(d / 'CvSRelRowDataAL3120V1.lean').write_text(A)
print('A0', len(A0) // 1024, 'KB  A1', len(A1) // 1024, 'KB  A', len(A) // 1024, 'KB')
