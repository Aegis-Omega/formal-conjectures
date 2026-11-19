"""Derive gen_diag32.py (untrusted mirror for CvSDiagL32V1, window L = 3/2, K series terms, the extra
prime power 4) from the lab's tools/gen_diag118.py by textual substitution.
usage: python3 make_gen_diag32.py REPO OUTDIR
"""
import re
import sys
from pathlib import Path

repo, out = Path(sys.argv[1]), Path(sys.argv[2])
t = (repo / 'research/rh/feshbach_lean_v1/tools/gen_diag118.py').read_text()
def sub1(a, b, cnt=1):
    global t
    assert t.count(a) == cnt, (a, t.count(a))
    t = t.replace(a, b)
d1 = t.index('"""', 3) + 3
t = ('"""Untrusted generator for CvSDiagL32V1 (port of gen_diag118.py to L = 3/2, K series terms, prime\n'
     'powers 2, 3, 4): exact-rational mirror of the Lean definitions. Emits the E tables and the\n'
     'outward-rounded boxes for cvsEntry M (3/2) n n, n = 0..N-1.  usage: gen_diag32.py [K] [N]"""') + t[d1:]
sub1('S64, S48 = 2**64, 2**48\n', 'S64, S48 = 2**64, 2**48\nK = int(sys.argv[1]) if len(sys.argv) > 1 else 300\n'
     'N = int(sys.argv[2]) if len(sys.argv) > 2 else 151\n')
t = re.sub(r'e1116Lo = F\(\d+, \d+\)', 'e34Lo = F(146190367214327850032107338, 309485009821345068724781056)', t)
t = re.sub(r'e1116Hi = F\(\d+, \d+\)', 'e34Hi = F(73095183607163925016053672, 154742504910672534362390528)', t)
t = t.replace('e1116', 'e34')
sub1('aK = F(159, 2)', 'aK = F(4 * K - 1, 2)')
assert t.count('range(40)') == 7, t.count('range(40)')
t = t.replace('range(40)', 'range(K)')
sub1('Ehi(40)', 'Ehi(K)', 2)
t = t.replace('F(11, 8)', 'F(3, 2)')
t, n8 = re.subn(r'8 \* (l[23](?:Lo|Hi)) / 11', r'2 * \1 / 3', t); assert n8 == 4
sub1('16 * n * lLo / 11 + F(1, 2), 16 * n * lHi / 11 + F(1, 2)', '4 * n * lLo / 3 + F(1, 2), 4 * n * lHi / 3 + F(1, 2)')
sub1('(16 * piLo * n / 11) ** 2', '(4 * piLo * n / 3) ** 2'); sub1('(16 * piHi * n / 11) ** 2', '(4 * piHi * n / 3) ** 2')
sub1('def ql(n):', '''cf4Lo, cf4Hi = F(3, 2) * l2Lo * (1 - 4 * l2Hi / 3), F(3, 2) * l2Hi * (1 - 4 * l2Lo / 3)
def co4(n): return 8 * n * l2Lo / 3 + F(1, 2), 8 * n * l2Hi / 3 + F(1, 2)
def P4Lo(n): c4 = sinPiLo(*co4(n)); return min(cf4Lo * c4, cf4Hi * c4)
def P4Hi(n): c4 = sinPiHi(*co4(n)); return max(cf4Lo * c4, cf4Hi * c4)
def ql(n):''')
sub1('2 * DLo(ql(n), qh(n)) - PdHi(n)', '2 * DLo(ql(n), qh(n)) - PdHi(n) - P4Hi(n)')
sub1('2 * DHi(ql(n), qh(n)) - PdLo(n)', '2 * DHi(ql(n), qh(n)) - PdLo(n) - P4Lo(n)')
sub1('for n in range(71):', 'for n in range(N):')
sub1('abs(thLo(co(n, l3Lo, l3Hi)[0])) <= 2\n', 'abs(thLo(co(n, l3Lo, l3Hi)[0])) <= 2 and abs(thLo(co4(n)[0])) <= 2\n')
sub1('for n in (0, 1, 2, 35, 70):', 'for n in [m for m in (0, 1, 2, 75, 150) if m < N]:')
sub1('r = 16 * mp.pi * n / 11; L = mp.mpf(11) / 8', 'r = 4 * mp.pi * n / 3; L = mp.mpf(3) / 2')
sub1('* mp.cos(2 * mp.pi * n / L * mp.log(3)))', '* mp.cos(2 * mp.pi * n / L * mp.log(3)) +\n'
     '                 mp.log(2) * (1 - 2 * mp.log(2) / L) * mp.cos(2 * mp.pi * n / L * 2 * mp.log(2)))')
sub1('print(f"-- worst entry width {worst:.3e}", file=sys.stderr)', 'print(f"-- K={K} N={N} worst entry width {worst:.3e}", file=sys.stderr)')
left = [l for l in t.split('\n') if re.search(r'(?<![\d.*])(11|16|40|70|71|118)(?![\d.])', l)]
(out / 'gen_diag32.py').write_text(t)
print('written gen_diag32.py; lines still mentioning old constants:'); [print('   ', l[:150]) for l in left]
