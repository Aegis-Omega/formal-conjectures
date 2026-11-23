"""Derive make_gen_diag3120.py and port_diag_l3120.py (diagonal at L = 31/20) from the L = 3/2 scripts
make_gen_diag32.py and port_diag_l32.py of ../20261111_window_l32_diagonal_v1/ by counted substitution.
usage: python3 make_diag_ports3120.py L32_DIAG_DIR OUTDIR
"""
import sys
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])


def port(name, newname, reps):
    t = (src / name).read_text()
    for a, b in reps:
        assert a in t, (name, a)
        t = t.replace(a, b)
    (out / newname).write_text(t)
    print(newname, len(reps), 'substitutions')


port('make_gen_diag32.py', 'make_gen_diag3120.py', [
    ('"""Derive gen_diag32.py (untrusted mirror for CvSDiagL32V1, window L = 3/2,',
     '"""Derive gen_diag3120.py (untrusted mirror for CvSDiagL3120V1, window L = 31/20,'),
    ('usage: python3 make_gen_diag32.py REPO OUTDIR', 'usage: python3 make_gen_diag3120.py REPO OUTDIR\n(derived from ../20261111_window_l32_diagonal_v1/make_gen_diag32.py)'),
    ("'\"\"\"Untrusted generator for CvSDiagL32V1 (port of gen_diag118.py to L = 3/2,",
     "'\"\"\"Untrusted generator for CvSDiagL3120V1 (port of gen_diag118.py to L = 31/20,"),
    ("'outward-rounded boxes for cvsEntry M (3/2) n n, n = 0..N-1.  usage: gen_diag32.py [K] [N]\"\"\"'",
     "'outward-rounded boxes for cvsEntry M (31/20) n n, n = 0..N-1.  usage: gen_diag3120.py [K] [N]\"\"\"'"),
    ("'N = int(sys.argv[2]) if len(sys.argv) > 2 else 151\\n'", "'N = int(sys.argv[2]) if len(sys.argv) > 2 else 157\\n'"),
    ("'e34Lo = F(146190367214327850032107338, 309485009821345068724781056)'",
     "'e3140Lo = F(142580914187195743784704817, 309485009821345068724781056)'"),
    ("'e34Hi = F(73095183607163925016053672, 154742504910672534362390528)'",
     "'e3140Hi = F(4455653568349866993272026, 9671406556917033397649408)'"),
    ("t = t.replace('e1116', 'e34')", "t = t.replace('e1116', 'e3140')"),
    ("t = t.replace('F(11, 8)', 'F(3, 2)')", "t = t.replace('F(11, 8)', 'F(31, 20)')"),
    ("r'2 * \\1 / 3'", "r'20 * \\1 / 31'"),
    ("'4 * n * lLo / 3 + F(1, 2), 4 * n * lHi / 3 + F(1, 2)'", "'40 * n * lLo / 31 + F(1, 2), 40 * n * lHi / 31 + F(1, 2)'"),
    ("'(4 * piLo * n / 3) ** 2'", "'(40 * piLo * n / 31) ** 2'"), ("'(4 * piHi * n / 3) ** 2'", "'(40 * piHi * n / 31) ** 2'"),
    ("cf4Lo, cf4Hi = F(3, 2) * l2Lo * (1 - 4 * l2Hi / 3), F(3, 2) * l2Hi * (1 - 4 * l2Lo / 3)",
     "cf4Lo, cf4Hi = F(31, 20) * l2Lo * (1 - 40 * l2Hi / 31), F(31, 20) * l2Hi * (1 - 40 * l2Lo / 31)"),
    ("def co4(n): return 8 * n * l2Lo / 3 + F(1, 2), 8 * n * l2Hi / 3 + F(1, 2)",
     "def co4(n): return 80 * n * l2Lo / 31 + F(1, 2), 80 * n * l2Hi / 31 + F(1, 2)"),
    ("(0, 1, 2, 75, 150)", "(0, 1, 2, 78, 156)"),
    ("'r = 4 * mp.pi * n / 3; L = mp.mpf(3) / 2'", "'r = 40 * mp.pi * n / 31; L = mp.mpf(31) / 20'"),
    ("(out / 'gen_diag32.py')", "(out / 'gen_diag3120.py')"), ("print('written gen_diag32.py;", "print('written gen_diag3120.py;")])

port('port_diag_l32.py', 'port_diag_l3120.py', [
    ('"""Build CvSDiagL32V1.lean (diagonal of the L = 3/2 low block)', '"""Build CvSDiagL3120V1.lean (diagonal of the L = 31/20 low block)'),
    ('mechanical substitution (window 11/8 -> 3/2,', 'mechanical substitution (window 11/8 -> 31/20,'),
    ('hand-written third prime-power term (4 = 2^2, log 4 < 3/2) and the data emitted by gen_diag32.py.',
     'hand-written third prime-power term (4 = 2^2, log 4 < 31/20) and the data emitted by gen_diag3120.py\n(derived from ../20261111_window_l32_diagonal_v1/port_diag_l32.py).'),
    ('usage: python3 port_diag_l32.py', 'usage: python3 port_diag_l3120.py'),
    ('(Elo = 0, Ehi = e34Hi^49)', '(Elo = 0, Ehi = e3140Hi^49)'),
    ('CvSTauL32V1', 'CvSTauL3120V1'), ('CvSNodeL32V1', 'CvSNodeL3120V1'), ('CvSDiagL32V1', 'CvSDiagL3120V1'),
    ('gen_diag32.py', 'gen_diag3120.py'), ('port_diag_l32.py', 'port_diag_l3120.py'),
    ('`cvsEntry M (3/2) n n`', '`cvsEntry M (31/20) n n`'), ('L = 3/2', 'L = 31/20'),
    ('(`log 4 < 3/2`,', '(`log 4 < 31/20`,'), ('(e^{{−3/4}})^{{4k+1}}', '(e^{{−31/40}})^{{4k+1}}'),
    ('and `ω = 4πn/3`', 'and `ω = 40πn/31`'), ('`e^{{−c_k·3/2}}`', '`e^{{−c_k·31/20}}`'),
    ('`e^{{−c_{K}·3/2}}`', '`e^{{−c_{K}·31/20}}`'),
    ('(3 / 2)', '(31 / 20)'), ('(3 / 2 : ℝ)', '(31 / 20 : ℝ)'), ('3 / 2 *', '31 / 20 *'),
    ('have hL : (0 : ℝ) < 3 / 2 := by norm_num', 'have hL : (0 : ℝ) < 31 / 20 := by norm_num'),
    ('4 * l2Hi / 3', '40 * l2Hi / 31'), ('4 * l2Lo / 3', '40 * l2Lo / 31'),
    ('4 * (l2Hi : ℝ) / 3', '40 * (l2Hi : ℝ) / 31'), ('4 * (l2Lo : ℝ) / 3', '40 * (l2Lo : ℝ) / 31'),
    ('8 * n * l2Lo / 3', '80 * n * l2Lo / 31'), ('8 * n * l2Hi / 3', '80 * n * l2Hi / 31'),
    ('8 * n * Real.log 2 / 3', '80 * n * Real.log 2 / 31'),
    ("s = s.replace('11 / 8', '3 / 2').replace('11/8', '3/2')", "s = s.replace('11 / 8', '31 / 20').replace('11/8', '31/20')"),
    ("r'2 * \\1 / 3'", "r'20 * \\1 / 31'"), ("r'4 * \\1 / 3'", "r'40 * \\1 / 31'"),
    ("s.replace('CvSDiagL118V1', 'CvSDiagL3120V1')", "s.replace('CvSDiagL118V1', 'CvSDiagL3120V1')")])


p = out / 'port_diag_l3120.py'
L = p.read_text().split('\n')
i = [k for k, l in enumerate(L) if l.startswith("    s, _ = re.subn(r'8 ")]
assert len(i) == 1 and L[i[0] + 1].startswith("    s, _ = re.subn(r'16 "), i
i = i[0]
assert [l[:30] for l in L[i + 2:i + 5]] == ["    s = re.sub(r'(?<![\\d.])40(", "    s = re.sub(r'(?<![\\d.])71(",
                                            "    s = re.sub(r'(?<![\\d.])70("], L[i + 2:i + 5]
L[i:i + 5] = L[i + 2:i + 5] + L[i:i + 2]
p.write_text('\n'.join(L))
print('port_diag_l3120.py: K and N substituted before 2/LT')
