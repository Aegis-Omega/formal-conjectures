"""Derive make_gen_diag4932.py and port_diag_l4932.py (diagonal at L = 49/32) from the L = 3/2 scripts
make_gen_diag32.py and port_diag_l32.py of ../20261111_window_l32_diagonal_v1/ by counted substitution.
usage: python3 make_diag_ports4932.py L32_DIAG_DIR OUTDIR
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


port('make_gen_diag32.py', 'make_gen_diag4932.py', [
    ('"""Derive gen_diag32.py (untrusted mirror for CvSDiagL32V1, window L = 3/2,',
     '"""Derive gen_diag4932.py (untrusted mirror for CvSDiagL4932V1, window L = 49/32,'),
    ('usage: python3 make_gen_diag32.py REPO OUTDIR', 'usage: python3 make_gen_diag4932.py REPO OUTDIR\n(derived from ../20261111_window_l32_diagonal_v1/make_gen_diag32.py)'),
    ("'\"\"\"Untrusted generator for CvSDiagL32V1 (port of gen_diag118.py to L = 3/2,",
     "'\"\"\"Untrusted generator for CvSDiagL4932V1 (port of gen_diag118.py to L = 49/32,"),
    ("'outward-rounded boxes for cvsEntry M (3/2) n n, n = 0..N-1.  usage: gen_diag32.py [K] [N]\"\"\"'",
     "'outward-rounded boxes for cvsEntry M (49/32) n n, n = 0..N-1.  usage: gen_diag4932.py [K] [N]\"\"\"'"),
    ("'N = int(sys.argv[2]) if len(sys.argv) > 2 else 151\\n'", "'N = int(sys.argv[2]) if len(sys.argv) > 2 else 157\\n'"),
    ("'e34Lo = F(146190367214327850032107338, 309485009821345068724781056)'",
     "'e4964Lo = F(143923895647018040563762077, 309485009821345068724781056)'"),
    ("'e34Hi = F(73095183607163925016053672, 154742504910672534362390528)'",
     "'e4964Hi = F(4497621738969313767617565, 9671406556917033397649408)'"),
    ("t = t.replace('e1116', 'e34')", "t = t.replace('e1116', 'e4964')"),
    ("t = t.replace('F(11, 8)', 'F(3, 2)')", "t = t.replace('F(11, 8)', 'F(49, 32)')"),
    ("r'2 * \\1 / 3'", "r'32 * \\1 / 49'"),
    ("'4 * n * lLo / 3 + F(1, 2), 4 * n * lHi / 3 + F(1, 2)'", "'64 * n * lLo / 49 + F(1, 2), 64 * n * lHi / 49 + F(1, 2)'"),
    ("'(4 * piLo * n / 3) ** 2'", "'(64 * piLo * n / 49) ** 2'"), ("'(4 * piHi * n / 3) ** 2'", "'(64 * piHi * n / 49) ** 2'"),
    ("cf4Lo, cf4Hi = F(3, 2) * l2Lo * (1 - 4 * l2Hi / 3), F(3, 2) * l2Hi * (1 - 4 * l2Lo / 3)",
     "cf4Lo, cf4Hi = F(49, 32) * l2Lo * (1 - 64 * l2Hi / 49), F(49, 32) * l2Hi * (1 - 64 * l2Lo / 49)"),
    ("def co4(n): return 8 * n * l2Lo / 3 + F(1, 2), 8 * n * l2Hi / 3 + F(1, 2)",
     "def co4(n): return 128 * n * l2Lo / 49 + F(1, 2), 128 * n * l2Hi / 49 + F(1, 2)"),
    ("(0, 1, 2, 75, 150)", "(0, 1, 2, 78, 156)"),
    ("'r = 4 * mp.pi * n / 3; L = mp.mpf(3) / 2'", "'r = 64 * mp.pi * n / 49; L = mp.mpf(49) / 32'"),
    ("(out / 'gen_diag32.py')", "(out / 'gen_diag4932.py')"), ("print('written gen_diag32.py;", "print('written gen_diag4932.py;")])

port('port_diag_l32.py', 'port_diag_l4932.py', [
    ('"""Build CvSDiagL32V1.lean (diagonal of the L = 3/2 low block)', '"""Build CvSDiagL4932V1.lean (diagonal of the L = 49/32 low block)'),
    ('mechanical substitution (window 11/8 -> 3/2,', 'mechanical substitution (window 11/8 -> 49/32,'),
    ('hand-written third prime-power term (4 = 2^2, log 4 < 3/2) and the data emitted by gen_diag32.py.',
     'hand-written third prime-power term (4 = 2^2, log 4 < 49/32) and the data emitted by gen_diag4932.py\n(derived from ../20261111_window_l32_diagonal_v1/port_diag_l32.py).'),
    ('usage: python3 port_diag_l32.py', 'usage: python3 port_diag_l4932.py'),
    ('(Elo = 0, Ehi = e34Hi^49)', '(Elo = 0, Ehi = e4964Hi^49)'),
    ('CvSTauL32V1', 'CvSTauL4932V1'), ('CvSNodeL32V1', 'CvSNodeL4932V1'), ('CvSDiagL32V1', 'CvSDiagL4932V1'),
    ('gen_diag32.py', 'gen_diag4932.py'), ('port_diag_l32.py', 'port_diag_l4932.py'),
    ('`cvsEntry M (3/2) n n`', '`cvsEntry M (49/32) n n`'), ('L = 3/2', 'L = 49/32'),
    ('(`log 4 < 3/2`,', '(`log 4 < 49/32`,'), ('(e^{{−3/4}})^{{4k+1}}', '(e^{{−49/64}})^{{4k+1}}'),
    ('and `ω = 4πn/3`', 'and `ω = 64πn/49`'), ('`e^{{−c_k·3/2}}`', '`e^{{−c_k·49/32}}`'),
    ('`e^{{−c_{K}·3/2}}`', '`e^{{−c_{K}·49/32}}`'),
    ('(3 / 2)', '(49 / 32)'), ('(3 / 2 : ℝ)', '(49 / 32 : ℝ)'), ('3 / 2 *', '49 / 32 *'),
    ('have hL : (0 : ℝ) < 3 / 2 := by norm_num', 'have hL : (0 : ℝ) < 49 / 32 := by norm_num'),
    ('4 * l2Hi / 3', '64 * l2Hi / 49'), ('4 * l2Lo / 3', '64 * l2Lo / 49'),
    ('4 * (l2Hi : ℝ) / 3', '64 * (l2Hi : ℝ) / 49'), ('4 * (l2Lo : ℝ) / 3', '64 * (l2Lo : ℝ) / 49'),
    ('8 * n * l2Lo / 3', '128 * n * l2Lo / 49'), ('8 * n * l2Hi / 3', '128 * n * l2Hi / 49'),
    ('8 * n * Real.log 2 / 3', '128 * n * Real.log 2 / 49'),
    ("s = s.replace('11 / 8', '3 / 2').replace('11/8', '3/2')", "s = s.replace('11 / 8', '49 / 32').replace('11/8', '49/32')"),
    ("r'2 * \\1 / 3'", "r'32 * \\1 / 49'"), ("r'4 * \\1 / 3'", "r'64 * \\1 / 49'"),
    ("s.replace('CvSDiagL118V1', 'CvSDiagL4932V1')", "s.replace('CvSDiagL118V1', 'CvSDiagL4932V1')")])
