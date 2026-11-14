"""Derive gen_tau4932f.py, build_tau4932.py and assemble_tau4932.py (L = 49/32, k <= 2000, low boxes for
k <= 156) from the L = 3/2 scripts of ../20261111_window_l32_tau_v1/ by counted literal substitution.
usage: python3 make_tau_gen4932.py L32_TAU_DIR OUTDIR
"""
import sys
from fractions import Fraction as F
from math import floor
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])
lo = F(143923895647018040563762077, 309485009821345068724781056)
hi = F(4497621738969313767617565, 9671406556917033397649408)
NElo = [floor((1 - hi ** (4 * min(j, 12) + 1)) * 2 ** 64) for j in range(13)]


def port(name, newname, reps):
    t = (src / name).read_text()
    for a, b in reps:
        n = t.count(a)
        assert n >= 1, (name, a)
        t = t.replace(a, b)
    (out / newname).write_text(t)
    print(newname, 'substitutions', len(reps))


common = [('L = 3/2', 'L = 49/32'), ('tau M (3 / 2)', 'tau M (49 / 32)'), ('CvSNodeL32V1.lean', 'CvSNodeL4932V1.lean')]
port('gen_tau32f.py', 'gen_tau4932f.py', [
    ('CvSTauFastL32V1.tauF (window L = 3/2', 'CvSTauFastL4932V1.tauF (window L = 49/32'),
    ('gen_tau32f.py K1 K2', 'gen_tau4932f.py K1 K2'),
    ('314159265358979323847, 3 * 10 ** 20', '314159265358979323847, 49 * 10 ** 20'),
    ('e34Lo = F(146190367214327850032107338, 309485009821345068724781056)',
     f'e4964Lo = F({lo.numerator}, {lo.denominator})'),
    ('e34Hi = F(73095183607163925016053672, 154742504910672534362390528)',
     f'e4964Hi = F({hi.numerator}, {hi.denominator})'),
    ('return e34Hi ** ', 'return e4964Hi ** '), ('return e34Lo ** ', 'return e4964Lo ** '),
    ('assert NEloT == [9733119166315628212, 18012918234713208232, 18425145157003694732, 18445668726966845320, 18446690535347753337, 18446741408191472461, 18446743941001220773, 18446744067102392875, 18446744073380600552, 18446744073693174106, 18446744073708736227, 18446744073709511020, 18446744073709549594]',
     'assert NEloT == ' + repr(NElo)),
    ('def omLo(k): return 4 * piLo * k / 3', 'def omLo(k): return 64 * piLo * k / 49'),
    ('def omHi(k): return 4 * piHi * k / 3', 'def omHi(k): return 64 * piHi * k / 49'),
    ('a, b = 4 * pLoN * k, 4 * pHiN * k', 'a, b = 64 * pLoN * k, 64 * pHiN * k'),
    ('(4 * k * l2Lo / 3, 4 * k * l2Hi / 3, w2Lo, w2Hi), (4 * k * l3Lo / 3, 4 * k * l3Hi / 3, w3Lo, w3Hi)',
     '(64 * k * l2Lo / 49, 64 * k * l2Hi / 49, w2Lo, w2Hi), (64 * k * l3Lo / 49, 64 * k * l3Hi / 49, w3Lo, w3Hi)'),
    ('(8 * k * l2Lo / 3, 8 * k * l2Hi / 3, l2Lo, l2Hi)', '(128 * k * l2Lo / 49, 128 * k * l2Hi / 49, l2Lo, l2Hi)'),
    ('w = 4 * math.pi * k / 3', 'w = 64 * math.pi * k / 49'),
    ('def tgt_of(k): return 3e-10 if k <= 150 else 3e-9', 'def tgt_of(k): return 3e-10 if k <= 156 else 3e-9'),
    ('w = 4 * mp.pi * k / 3; L = mp.mpf(3) / 2', 'w = 64 * mp.pi * k / 49; L = mp.mpf(49) / 32'),
    ('mp.sin(mp.pi * 4 * k * mp.log(2) / 3)', 'mp.sin(mp.pi * 64 * k * mp.log(2) / 49)'),
    ('mp.sin(mp.pi * 4 * k * mp.log(3) / 3)', 'mp.sin(mp.pi * 64 * k * mp.log(3) / 49)'),
    ('mp.sin(mp.pi * 8 * k * mp.log(2) / 3)', 'mp.sin(mp.pi * 128 * k * mp.log(2) / 49)')])
port('build_tau32.py', 'build_tau4932.py', common + [
    ('CvSTauL32K', 'CvSTauL4932K'), ('import gen_tau32f as g', 'import gen_tau4932f as g'),
    ('gen_tau32f.py', 'gen_tau4932f.py'), ('CvSTauFastL32V1', 'CvSTauFastL4932V1'),
    ('usage: python3 build_tau32.py', 'usage: python3 build_tau4932.py')])
port('assemble_tau32.py', 'assemble_tau4932.py', common + [
    ('CvSTauL32AllV1', 'CvSTauL4932AllV1'), ('CvSTauL32K', 'CvSTauL4932K'),
    ('range(1, 901, 50)', 'range(1, 2001, 50)'),
    ('k = 1..900 from the 18 data modules\nCvSTauL4932K{1,51,...,851}V1', 'k = 1..2000 from the 40 data modules\nCvSTauL4932K{1,51,...,1951}V1'),
    ('usage: python3 assemble_tau32.py', 'usage: python3 assemble_tau4932.py'),
    ('`k = 1, …, 900`', '`k = 1, …, 2000`'),
    ('The eighteen data modules `CvSTauL4932K{1, 51, …, 851}V1`', 'The forty data modules `CvSTauL4932K{1, 51, …, 1951}V1`'),
    ('`1.0·10⁻¹⁰` for `k ≤ 150` and `1.0·10⁻⁹` for `150 < k ≤ 900` (the row-check budget of\n`ROW_BOXES_20261111.md`',
     '`1.0·10⁻¹⁰` for `k ≤ 156` and `1.0·10⁻⁹` for `156 < k ≤ 2000` (the row-check budget of\n`../20261112_window_beyond_l32_feasibility_v1/`'),
    ('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)')])
