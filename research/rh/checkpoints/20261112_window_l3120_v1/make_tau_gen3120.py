"""Derive gen_tau3120f.py, build_tau3120.py and assemble_tau3120.py (L = 31/20, k <= 2000, low boxes for
k <= 156) from the L = 3/2 scripts of ../20261111_window_l32_tau_v1/ by counted literal substitution.
usage: python3 make_tau_gen3120.py L32_TAU_DIR OUTDIR
"""
import sys
from fractions import Fraction as F
from math import floor
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])
lo = F(142580914187195743784704817, 309485009821345068724781056)
hi = F(4455653568349866993272026, 9671406556917033397649408)
NElo = [floor((1 - hi ** (4 * min(j, 12) + 1)) * 2 ** 64) for j in range(13)]


def port(name, newname, reps):
    t = (src / name).read_text()
    for a, b in reps:
        n = t.count(a)
        assert n >= 1, (name, a)
        t = t.replace(a, b)
    (out / newname).write_text(t)
    print(newname, 'substitutions', len(reps))


common = [('L = 3/2', 'L = 31/20'), ('tau M (3 / 2)', 'tau M (31 / 20)'), ('CvSNodeL32V1.lean', 'CvSNodeL3120V1.lean')]
port('gen_tau32f.py', 'gen_tau3120f.py', [
    ('CvSTauFastL32V1.tauF (window L = 3/2', 'CvSTauFastL3120V1.tauF (window L = 31/20'),
    ('gen_tau32f.py K1 K2', 'gen_tau3120f.py K1 K2'),
    ('314159265358979323847, 3 * 10 ** 20', '314159265358979323847, 31 * 10 ** 20'),
    ('e34Lo = F(146190367214327850032107338, 309485009821345068724781056)',
     f'e3140Lo = F({lo.numerator}, {lo.denominator})'),
    ('e34Hi = F(73095183607163925016053672, 154742504910672534362390528)',
     f'e3140Hi = F({hi.numerator}, {hi.denominator})'),
    ('return e34Hi ** ', 'return e3140Hi ** '), ('return e34Lo ** ', 'return e3140Lo ** '),
    ('assert NEloT == [9733119166315628212, 18012918234713208232, 18425145157003694732, 18445668726966845320, 18446690535347753337, 18446741408191472461, 18446743941001220773, 18446744067102392875, 18446744073380600552, 18446744073693174106, 18446744073708736227, 18446744073709511020, 18446744073709549594]',
     'assert NEloT == ' + repr(NElo)),
    ('def omLo(k): return 4 * piLo * k / 3', 'def omLo(k): return 40 * piLo * k / 31'),
    ('def omHi(k): return 4 * piHi * k / 3', 'def omHi(k): return 40 * piHi * k / 31'),
    ('a, b = 4 * pLoN * k, 4 * pHiN * k', 'a, b = 40 * pLoN * k, 40 * pHiN * k'),
    ('(4 * k * l2Lo / 3, 4 * k * l2Hi / 3, w2Lo, w2Hi), (4 * k * l3Lo / 3, 4 * k * l3Hi / 3, w3Lo, w3Hi)',
     '(40 * k * l2Lo / 31, 40 * k * l2Hi / 31, w2Lo, w2Hi), (40 * k * l3Lo / 31, 40 * k * l3Hi / 31, w3Lo, w3Hi)'),
    ('(8 * k * l2Lo / 3, 8 * k * l2Hi / 3, l2Lo, l2Hi)', '(80 * k * l2Lo / 31, 80 * k * l2Hi / 31, l2Lo, l2Hi)'),
    ('w = 4 * math.pi * k / 3', 'w = 40 * math.pi * k / 31'),
    ('def tgt_of(k): return 3e-10 if k <= 150 else 3e-9', 'def tgt_of(k): return 3e-11 if k <= 156 else 3e-9'),
    ('w = 4 * mp.pi * k / 3; L = mp.mpf(3) / 2', 'w = 40 * mp.pi * k / 31; L = mp.mpf(31) / 20'),
    ('mp.sin(mp.pi * 4 * k * mp.log(2) / 3)', 'mp.sin(mp.pi * 40 * k * mp.log(2) / 31)'),
    ('mp.sin(mp.pi * 4 * k * mp.log(3) / 3)', 'mp.sin(mp.pi * 40 * k * mp.log(3) / 31)'),
    ('mp.sin(mp.pi * 8 * k * mp.log(2) / 3)', 'mp.sin(mp.pi * 80 * k * mp.log(2) / 31)')])
port('build_tau32.py', 'build_tau3120.py', common + [
    ('CvSTauL32K', 'CvSTauL3120K'), ('import gen_tau32f as g', 'import gen_tau3120f as g'),
    ('gen_tau32f.py', 'gen_tau3120f.py'), ('CvSTauFastL32V1', 'CvSTauFastL3120V1'),
    ('usage: python3 build_tau32.py', 'usage: python3 build_tau3120.py')])
port('assemble_tau32.py', 'assemble_tau3120.py', common + [
    ('CvSTauL32AllV1', 'CvSTauL3120AllV1'), ('CvSTauL32K', 'CvSTauL3120K'),
    ('range(1, 901, 50)', 'range(1, 2001, 50)'),
    ('k = 1..900 from the 18 data modules\nCvSTauL3120K{1,51,...,851}V1', 'k = 1..2000 from the 40 data modules\nCvSTauL3120K{1,51,...,1951}V1'),
    ('usage: python3 assemble_tau32.py', 'usage: python3 assemble_tau3120.py'),
    ('`k = 1, …, 900`', '`k = 1, …, 2000`'),
    ('The eighteen data modules `CvSTauL3120K{1, 51, …, 851}V1`', 'The forty data modules `CvSTauL3120K{1, 51, …, 1951}V1`'),
    ('`1.0·10⁻¹⁰` for `k ≤ 150` and `1.0·10⁻⁹` for `150 < k ≤ 900` (the row-check budget of\n`ROW_BOXES_20261111.md`',
     '`1.0·10⁻¹¹` for `k ≤ 156` and `1.0·10⁻⁹` for `156 < k ≤ 2000` (the row-check budget of\n`../20261112_window_l3120_v1/FEASIBILITY_3120.log`'),
    ('1 ≤ k ≤ 900', '1 ≤ k ≤ 2000'), ('(h2 : k ≤ 900)', '(h2 : k ≤ 2000)'),
    ('radius `5·10⁻¹¹` and `5·10⁻¹⁰`', 'radius `5·10⁻¹²` and `5·10⁻¹⁰`')])
