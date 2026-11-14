"""Derive the L = 3/2, M = 4, K = 150 trace modules from the L = 11/8 ones by literal substitution.
usage: python3 port_trace_l32.py REPO OUTDIR
Writes CvSTraceDistK150V1.lean, CvSTraceCellL32V1.lean, CvSTraceIntegralL32V1.lean. Untrusted; the kernel decides.
"""
import re
import sys
from pathlib import Path

repo, out = Path(sys.argv[1]), Path(sys.argv[2])
F = repo / 'research/rh/feshbach_lean_v1'


def num(t, pairs):
    for a, b in pairs:
        t, n = re.subn(r'(?<![\d.])' + re.escape(a) + r'(?![\d.])', b, t)
    return t


def lit(t, pairs, must=True):
    for a, b in pairs:
        assert (a in t) or not must, a
        t = t.replace(a, b)
    return t


K = [('70', '150'), ('139', '299'), ('141', '301'), ('69', '149')]
L = [('11 / 16', '3 / 4'), ('11 / 8', '3 / 2'), ('8 / 11', '2 / 3'), ('121 / 64', '9 / 4'),
     ('19 / 8', '5 / 2'), ('3 / 8', '1 / 2')]

# --- the trace coefficients and families for 299 atoms -------------------------------------------
t = (F / 'CvSTraceDistV1.lean').read_text()
t = lit(t, [('CvSTraceDistV1', 'CvSTraceDistK150V1')])
t = num(t, K)
(out / 'CvSTraceDistK150V1.lean').write_text(t)

# --- one cell ------------------------------------------------------------------------------------
t = (F / 'CvSTraceCellL118V1.lean').read_text()
t = lit(t, [('import CvSTauL118V1', 'import CvSExpL32V1\nimport CvSTraceM4SlackV1\nimport CvSTraceDistK150V1'),
            ('open AEGIS.CvSTauL118V1 (e1116Lo e1116Hi e1116_bounds)',
             'open AEGIS.CvSExpL32V1 (e34Lo e34Hi e34_bounds)\nopen AEGIS.CvSTraceM4SlackV1'),
            ('AEGIS.CvSTraceDistV1', 'AEGIS.CvSTraceDistK150V1'),
            ('CvSTraceCellL118V1', 'CvSTraceCellL32V1'), ('e1116', 'e34'), ('h118', 'h32'),
            ('16 * piLo / 11', '4 * piLo / 3'), ('ScertM 3', 'ScertM 4'),
            ('w2Hi + w3Hi', 'w2Hi + w3Hi + w4Hi'), ('L = 11/8', 'L = 3/2')])
t = lit(t, [('scertM_three_ge', 'scertM_four_ge')], must=False)
t = num(num(t, L), K)
(out / 'CvSTraceCellL32V1.lean').write_text(t)

# --- the integral and the premises ---------------------------------------------------------------
t = (F / 'CvSTraceIntegralL118V1.lean').read_text()
t = lit(t, [('AEGIS.CvSTraceDistV1', 'AEGIS.CvSTraceDistK150V1'),
            ('open AEGIS.CvSTauL12V1\n', 'open AEGIS.CvSTauL12V1\nopen AEGIS.CvSTraceM4SlackV1\n'),
            ('CvSTraceCellL118V1', 'CvSTraceCellL32V1'), ('CvSTraceIntegralL118V1', 'CvSTraceIntegralL32V1'),
            ('h118', 'h32'), ('ScertM 3', 'ScertM 4'), ('w2Hi + w3Hi', 'w2Hi + w3Hi + w4Hi'),
            ('scertM_three_ge', 'scertM_four_ge'),
            ('(hT : T ≤ 7 / 2)', '(hT : T ≤ 3)'), ('    58 ≤ (2 * Real.pi)', '    66 ≤ (2 * Real.pi)'),
            ('363 / 40 * Real.pi ^ 2 - 11 / 4 * T * Real.pi', '99 / 10 * Real.pi ^ 2 - 3 * T * Real.pi'),
            ('have hT\' : (T : ℝ) ≤ 7 / 2', 'have hT\' : (T : ℝ) ≤ 3'),
            ('`κ = 58`, `m = 33/20` and any `T ≤ 7/2`', '`κ = 66`, `m = 33/20` and any `T ≤ 3`'),
            ('L = 11/8', 'L = 3/2')])
t = num(num(t, L), K)
(out / 'CvSTraceIntegralL32V1.lean').write_text(t)
print('written', [p.name for p in sorted(out.glob('CvSTrace*.lean'))])
