"""Derive the L = 49/32, M = 4, K = 156 trace modules from the L = 11/8 ones by literal substitution
(derived from ../20261110_window_l32_trace_port_v1/port_trace_l32.py).
usage: python3 port_trace_l4932.py REPO OUTDIR
Writes CvSTraceDistK156V1.lean, CvSTraceCellL4932V1.lean, CvSTraceIntegralL4932V1.lean. Untrusted; the kernel decides.
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


K = [('70', '156'), ('139', '311'), ('141', '313'), ('69', '155')]
L = [('11 / 16', '49 / 64'), ('11 / 8', '49 / 32'), ('8 / 11', '32 / 49'), ('121 / 64', '2401 / 1024'),
     ('19 / 8', '81 / 32'), ('3 / 8', '17 / 32')]

# --- the trace coefficients and families for 311 atoms -------------------------------------------
t = (F / 'CvSTraceDistV1.lean').read_text()
t = lit(t, [('CvSTraceDistV1', 'CvSTraceDistK156V1')])
t = num(t, K)
(out / 'CvSTraceDistK156V1.lean').write_text(t)

# --- one cell ------------------------------------------------------------------------------------
t = (F / 'CvSTraceCellL118V1.lean').read_text()
t = lit(t, [('import CvSTauL118V1', 'import CvSExpL4932V1\nimport CvSTraceM4SlackV1\nimport CvSTraceDistK156V1'),
            ('open AEGIS.CvSTauL118V1 (e1116Lo e1116Hi e1116_bounds)',
             'open AEGIS.CvSExpL4932V1 (e4964Lo e4964Hi e4964_bounds)\nopen AEGIS.CvSTraceM4SlackV1'),
            ('AEGIS.CvSTraceDistV1', 'AEGIS.CvSTraceDistK156V1'),
            ('CvSTraceCellL118V1', 'CvSTraceCellL4932V1'), ('e1116', 'e4964'), ('h118', 'h4932'),
            ('16 * piLo / 11', '64 * piLo / 49'), ('ScertM 3', 'ScertM 4'),
            ('w2Hi + w3Hi', 'w2Hi + w3Hi + w4Hi'), ('L = 11/8', 'L = 49/32')])
t = lit(t, [('scertM_three_ge', 'scertM_four_ge')], must=False)
t = num(num(t, L), K)
(out / 'CvSTraceCellL4932V1.lean').write_text(t)

# --- the integral and the premises ---------------------------------------------------------------
t = (F / 'CvSTraceIntegralL118V1.lean').read_text()
t = lit(t, [('AEGIS.CvSTraceDistV1', 'AEGIS.CvSTraceDistK156V1'),
            ('open AEGIS.CvSTauL12V1\n', 'open AEGIS.CvSTauL12V1\nopen AEGIS.CvSTraceM4SlackV1\n'),
            ('CvSTraceCellL118V1', 'CvSTraceCellL4932V1'), ('CvSTraceIntegralL118V1', 'CvSTraceIntegralL4932V1'),
            ('h118', 'h4932'), ('ScertM 3', 'ScertM 4'), ('w2Hi + w3Hi', 'w2Hi + w3Hi + w4Hi'),
            ('scertM_three_ge', 'scertM_four_ge'),
            ('(hT : T ≤ 7 / 2)', '(hT : T ≤ 3)'), ('    58 ≤ (2 * Real.pi)', '    66 ≤ (2 * Real.pi)'),
            ('363 / 40 * Real.pi ^ 2 - 11 / 4 * T * Real.pi', '1617 / 160 * Real.pi ^ 2 - 49 / 16 * T * Real.pi'),
            ('have hT\' : (T : ℝ) ≤ 7 / 2', 'have hT\' : (T : ℝ) ≤ 3'),
            ('`κ = 58`, `m = 33/20` and any `T ≤ 7/2`', '`κ = 66`, `m = 33/20` and any `T ≤ 3`'),
            ('L = 11/8', 'L = 49/32')])
t = num(num(t, L), K)
(out / 'CvSTraceIntegralL4932V1.lean').write_text(t)
print('written', [p.name for p in sorted(out.glob('CvSTrace*.lean'))])
