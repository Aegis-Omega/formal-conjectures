"""Derive CvSTauL3120V1.lean (source integrals at L = 31/20) from the lab's CvSTauL118V1.lean (L = 11/8),
as ../20261111_window_l32_diagonal_v1/port_tau_l32.py does at L = 3/2.
Mechanical substitution; the exponential enclosure comes from CvSExpL3120V1.e3140_bounds.
usage: python3 port_tau_l3120.py REPO OUTDIR
"""
import re
import sys
from pathlib import Path

repo, out = Path(sys.argv[1]), Path(sys.argv[2])
t = (repo / 'research/rh/feshbach_lean_v1/CvSTauL118V1.lean').read_text()
# drop the local exp enclosure (defs + theorem), use CvSExpL3120V1 instead
a = t.index('def e1116Lo'); b = t.index('theorem exp_width')
t = t[:a] + t[b:]
d0 = t.index('/-!\n# Kernel check'); d1 = t.index('-/', d0) + 2
doc = '''/-!
# Kernel check for the source integrals at `L = 31/20`

The check of `CvSTauL118V1` with the window moved to `L = 31/20`: `e^{−31/40}` from
`CvSExpL3120V1.e3140_bounds`, `e^{−c_j L} = (e^{−31/40})^{4j+1}` and `ω_k = 40πk/31`. The rational `π`
bounds, the outward rounding, the arctan partial sums and the term bounds are those of
`CvSTauL12V1`. `tauCheck_sound` turns a passing check into `lo ≤ ∫ h₊ S_k ≤ hi`. Generated
mechanically by `port_tau_l3120.py` from the lab source; proofs unchanged. No `native_decide`. Not RH.
-/'''
t = t[:d0] + doc + t[d1:]
t = t.replace('import CvSTauL12V1\n', 'import CvSTauL12V1\nimport CvSExpL3120V1\n', 1)
t = t.replace('  atPartial_cast term_lo term_hi)\n', '  atPartial_cast term_lo term_hi)\nopen AEGIS.CvSExpL3120V1 (e3140Lo e3140Hi e3140_bounds)\n', 1)
t = t.replace('#print axioms AEGIS.CvSTauL118V1.e1116_bounds\n', '')
for x, y in [('e1116Lo', 'e3140Lo'), ('e1116Hi', 'e3140Hi'), ('e1116_bounds', 'e3140_bounds'),
             ('-11 / 16', '-31 / 40'), ('11 / 8', '31 / 20'), ('11/8', '31/20'), ('CvSTauL118V1', 'CvSTauL3120V1')]:
    t = t.replace(x, y)
t, n16 = re.subn(r'16 \* ([^\n/]{1,30}?) / 11', r'40 * \1 / 31', t)
left = [l for l in t.split('\n')[16:] if re.search(r'(?<![\d.])(11|16|118)(?![\d.])', l)]
assert not left, left
(out / 'CvSTauL3120V1.lean').write_text(t)
print('written CvSTauL3120V1.lean lines', t.count('\n'), 'omega substitutions', n16)
