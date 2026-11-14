"""Port one lab module CvSRelRow<M>L118V1.lean to L = 49/32 by whole-number token rules (per module), plain
string rules, and a check that no listed 11/8 constant is left (port_mod.py of
../20261112_window_l32_rowcert_v1/ with port_rules4932.json). usage: port_mod4932.py REPO OUTDIR M"""
import json
import re
import sys
from pathlib import Path
repo, out, M = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
rules = json.load(open(Path(__file__).parent / 'port_rules4932.json'))[M]
t = (repo / f'research/rh/feshbach_lean_v1/CvSRelRow{M}L118V1.lean').read_text()
for a, b, n in rules.get('str', []):
    c = t.count(a)
    assert c == n, (M, a, c, n)
    t = t.replace(a, b)
tok = rules.get('tok', {})
if tok:
    pat = re.compile(r'(?<!\^ )(?<![\d.\w^])(' + '|'.join(sorted(map(re.escape, tok), key=len, reverse=True)) + r')(?![\d\w])')
    t = pat.sub(lambda m: tok[m.group(1)], t)
t = t.replace('`L = 11/8`', '`L = 49/32`').replace('(11/8)', '(49/32)').replace('11 / 8', '49 / 32').replace('L118V1', 'L4932V1')
t = t.replace('CvSTauR1PrimeL4932V1', 'CvSTauL4932AllV1')
bad = rules.get('forbid', [])
left = [l for l in t.split('\n') if any(re.search(r'(?<![\d.\w])' + re.escape(x) + r'(?![\d\w])', l) for x in bad)]
assert not left, (M, left[:6])
(out / f'CvSRelRow{M}L4932V1.lean').write_text(t)
print('ported', M)
