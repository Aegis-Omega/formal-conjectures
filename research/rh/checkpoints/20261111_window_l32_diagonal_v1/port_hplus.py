"""Derive CvSHplusK{K}V1.lean from CvSDiagL12V1.lean: the window-free enclosure of h+ and the
window-free pieces of the diagonal series, with K series terms instead of 40
(aK = c_K - 1 = (4K-1)/2, tail 1/(4 aK^4)).
usage: python3 port_hplus.py REPO OUTDIR K
"""
import re
import sys
from pathlib import Path

repo, out, K = Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3])
name = f'CvSHplusK{K}V1'
src = (repo / 'research/rh/feshbach_lean_v1/CvSDiagL12V1.lean').read_text().split('\n')
def idx(prefix, start=0):
    return next(i for i in range(start, len(src)) if src[i].startswith(prefix))
d0, d1 = idx('/-!'), idx('-/', idx('/-!'))          # module docstring
end = idx('  constructor <;> linarith [T.1, T.2, S.1, S.2, L1.1, L2.2, C.1, C.2]')
f0, g0 = idx('def fLo'), idx('def gDLo')
assert src[f0 + 2].startswith('def fHi') and src[g0 + 2].startswith('def gDHi')
doc = f'''/-!
# `h₊` for `r²` in a rational interval, with `K = {K}` series terms

Window-free slice of `@SRC@` (logarithms of positive rationals, interval division,
`hplus_bounds`, and the window-free pieces `fLo fHi gDLo gDHi` of the diagonal series), re-run
with `K = {K}` terms of `CvSDiagTelV1.hplus_tel` instead of `40`: `aK = c_{K} − 1 = {4*K-1}/2`, so
the telescoped tail `1/(4 aK⁴)` drops from about `6·10⁻⁹` to about `{1/(4*((4*K-1)/2)**4):.1e}`.
Generated mechanically by `port_hplus.py` from the lab source; proofs unchanged. Not RH.
-/'''.split('\n')
body = src[:d0] + doc + src[d1 + 1:end + 1] + [''] + src[f0:f0 + 4] + [''] + src[g0:g0 + 4]
t = '\n'.join(body + ['', f'end AEGIS.{name}', '', f'#print axioms AEGIS.{name}.hplus_bounds', ''])
t = t.replace('CvSDiagL12V1', name)
t = t.replace('@SRC@', 'CvSDiagL12V1')
pre, post = t[:t.index('open Finset')], t[t.index('open Finset'):]
post, n40 = re.subn(r'(?<![\d.])40(?![\d.])', str(K), post)
assert 'def aK : ℚ := 159 / 2' in post
post = post.replace('159 / 2', f'{4*K-1} / 2').replace('159/2', f'{4*K-1}/2')
(out / f'{name}.lean').write_text(pre + post)
print('written', name, 'lines', (pre + post).count('\n'), 'replaced 40 ->', n40)
