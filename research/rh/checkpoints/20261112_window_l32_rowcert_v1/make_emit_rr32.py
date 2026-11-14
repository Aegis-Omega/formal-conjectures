"""Derive emit_rr32.py (Lean data modules of the L = 3/2 row certificate) from the lab's
tools/emit_rr118.py: KK 70 -> 150, NP 250 -> 900, kappa 58 -> 60, phi with 3^2, the kernel-checked
boxes of CvSTauL32AllV1 / CvSDiagL32V1, LDL scale 2^80. Every substitution is counted.
usage: python3 make_emit_rr32.py REPO > emit_rr32.py"""
import sys
from pathlib import Path
t = (Path(sys.argv[1]) / 'research/rh/feshbach_lean_v1/tools/emit_rr118.py').read_text()
def sub(a, b, n=1):
    global t
    assert t.count(a) == n, (a, t.count(a))
    t = t.replace(a, b)
sub("c = pickle.load(open('cert43_64.pkl', 'rb'))", "c = pickle.load(open('cert43_80.pkl', 'rb'))")
sub('import CvSTauR1PrimeL118V1\nimport CvSDiagL118V1\n', 'import CvSTauL32AllV1\nimport CvSDiagL32V1\n')
sub('''open AEGIS.CvSTauPrimeL118V1 (tauFLo tauFHi)
open AEGIS.CvSTauR1PrimeL118V1 (tauFLoExtra tauFHiExtra)
open AEGIS.CvSDiagL118V1 (diagLo diagHi)''', '''open AEGIS.CvSTauL32AllV1 (tLoAll tHiAll)
open AEGIS.CvSDiagL32V1 (diagLo diagHi)''')
sub('''def boxLo (k : ℕ) : ℚ := if k = 0 then 0 else if k ≤ 70 then tauFLo.getD (k - 1) 0 else
  tauFLoExtra.getD (k - 71) 0
def boxHi (k : ℕ) : ℚ := if k = 0 then 0 else if k ≤ 70 then tauFHi.getD (k - 1) 0 else
  tauFHiExtra.getD (k - 71) 0''', '''def boxLo (k : ℕ) : ℚ := if k = 0 then 0 else tLoAll k
def boxHi (k : ℕ) : ℚ := if k = 0 then 0 else tHiAll k''')
sub('(List.range 251).all', '(List.range 901).all')
sub('''def phi (n : ℤ) : ℤ := -(1024 * SI * n * n + 121 * 2 ^ 70)''', '''def phi (n : ℤ) : ℤ := -(64 * SI * n * n + 9 * 2 ^ 70)''')
sub('`121 · 2^72 f̂_n` with `f̂_n = -(256/121)(SI/2^70) n² - 1/4 ≈ -(16πn/11)² - 1/4`',
    '`9 · 2^72 f̂_n` with `f̂_n = -(64/9)(SI/2^70) n² - 1/4 ≈ -(4πn/3)² - 1/4`')
sub('/-- The outside rows `70 < |m| ≤ 250`. -/', '/-- The outside rows `150 < |m| ≤ 900`. -/')
sub('((List.range 180).map fun k => (k : ℤ) + 71) ++ (List.range 180).map fun k => -((k : ℤ) + 71)',
    '((List.range 750).map fun k => (k : ℤ) + 151) ++ (List.range 750).map fun k => -((k : ℤ) + 151)')
sub('`n = -70, …, 70`', '`n = -150, …, 150`', 2)
sub('(n + 70).toNat', '(n + 150).toNat', 3)
sub('(List.range 141).all', '(List.range 301).all', 4)
sub('((i : ℤ) - 70)', '((i : ℤ) - 150)', 8)
sub('`u = 0, …, 321`', '`u = 0, …, 1051`')
sub('(List.range 321).all', '(List.range 1051).all')
sub('`121 · 2^172 / φ_m`, `m = -70, …, 70`', '`9 · 2^172 / φ_m`, `m = -150, …, 150`')
sub('(m + 70).toNat', '(m + 150).toNat')
sub('121 * 2 ^ 172 / phi', '9 * 2 ^ 172 / phi')
sub("Cq='`Ĉ = Cq/2^64 ≈ 11/(16π²)`.'", "Cq='`Ĉ = Cq/2^64 ≈ 3/(4π²)`.'")
sub('13² (L/π)²', '15² (L/π)²')
sub('/-- `2^128 gramUp 250`. -/', '/-- `2^128 gramUp 900`. -/')
sub('2 ^ 129 / (501 - 2 * n) + 2 ^ 129 / (501 + 2 * n)', '2 ^ 129 / (1801 - 2 * n) + 2 ^ 129 / (1801 + 2 * n)')
sub('(hq (250 - m) - hq (250 - n) + (hq (250 + n) - hq (250 + m)))', '(hq (900 - m) - hq (900 - n) + (hq (900 + n) - hq (900 + m)))')
sub('(hq (250 - n) - hq (250 - m) + (hq (250 + m) - hq (250 + n)))', '(hq (900 - n) - hq (900 - m) + (hq (900 + m) - hq (900 + n)))')
sub('  58 * Et n m - LPq', '  60 * Et n m - LPq')
sub('((List.range 141).map fun (b : ℕ) => Et n ((b : ℤ) - 70) * gv jj ((b : ℤ) - 70)).sum',
    '((List.range 301).map fun (b : ℕ) => Et n ((b : ℤ) - 150) * gv jj ((b : ℤ) - 150)).sum')
sub('(List.range 71).all fun n =>', '(List.range 151).all fun n =>')
sub('`τ_k`, `k ≤ 250`', '`τ_k`, `k ≤ 900`')
sub('`cvsEntry M (11/8) n n`, `n ≤ 70`', '`cvsEntry M (3/2) n n`, `n ≤ 150`')
sub('`Σ_{70<|m|≤250}', '`Σ_{150<|m|≤900}')
sub('`k = 0, …, 250`', '`k = 0, …, 900`')
sub('`n = 0, …, 70`', '`n = 0, …, 150`')
sub('`tools/gen_rr118.py` (untrusted)', '`gen_rr32.py` (untrusted)')
sub('`139 × 139`, entries of at most 33 bits', '`299 × 299`, entries of at most 41 bits')
sub('`2^64 P̃ = certL', '`2^80 P̃ = certL')
sub('`tools/gen_rr118.py` and `tools/cert43.py`', '`gen_rr32.py` and `cert43.py 80`')
sub('/-- The packed lower factor at `2^32`. -/', '/-- The packed lower factor at `2^40`. -/')
t = t.replace('`L = 11/8`', '`L = 3/2`').replace('L118V1', 'L32V1').replace("rr43_data.pkl and\ncert43_64.pkl", "rr43_data.pkl and\ncert43_80.pkl")
t = t.replace('(output of gen_rr118.py and cert43.py)', '(output of gen_rr32.py, rescale_pkl.py and cert43.py 80)')
t = t.replace('modules of the L = 11/8 relative', 'modules of the L = 3/2 relative', 1).replace('python3 emit_rr118.py OUTDIR', 'python3 emit_rr32.py OUTDIR', 1)
left = [l for l in t.split('\n') if any(x in l for x in ('11/8', '118', ' 70', '(70', '71', '141', '139', '250', '251', '321', '501', '121'))]
print(t)
print('\n'.join('LEFT: ' + l for l in left), file=sys.stderr)
