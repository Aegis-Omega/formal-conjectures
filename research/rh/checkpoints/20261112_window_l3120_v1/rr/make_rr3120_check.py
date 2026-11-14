"""Port CvSRelRowCheckL118V1 / CvSRelRowPsdL118V1 to L = 31/20 (KK = 156: 313 indices, 311 rows; NP = 2000;
kappa = 66; LDL at 2^80 with P at 2^-516, so the interval shift is 436; 16 chunks of 20 rows).
Derived from ../20261112_window_l32_rowcert_v1/make_rr32_check.py.
usage: python3 make_rr3120_check.py REPO OUTDIR"""
import re
import sys
from pathlib import Path
repo, out = Path(sys.argv[1]), Path(sys.argv[2])
F = repo / 'research/rh/feshbach_lean_v1'
PS, Q = 516, 80
CH = [(a, min(20, 311 - a)) for a in range(0, 311, 20)]
def sub(t, a, b, n=1):
    assert t.count(a) == n, (a, t.count(a))
    return t.replace(a, b)
# ---- Check
t = (F / 'CvSRelRowCheckL118V1.lean').read_text()
t = sub(t, '`Pm i j` (scale `2^-488`)', f'`Pm i j` (scale `2^-{PS}`)')
t = sub(t, 'The kernel computes its rows in seven chunks', f'The kernel computes its rows in {len(CH)} chunks')
t = sub(t, 'rounds them to intervals at `2^-64`', f'rounds them to intervals at `2^-{Q}`')
t = sub(t, '((i : ℤ) - 70 + s)', '((i : ℤ) - 156 + s)', 3)
t = sub(t, '((j : ℤ) - 70 + t)', '((j : ℤ) - 156 + t)')
t = sub(t, '/-- The check matrix at `2^-488`. -/', f'/-- The check matrix at `2^-{PS}`. -/')
t = sub(t, 'h(250 - m), h(250 + m)`', 'h(2000 - m), h(2000 + m)`')
t = sub(t, 'hq (250 - m), hq (250 + m)', 'hq (2000 - m), hq (2000 + m)')
t = sub(t, '2 ^ 129 / (501 - 2 * n) + 2 ^ 129 / (501 + 2 * n)', '2 ^ 129 / (4001 - 2 * n) + 2 ^ 129 / (4001 + 2 * n)')
t = sub(t, '  58 * et - LPq', '  66 * et - LPq')
t = sub(t, 'def cols141 : List Col := (List.range 141).map fun (b : ℕ) => col ((b : ℤ) - 70)',
        'def cols313 : List Col := (List.range 313).map fun (b : ℕ) => col ((b : ℤ) - 156)')
t = t.replace('cols141', 'cols313')
t = sub(t, 'def Ul (jj : ℕ) : List ℤ := (List.range 139).map (U jj)', 'def Ul (jj : ℕ) : List ℤ := (List.range 311).map (U jj)')
t = sub(t, '(424 + certD.getD i 0 + dj)', f'({PS - Q} + certD.getD i 0 + dj)', 2)
t = sub(t, "zrowC cl (((a + r : ℕ) : ℤ) - 70)", "zrowC cl (((a + r : ℕ) : ℤ) - 156)")
a = t.index('def Itab : List (List Iv) :='); b = t.index('def cols : List')
t = t[:a] + 'def Itab : List (List Iv) :=\n  ' + ' ++\n    '.join(f'Ichunk {s} {k}' for s, k in CH) + '\n\n' + t[b:]
a = t.index('theorem chunk0_ok'); b = t.index('theorem certL_ok')
t = t[:a] + ''.join(f'theorem chunk{i}_ok : rowsOk certBase certB 311 certEps certEta cols {s}\n    ((certL.drop {s}).take {k}) (Ichunk {s} {k}) = true := by decide +kernel\n' for i, (s, k) in enumerate(CH)) + '\n' + t[b:]
t = sub(t, 'decide (0 < 139) && decide (139 * 139 * (2 * certB * (2 * certB)) < certBase) &&\n    decide (certL.length = 139) && certL.all (rowBounded certB 139)',
        'decide (0 < 311) && decide (311 * 311 * (2 * certB * (2 * certB)) < certBase) &&\n    decide (certL.length = 311) && certL.all (rowBounded certB 311)')
t = sub(t, 'theorem length_certD : certD.length = 139 := by decide', 'theorem length_certD : certD.length = 311 := by decide')
a = t.index('#print axioms AEGIS.CvSRelRowCheckL118V1.chunk0_ok')
t = t[:a] + ''.join(f'#print axioms AEGIS.CvSRelRowCheckL118V1.chunk{i}_ok\n' for i in range(len(CH))) + '#print axioms AEGIS.CvSRelRowCheckL118V1.certL_ok\n'
t = t.replace('`L = 11/8`', '`L = 31/20`').replace('L118V1', 'L3120V1')
left = [l for l in t.split('\n') if re.search(r'(?<![\d.])(70|139|141|250|424|488|501|58)(?![\d.])', l)]
assert not left, left
(out / 'CvSRelRowCheckL3120V1.lean').write_text(t)
# ---- Psd
t = (F / 'CvSRelRowPsdL118V1.lean').read_text()
t = sub(t, 'encloses the scaled matrix `Pm i j / 2^(488 + d_i + d_j)`', f'encloses the scaled matrix `Pm i j / 2^({PS} + d_i + d_j)`')
t = t.replace('cols141', 'cols313')
for x, y in [('139', '311'), ('141', '313')]:
    t = re.sub(r'(?<![\d.])' + x + r'(?![\d.])', y, t)
t = re.sub(r'\(\(i : ℤ\) - 70\)', '((i : ℤ) - 156)', t)
t = re.sub(r'\(\(i : ℤ\) - 69\)', '((i : ℤ) - 155)', t)
t = re.sub(r'\(\(i : ℤ\) - 68\)', '((i : ℤ) - 154)', t)
t = t.replace('((i : ℤ) - 70 + 1)', '((i : ℤ) - 156 + 1)').replace('(i : ℤ) - 70 + 1', '(i : ℤ) - 156 + 1').replace('(i : ℤ) - 70 + 2', '(i : ℤ) - 156 + 2')
t = t.replace('((a + r : ℕ) : ℤ) - 69', '((a + r : ℕ) : ℤ) - 155').replace('((a + r : ℕ) : ℤ) - 68', '((a + r : ℕ) : ℤ) - 154')
t = t.replace('(((a + (r + 1) : ℕ) : ℤ) - 70)', '(((a + (r + 1) : ℕ) : ℤ) - 156)').replace('(((a + (r + 2) : ℕ) : ℤ) - 70)', '(((a + (r + 2) : ℕ) : ℤ) - 156)')
t = t.replace('((b : ℤ) - 70)', '((b : ℤ) - 156)').replace('(((j + 1 : ℕ) : ℤ) - 70)', '(((j + 1 : ℕ) : ℤ) - 156)').replace('(((j + 2 : ℕ) : ℤ) - 70)', '(((j + 2 : ℕ) : ℤ) - 156)')
t = t.replace('(j : ℤ) - 70 + 1', '(j : ℤ) - 156 + 1').replace('(j : ℤ) - 70 + 2', '(j : ℤ) - 156 + 2')
t = t.replace('424 + certD', f'{PS - Q} + certD').replace('(488 + certD', f'({PS} + certD').replace('2 ^ 488', f'2 ^ {PS}')
t = t.replace('= s + 64 := by', f'= s + {Q} := by').replace('(0 : ℝ) < 2 ^ 64 := by positivity', f'(0 : ℝ) < 2 ^ {Q} := by positivity')
t = t.replace('.Mem 64 (Ps i j)', f'.Mem {Q} (Ps i j)').replace('quad_lower_complex 64 certBase', f'quad_lower_complex {Q} certBase')
t = t.replace('(by positivity : (0 : ℝ) < 2 ^ 64)', f'(by positivity : (0 : ℝ) < 2 ^ {Q})')
a = t.index('theorem certL_split'); b = t.index('theorem take_len')
t = t[:a] + 'theorem certL_split : certL = ' + ' ++\n    '.join(f'(certL.drop {s}).take {k}' for s, k in CH) + ' := by rfl\n\n' + t[b:]
a = t.index('theorem rowsOk_true'); b = t.index('theorem Itab_length')
body = 'theorem rowsOk_true : rowsOk certBase certB 311 certEps certEta cols 0 certL Itab = true := by\n  rw [certL_split, Itab]\n  simp only [List.append_assoc]\n  rw ['
body += ',\n    '.join(f'rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len {s} {k} (by norm_num)])' for s, k in CH[:-1]) + ']\n'
body += '  simp only [' + ', '.join(f'take_len {s} {k} (by norm_num)' for s, k in CH[:-1]) + ']\n  norm_num only\n'
body += '  simp only [' + ', '.join(f'chunk{i}_ok' for i in range(len(CH))) + ',\n    Bool.and_self]\n\n'
t = t[:a] + body + t[b:]
t = t.replace('`L = 11/8`', '`L = 31/20`').replace('L118V1', 'L3120V1')
left = [l for l in t.split('\n') if re.search(r'(?<![\d.])(70|69|68|139|141|424|488)(?![\d.])', l)]
assert not left, left
t = t.replace('\nnamespace AEGIS.CvSRelRowPsdL3120V1', '\nset_option maxRecDepth 100000\n\nnamespace AEGIS.CvSRelRowPsdL3120V1', 1)
(out / 'CvSRelRowPsdL3120V1.lean').write_text(t)
print('written Check and Psd;', len(CH), 'chunks')
