"""Second layer of the window 2r <= 8/5 port: rows NP = 2000 -> 4000 and slack m = 33/20 -> 8/5.
Reads the output of make_port85.py (D1) and writes D2. Every NP-derived number of the 49/32 port is
mapped by one token pass (NP, NP + 1, NP - 49 = last tau block, NP - 156 = outside rows per side,
2 NP + 1, NP + 156, NP + 157, NP + 158, the rounding counts 2 (NP - 156), 4 (NP - 156), + 1, the
harmonic errors 4 (NP + 156) and its slack, q (NP + 1), the K-table error, hupN (NP + 156)); the
list of tau data modules (80), the chunk counts, the trace layout (TOP 621 -> 600, t* = 589.8 at
m = 8/5), node_big (log 5 > 8/5 from e^8 < 5^5) and the Cu constant are set explicitly.
usage: python3 make_np85.py D1 D2"""
import re
import shutil
import sys
from pathlib import Path

d1, d2 = Path(sys.argv[1]), Path(sys.argv[2])
NP = 4000


def hupN(K):
    return sum((2 ** 64 + k) // (k + 1) for k in range(K))


assert hupN(2156) == 152249418040331449282
TOK = {2000: NP, 2001: NP + 1, 1999: NP - 1, 1951: NP - 49, 1844: NP - 156, 4001: 2 * NP + 1,
       2156: NP + 156, 2157: NP + 157, 2158: NP + 158, 3688: 2 * (NP - 156), 7376: 4 * (NP - 156),
       7377: 4 * (NP - 156) + 1, 8624: 4 * (NP + 156), 8700: 4 * (NP + 156) + 76, 10005: 5 * (NP + 1),
       1700000: 3500000, 152249418040331449282: hupN(NP + 156)}
# K-table error: 225 (4 (NP - 156) + 1) + 2 <= 3500000
assert 225 * (4 * (NP - 156) + 1) + 2 <= 3500000
TX = re.compile(r'(?<!\d)(?<!\d\.)(\d+)(?![\d])')


def tok(t):
    return TX.sub(lambda m: str(TOK.get(int(m.group(1)), m.group(1))), t)


def sub(t, a, b, n=1):
    assert t.count(a) == n, (a, t.count(a))
    return t.replace(a, b)


if d2.exists():
    shutil.rmtree(d2)
shutil.copytree(d1, d2)
for p in sorted(d2.rglob('*')):
    if p.is_file() and p.suffix in ('.py', '.sh', '.json', '.txt', '.lean') and p.name != 'CvSExpL85V1.lean':
        p.write_text(tok(p.read_text()))

# tau data modules K1, K51, ..., K3951 (build order: sorted names, as before)
p = d2 / 'build_order.txt'
L = p.read_text().split('\n')
idx = [i for i, l in enumerate(L) if re.fullmatch(r'CvSTauL85K\d+V1', l)]
assert len(idx) == 40 and idx == list(range(idx[0], idx[0] + 40)), idx
L[idx[0]:idx[0] + 40] = sorted(f'CvSTauL85K{s}V1' for s in range(1, NP + 1, 50))
p.write_text('\n'.join(L))

p = d2 / 'make_tau_gen85.py'
t = p.read_text()
t = sub(t, 'from the 40 data modules', 'from the 80 data modules')
t = sub(t, 'The forty data modules', 'The eighty data modules')
# tau_mem_all splits over 80 blocks instead of 40; its if_neg simp work is quadratic in the blocks, past the
# default 200000 heartbeats, so the assembler raises the limit for that one theorem (the proof is unchanged)
t = sub(t, "'radius `5·10⁻¹³` and `5·10⁻¹⁰`')])",
        "'radius `5·10⁻¹³` and `5·10⁻¹⁰`'),\n    (\"'''/-- **`τ_k` at `L = 8/5`\", \"'''set_option maxHeartbeats 2000000 in\\n/-- **`τ_k` at `L = 8/5`\")])")
p.write_text(t)
for name, a, b in [('rr/chunk_h85.py', 'into 44 kernel checks', 'into 84 kernel checks'),
                   ('rr/fast_hq85.py', 'in 44 chunks', 'in 84 chunks'),
                   ('rr/chunk_data85.py', 'boxes_ok: 40 chunks', 'boxes_ok: 80 chunks'),
                   ('rr/chunk_box85.py', 'into the 40 chunks', 'into the 80 chunks'),
                   ('rr/chunk_box85.py', 'len(CH) == 40', 'len(CH) == 80')]:
    p = d2 / name
    p.write_text(sub(p.read_text(), a, b))
# chunksG_cov decides 4158 values in the elaborator; at NP = 2000 (2158) that fit the default heartbeats of
# CvSRelRowCheck, at 4000 it does not (the data modules already run with maxHeartbeats 0)
p = d2 / 'rr/fast_hq85.py'
p.write_text(sub(p.read_text(), "F += 'theorem chunksG_cov :", "F += 'set_option maxHeartbeats 0 in\\ntheorem chunksG_cov :"))

# slack m = 8/5: trace certificate (TOP 600, 1500 cells of width 1/3 on [100, 600]), integral, window
p = d2 / 'make_gen_cert85.py'
t = p.read_text()
t = sub(t, '"(\'100\', \'1 / 3\', 1563, 43)"', '"(\'100\', \'1 / 3\', 1500, 43)"')
t = sub(t, '"TOP = 621"', '"TOP = 600"')
t = sub(t, '1/3 on [100, 621]; m = 33/20."', '1/3 on [100, 600]; m = 8/5."')
t = sub(t, '    assert a in t or a == "cert118_totals.json", a\n    t = t.replace(a, b)\n',
        '    assert a in t or a == "cert118_totals.json", a\n    t = t.replace(a, b)\n'
        "for a in ('33 / 20', '33/20'):\n    assert a in t, a\nt = t.replace('33 / 20', '8 / 5').replace('33/20', '8/5')\n")
p.write_text(t)

p = d2 / 'port_trace_l85.py'
t = p.read_text()
t = sub(t, "'264 / 25 * Real.pi ^ 2 - 16 / 5 * T * Real.pi'", "'256 / 25 * Real.pi ^ 2 - 16 / 5 * T * Real.pi'")
t = sub(t, "'`κ = 66`, `m = 33/20` and any `T ≤ 3`'", "'`κ = 66`, `m = 8/5` and any `T ≤ 3`'")
t = sub(t, "t = num(num(t, L), K)\n(out / 'CvSTraceIntegralL85V1.lean').write_text(t)",
        "t = num(num(t, L), K)\nassert '33 / 20' in t\nt = t.replace('33 / 20', '8 / 5')\n"
        "(out / 'CvSTraceIntegralL85V1.lean').write_text(t)")
p.write_text(t)

p = d2 / 'make_window85.py'
t = p.read_text()
t = sub(t, "'`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 8/5`, `m = 33/20`'",
        "'`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 8/5`, `m = 8/5`'")
t = sub(t, "(out / 'CvSWindowL85V1.lean').write_text(t)",
        "assert t.count('33 / 20') == 2\nt = t.replace('33 / 20', '8 / 5')\n(out / 'CvSWindowL85V1.lean').write_text(t)")
p.write_text(t)

# LDL at q = 88 (cert43.py 88 on the rescaled NP = 4000 pickle; q = 80 and 84 fail), entries of 45 bits
p = d2 / 'rr/make_rr85_check.py'
t = p.read_text()
t = sub(t, 'PS, Q = 508, 80', 'PS, Q = 508, 88')
t = sub(t, 'LDL at 2^80 with P at 2^-508, so the interval shift is 428', 'LDL at 2^88 with P at 2^-508, so the interval shift is 420')
p.write_text(t)
p = d2 / 'rr/make_emit_rr85.py'
t = p.read_text()
t = sub(t, 'cert43_80.pkl', 'cert43_88.pkl', 2)
t = sub(t, "'`2^80 P̃ = certL'", "'`2^88 P̃ = certL'")
t = sub(t, '`cert43.py 80`', '`cert43.py 88`')
t = sub(t, 'cert43.py 80)', 'cert43.py 88)')
t = sub(t, 'LDL scale 2^80', 'LDL scale 2^88')
t = sub(t, "'/-- The packed lower factor at `2^40`. -/'", "'/-- The packed lower factor at `2^44`. -/'")
t = sub(t, "'`311 × 311`, entries of at most 41 bits'", "'`311 × 311`, entries of at most 45 bits'")
p.write_text(t)
p = d2 / 'regen.sh'
t = sub(p.read_text(), 'rr/cert43_80.pkl', 'rr/cert43_88.pkl')
t = sub(t, 'Regenerate the 69 generated Lean modules', 'Regenerate the 109 generated Lean modules')
t = sub(t, '"$S/gen_diag85.py" 300 157 >', '"$S/gen_diag85.py" 600 157 >')
t = sub(t, '"$OUT/diag85_data.txt" 300 157 8', '"$OUT/diag85_data.txt" 600 157 4')
# CvSDiagL85V1 imports the h+ enclosure with K = 600 terms (port_hplus.py of the 3/2 diagonal checkpoint)
t = sub(t, 'python3 "$S/gen_diag85.py" 600 157 >',
        'python3 "$C/20261111_window_l32_diagonal_v1/port_hplus.py" "$REPO" "$M" 600\npython3 "$S/gen_diag85.py" 600 157 >')
t = sub(t, 'Regenerate the 109 generated Lean modules', 'Regenerate the 110 generated Lean modules')
p.write_text(t)
p = d2 / 'build_order.txt'
L = p.read_text().split('\n')
assert L.count('CvSDiagL85V1') == 1 and 'CvSHplusK600V1' not in L
L.insert(L.index('CvSDiagL85V1'), 'CvSHplusK600V1')
p.write_text('\n'.join(L))

# outside-row tables: tLit in 81 rows of 50; S/T/V checks in chunks of 4 rows (79 pieces) instead of 8,
# since every row now sums 7688 outside terms instead of 3688
p = d2 / 'rr/fast_tq85.py'
t = p.read_text()
t = sub(t, 'assert len(rows) == 41 and len(rows[-1]) == 1', 'assert len(rows) == 81 and len(rows[-1]) == 1')
t = sub(t, "assert blk.count(f'{raw} {j} ') == 41, blk.count(f'{raw} {j} ')",
        "assert blk.count(f'{raw} {j} ') == 80, blk.count(f'{raw} {j} ')")
p.write_text(t)
p = d2 / 'rr/chunk_data85.py'
t = p.read_text()
t = sub(t, 'N, C = 313, 8', 'N, C = 313, 4')
t = sub(t, 'into chunks of 8 indices', 'into chunks of 4 indices')
p.write_text(t)

# diagonal: K = 600 series terms (width 3.9e-13 instead of 6.2e-12 at K = 300)
p = d2 / 'make_diag_ports85.py'
p.write_text(p.read_text() + """
p = out / 'port_diag_l85.py'
s = p.read_text()
assert s.count('6·10⁻¹²') == 2
s = s.replace('6·10⁻¹²', '4·10⁻¹³')
# with aK = 1199/2 the elaboration of D_bounds (gcongr, push_cast on aK^5) passes the default
# maxRecDepth; the proof is unchanged
a = "(out / 'CvSDiagL85V1.lean').write_text(head + body)"
assert s.count(a) == 1
s = s.replace(a, "full = head + body\\nassert full.count('\\\\ntheorem D_bounds ') == 1\\n"
              "full = full.replace('\\\\ntheorem D_bounds ', '\\\\nset_option maxRecDepth 100000 in\\\\ntheorem D_bounds ')\\n"
              "(out / 'CvSDiagL85V1.lean').write_text(full)")
p.write_text(s)
print('port_diag_l85.py: width 4e-13 (K = 600), maxRecDepth for D_bounds')
""")

# node_big at 8/5: log 5 >= 1/5 + 2 log 2 is below 8/5; use e^8 < 5^5
p = d2 / 'make_node85.py'
t = p.read_text()
a, b = t.index("newbig = '''"), t.index("'''\nt = t[:a] + newbig + t[b:]")
t = t[:a] + """newbig = '''/-- Prime powers `j + 1 ≥ 5` have `log(j+1) > 8/5`, so their node is the window end
(`exp (8/5) ^ 5 = e^8 < 5^5`). -/
theorem node_big {j : ℕ} (hj : 4 ≤ j) : node (8 / 5) j = 8 / 5 := by
  simp only [node]
  apply min_eq_right
  have h5 : (5 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ j + 1)
  have hl : Real.log 5 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h5
  have h85 : (8 / 5 : ℝ) < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have e : Real.exp (8 / 5) ^ 5 = Real.exp 1 ^ 8 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 1 ^ 8 < 5 ^ 5 := by
      have := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : (8 : ℕ) ≠ 0)
      linarith [show (2.7182818286 : ℝ) ^ 8 < 5 ^ 5 by norm_num]
    by_contra hc
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (not_lt.mp hc) 5
    linarith
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

""" + t[b:]
t = sub(t, 'from `log 5 ≥ 1/5 + 2 log 2 > 8/5`). As `CvSNodeL32V1` at `L = 3/2`; only `node_big` needs a\\nnew bound, since `log (9/2) < 8/5`. Not RH.',
        'from `e^8 < 5^5`). As `CvSNodeL32V1` at `L = 3/2`; only `node_big` needs a new bound, since\\n`log (9/2) < 8/5` and `1/5 + 2 log 2 < 8/5`. Not RH.')
t = sub(t, "and a new proof of node_big (log 5 >= 1/5 + 2 log 2 > 8/5; log(9/2) < 8/5 no longer suffices).",
        "and a new proof of node_big (e^8 < 5^5; log(9/2) and 1/5 + 2 log 2 are below 8/5).")
p.write_text(t)

for p in sorted(d2.rglob('*')):
    if p.is_file() and p.suffix in ('.py', '.sh', '.json', '.txt', '.lean'):
        for i, l in enumerate(p.read_text().split('\n')):
            if re.search(r'(?<!\d)(?<!\d\.)(2000|1951|1844|3688|33 / 20|33/20)(?![\d])', l):
                print(f'LEFT {p.relative_to(d2)}:{i + 1}: {l.strip()[:150]}')
print('NP', NP, 'H', NP + 156, hupN(NP + 156))
