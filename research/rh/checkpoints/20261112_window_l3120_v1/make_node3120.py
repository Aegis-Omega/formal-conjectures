"""Write CvSNodeL3120V1.lean from ../20261111_window_l32_diagonal_v1/CvSNodeL32V1.lean: L = 3/2 -> 31/20,
and a new proof of node_big (log 5 >= 1/5 + 2 log 2 > 31/20; log(9/2) < 31/20 no longer suffices).
usage: python3 make_node3120.py PATH/CvSNodeL32V1.lean OUT.lean
"""
import sys
t = open(sys.argv[1]).read()
t = t.replace('CvSNodeL32V1', 'CvSNodeL3120V1')
a = t.index('/-- Prime powers `j + 1 ≥ 5`'); b = t.index('end AEGIS.CvSNodeL3120V1')
newbig = '''/-- Prime powers `j + 1 ≥ 5` have `log(j+1) > 31/20`, so their node is the window end
(`log 5 = log (5/4) + 2 log 2 ≥ 1/5 + 2 log 2`). -/
theorem node_big {j : ℕ} (hj : 4 ≤ j) : node (31 / 20) j = 31 / 20 := by
  simp only [node]
  apply min_eq_right
  have h5 : (5 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ j + 1)
  have hl : Real.log 5 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h5
  have e5 : Real.log 5 = Real.log (5 / 4) + 2 * Real.log 2 := by
    conv_lhs => rw [show (5 : ℝ) = 5 / 4 * 2 ^ 2 by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlo : (31 / 20 : ℝ) ≤ 1 - (5 / 4 : ℝ)⁻¹ + 2 * l2Lo := by norm_num [l2Lo]
  have a := log2_bounds.1
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

'''
t = t[:a] + newbig + t[b:]
reps = [('# Prime-power nodes at the window `L = 3/2`', '# Prime-power nodes at the window `L = 31/20`'),
        ('At `L = 3/2` three prime powers lie inside the window', 'At `L = 31/20` three prime powers lie inside the window'),
        ('(`node_one`, `node_two`, `node_three`); every `j + 1 ≥ 5` sits at the window end (`node_big`,\nfrom `log 5 ≥ log (9/2) = 2 log 3 − log 2 > 3/2`). This is the `L = 3/2` analogue of the node\nlemmas of `CvSTauPrimeL118V1`, with one more interior node. Not RH.',
         '(`node_one`, `node_two`, `node_three`); every `j + 1 ≥ 5` sits at the window end (`node_big`,\nfrom `log 5 ≥ 1/5 + 2 log 2 > 31/20`). As `CvSNodeL32V1` at `L = 3/2`; only `node_big` needs a\nnew bound, since `log (9/2) < 31/20`. Not RH.'),
        ('/-- New at `L = 3/2`: the prime power `4 = 2²` is inside the window, `log 4 = 2 log 2 < 3/2`. -/',
         '/-- The prime power `4 = 2²` is inside the window, `log 4 = 2 log 2 < 31/20`. -/'),
        ('(3 / 2)', '(31 / 20)'), ('(l3Hi : ℝ) ≤ 3 / 2', '(l3Hi : ℝ) ≤ 31 / 20')]
for x, y in reps:
    assert x in t, x
    t = t.replace(x, y)
left = [l for l in t.split('\n') if ('3 / 2' in l or '3/2' in l) and 'CvSNodeL32V1' not in l]
assert not left, left
open(sys.argv[2], 'w').write(t)
