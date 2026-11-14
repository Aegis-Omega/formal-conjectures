"""Write CvSTauFarL4932V1.lean from ../20261112_window_l32_rowcert_v1/CvSTauFarL32V1.lean: L = 3/2 -> 49/32,
the cutoff |n| >= 151 -> |n| >= 2001 (NP = 2000), the prime arguments 2 n log p / L = 64 n log p / 49.
Every substitution is counted. usage: python3 make_taufar4932.py PATH/CvSTauFarL32V1.lean OUT.lean"""
import sys
t = open(sys.argv[1]).read()
R = [('CvSTauFastL32V1', 'CvSTauFastL4932V1', 3), ('CvSTauFarL32V1', 'CvSTauFarL4932V1', 3),
     ('# A sharp bound for `τ_n` far from the low block at L = 3/2', '# A sharp bound for `τ_n` far from the low block at L = 49/32', 1),
     ('and at `L = 3/2` the prime powers', 'and at `L = 49/32` the prime powers', 1),
     ('For `|n| ≥ 151` and every `M ≥ 4` this gives\n`|τ_n| ≤ 15` (the value is about `14.19`). Not RH.',
      'For `|n| ≥ 2001` and every `M ≥ 4` this gives\n`|τ_n| ≤ 15` (the value is about `14.18`). As `@FAR32@` at `L = 3/2`. Not RH.', 1),
     ('/-- **`|τ_n| ≤ 15` for `|n| ≥ 151` at L = 3/2**', '/-- **`|τ_n| ≤ 15` for `|n| ≥ 2001` at L = 49/32**', 1),
     ('(hn : 151 ≤ |n|)', '(hn : 2001 ≤ |n|)', 1), ('(151 : ℝ) ≤ |(n : ℝ)|', '(2001 : ℝ) ≤ |(n : ℝ)|', 1),
     ('(L := 3 / 2)', '(L := 49 / 32)', 1),
     ('(3 / 2 : ℝ) / |(n : ℝ)| ≤ 3 / 302', '(49 / 32 : ℝ) / |(n : ℝ)| ≤ 49 / 64032', 1),
     ('(3 / 302 + Real.pi ^ 2 / 2)', '(49 / 64032 + Real.pi ^ 2 / 2)', 1),
     ('(3 / 2)', '(49 / 32)', 3),
     ('4 * n * Real.log 2 / 3', '64 * n * Real.log 2 / 49', 5), ('4 * n * Real.log 3 / 3', '64 * n * Real.log 3 / 49', 5),
     ('8 * n * Real.log 2 / 3', '128 * n * Real.log 2 / 49', 5), ('@FAR32@', 'CvSTauFarL32V1', 1)]
for a, b, n in R:
    assert t.count(a) == n, (a, t.count(a), n)
    t = t.replace(a, b)
assert '3 / 2' not in t and '151' not in t
open(sys.argv[2], 'w').write(t)
