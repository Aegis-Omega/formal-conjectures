# The small eigenvalues of the window form are zero modes

Date: 2026-11-13. Evidence kind: `numerical` (float64 eigen-decompositions of the Arb midpoints of
the lab's own window matrices; no interval enclosure, no Lean). Nothing is promoted. **RH remains
OPEN.**

## What is computed

`sweep.py` builds, for a support length `l`, the moment-zero Weil (CvS) form on `L²[0, l]` in the
basis `e_m(x) = e^{2πimx/l}`, `|m| ≤ N`: the blocks `A11` and `G11` of `feshbach_blocks_arb.py`
(`../../aegis_source_0c1477f/research/feshbach_arb_v2/`, with its `cvs_entries.py`, sha256
`b9e2c3b9…`), band rows only, Arb at 192 bits; then the generalized eigenvalues
`A11 v = λ G11 v` of the midpoints. Only the prime powers `q < e^l` enter (`2, 3, 4, 5` at
`l = 1.8`) and the archimedean factor. With `N = 60` the low eigenvalues agree with the `N = 200`
and `N = 400` blocks of the Arb receipts (`l = 1.6`: `5.98e-12` against `5.35e-12`, the same
pattern of six small values below the bulk). In the lab's normalization `l = 2L₀`, so `l = 1.6` is
the window `8/5`.

## Results

1. **The lowest eigenvector detects the zeros.** At `l = 1.8` (`modes_all_1.8.txt`), every local
   minimum of `|Ĝ(t)|` on `(5, 60)`, `Ĝ(t) = ∫₀^l G(x) e^{−itx} dx`, is at an ordinate of a zeta
   zero: `γ₁, …, γ₁₁` within `7·10⁻⁴` (the grid step is `5·10⁻⁴`), `γ₁₂` within `0.005`, `γ₁₃`
   within `0.06`; there are no other minima. The matrix knows only the primes `2, 3, 5` and `4`.
   The next six eigenvectors have their deepest minima at the same zeros; from the eighth on they
   drift (`modes_1.8.txt`).
2. **One new small eigenvalue per zero.** As `l` grows (`sweep60.txt`, `l = 0.70, …, 2.10`), a new
   eigenvalue leaves the bulk (`~0.5–1`) each time `2πe^l` passes a zero. At the threshold `0.1`
   (`branch60.txt`) the eigenvalues `6, …, 12` cross at `l` within `±0.044` of `ln(γ_k/2π)`,
   `k = 4, …, 10` (for example `1.789` against `ln(γ₆/2π) = 1.789`); the first three zeros come
   later, by `0.43, 0.16, 0.11`. At `l = 1.6` there are six small eigenvalues, at `l = 1.8` eight.
3. So the threshold `T* = 2πe^{2L}` of Zhu's fit (`../20261113_window_route_position_v1/`) is the
   height where the zeros pass `2πe^l`: each zero below it adds one direction in which the window
   form is nearly zero, and its size falls with every further zero. A certificate of the sign on a
   window has to bound the form in all of these directions at once, which is why the margin and the
   certificate size (`NP`, the box widths, the atoms) grow so fast from window to window. The same
   phenomenon (eigenvectors of the Weil form restricted to an interval whose Fourier zeros approximate
   the zeta zeros) is reported by Connes and Consani (and with Moscovici, prolate operators); it is
   reproduced here in the lab's own matrices (`literature` for the comparison, not checked here).

## What it suggests (open)

The sign on a window of support length `l` is governed by the zeros up to about `2πe^l`. A theorem
of the form "if the zeros with `γ ≤ c·e^l` lie on the critical line, then the window sign holds up
to `l/2`, with an explicit bound for the contribution of the higher zeros" would let verified zero
computations stand in for window certificates. Nothing here proves such a bound; the part above the
threshold is where the difficulty sits, and it is not RH, which needs every window.

## Files and replay

`sweep.py DIR N l…` (the eigenvalues; with `SAVE_VEC=1` it also saves the twelve lowest eigenvectors
in the band basis to `vec_<l>.pkl`), `branch.py sweep60.txt` (the crossing points),
`modes.py` and `modes_all.py vec_1.8.pkl` (the Fourier minima), with `DIR =
REPO/research/rh/aegis_source_0c1477f/research/feshbach_arb_v2`:

```
python3 sweep.py $DIR 60 $(python3 -c "print(' '.join('%.2f' % (0.70 + 0.02 * i) for i in range(71)))") > sweep60.txt
python3 branch.py sweep60.txt > branch60.txt
SAVE_VEC=1 python3 sweep.py $DIR 60 1.8 && python3 modes.py vec_1.8.pkl > modes_1.8.txt && python3 modes_all.py vec_1.8.pkl > modes_all_1.8.txt
```

(about 3 s per value of `l`; python-flint, numpy, scipy).
