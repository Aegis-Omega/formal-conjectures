# The zero side of the window form: which zeros a window sees

Date: 2026-11-13. Evidence kind: `numerical` (float64 eigenvectors of the Arb midpoints of the lab's
window matrices, zeta zeros from Arb's `acb.zeta_zeros` used at their midpoints; no interval enclosure,
no Lean). Nothing is promoted. **RH remains OPEN.**

Continues `../20261113_window_zero_modes_v1/` (the small eigenvalues are zero modes).

## What is computed

For a support length `l` and `G = Σ_{|m| ≤ 60} V_m e^{2πimx/l}/√l` on `[0, l]` with the two moment
conditions (the moment-zero subspace of `sweep.py`), let `Ĝ(t) = ∫₀^l G(x) e^{−itx} dx`. The explicit
formula gives the Weil form as a sum over the zeros `ρ = 1/2 + iγ`; for zeros on the critical line the
term is `|Ĝ(γ)|²` (`γ` of both signs), and the moment conditions remove the pole terms.

* `explicit.py` compares, for the twelve lowest eigenvectors at `l = 1.2, 1.4, 1.6, 1.8`, the form value
  `λ = ⟨G, AG⟩` of the lab's matrix (prime side: prime powers `q < e^l` and the archimedean factor) with
  the zero side `Σ_γ |Ĝ(γ)|²` over the first 20000 zeros (to height 18046), plus the Riemann–von Mangoldt
  density integral above them.
* `model.py` replaces the zeros above a height `T₀` by that density,
  `Σ_{γ<T₀} |Ĝ(γ)|² + ∫_{T₀}^∞ |Ĝ(t)|² log(t/2π) dt/2π`, and computes the lowest eigenvalues of this form
  on the same subspace, for `T₀` a multiple of `T* = 2πe^l`.
* `inject.py` keeps every zero on the line except one pair moved to `1/2 ± δ + iγ₀` and asks for which
  heights `γ₀` the lowest eigenvalue of the zero side turns negative.

## Results

1. **The lab's matrix is the zero side of the explicit formula** (`explicit_20000.txt`,
   `explicit_50000.txt`). With 50000 zeros (to height 40434), the 25 of the 48 vectors whose part above
   the last zero is below `10⁻⁶` of the sum agree to `|Z − λ| ≤ 1.2·10⁻¹⁵`, the float64 resolution of
   the eigenvalues. For the others (the vectors with `G(0) ≠ 0`, whose transforms decay like `1/t`) the
   relative difference is at most `5·10⁻⁴` times the share of that tail, the error of its density
   approximation, or below `10⁻¹⁵` in absolute terms. This is a numerical check of the step "the CvS
   matrix is the restricted Weil form", which the Arb receipts of `feshbach_arb_v2` list as not
   formalised; it uses that the first 50000 zeros are on the critical line (verified far beyond this
   height, `literature`).
2. **The lowest eigenvalue comes from the zeros above `T*`.** Its share from the zeros below `T*` is
   `2.6·10⁻⁴, 7.2·10⁻⁵, 1.3·10⁻⁶, 1.9·10⁻⁸` at `l = 1.2, 1.4, 1.6, 1.8`: the lowest mode nearly vanishes
   at the low zeros, and its value is what the higher zeros leave.
3. **The zeros below about `4T*` and the mean density above fix the floor** (`model_20000.txt`):

   | `l` | `λ₁` (matrix) | `T₀ = T*` | `2T*` | `4T*` | zeros below `4T*` |
   |---|---|---|---|---|---|
   | 1.2 | `6.687·10⁻⁵` | `1.44·10⁻⁴` | `7.20·10⁻⁵` | `6.76·10⁻⁵` | 22 |
   | 1.4 | `5.765·10⁻⁸` | `1.03·10⁻⁶` | `6.48·10⁻⁸` | `5.77·10⁻⁸` | 30 |
   | 1.6 | `5.982·10⁻¹²` | `3.91·10⁻¹⁰` | `7.20·10⁻¹²` | `5.94·10⁻¹²` | 41 |

   With the exact zeros only below `T*` the model is off by factors 2, 18, 65; below `4T*` it is within
   1.1 %, and from `16T*` on the first six eigenvalues agree to 0.4 %. (At `l = 1.8`, `λ₁ ≈ 10⁻¹⁶` is
   below float64 resolution.)

4. **A window sees a single off-line zero only below about `2T*`** (`inject.py`, `inject_l16.txt`,
   `inject_grid.txt`). With every zero on the critical line except one pair (the two zeros nearest to a
   height `H` replaced by `1/2 ± δ + iγ₀` at their mean height `γ₀`), the lowest eigenvalue of the zero side
   becomes negative, so that a window theorem at `l` would exclude that pair, only for `γ₀` up to
   `1.5–1.8 T*` (`δ = 0.5`, i.e. `β = 1`; lower for small `δ`), and not from `1.75–2.0 T*` on: at `l = 1.6`
   detected at `γ₀ = 51.4` and not from `60.1` on (`T* = 31.1`; the same with 81 and 161 basis functions),
   and between those multiples of `T*` at `l = 1.2, 1.4, 1.8, 2.0, 2.4`. Above that the lowest eigenvalue stays
   positive for every `δ ≤ 1/2` at every height tested (to 20000). At `l ≥ 1.8` a negative value below
   `10⁻¹⁴` is not resolved in float64.

## Reading (open)

Suzuki (arXiv:2606.09096v3, *Weil's quadratic form via the screw function*; read in
`../20261103_suzuki_source_composition_v1/`) attaches to each `a > 0` the operator `A_a` of Weil's form
on an interval and its lowest point `λ_a`, proves unconditionally that the characteristic functions of
`A_a − λ` (`λ < λ_a`) have only real zeros, and notes that `λ = 0` for all large `a` is equivalent to
RH. If his interval matches the support length `l` here (the normalization is not checked in this
note), `λ₁` above is a numerical value of `λ_a`, the lab's Lean windows give the sign of the same form
on compact-smooth packets up to `l = 39/25` (`8/5` once `../20261113_window_l85_v1/` is complete), and
Results 2 and 3 say which zeros fix `λ_a`.

The window floor at support `l` is an interpolation problem: a function of exponential type `l` has to
nearly vanish at the first `N(4T*)` zeros (22 to 54 here), and the smooth density of the zeros above
sets the price. The number of these zeros grows like `e^l · l`; the floor falls doubly exponentially, as
in Zhu's fit (`../20261113_window_route_position_v1/`). A certificate from the prime side has to resolve
this floor to absolute precision; a certificate from the zero side would need the zeros above `4T*` on
the critical line, which is RH itself. So this changes neither the cost of a window nor the open part;
it says which zeros a window "sees": below about `8πe^l` individually, above it only through their mean
density and the deviation from it (the remainder `S(t)`), which on the lowest mode is about 1 % at `4T*`.

About a single off-line zero, a window of support `l` carries the information "none below about
`2T* = 4πe^l`" (Result 4). For `8/5` (`L₀ = 4/5`, `l = 1.6`) that is height about 55, the first eleven
zeros, which are on the line by classical computation. Zeros are verified on the line far higher (to
`3·10¹²`, Platt and Trudgian 2021, `literature`); a window reaches that height only at
`l ≈ ln(3·10¹²/4π) ≈ 26`, `L₀ ≈ 13`, where the form has about `N(T*) ≈ 6·10¹²` nearly-zero directions.
Collective configurations of off-line zeros are not tested, and the windows stay necessary in the lab's
chain, since RH is the statement for every `L` and the chain is what links them to Mathlib's
`RiemannHypothesis`.

## Files and replay

Outputs: `explicit_20000.txt`, `explicit_50000.txt`, `model_20000.txt`, `inject_l16.txt`, `inject_grid.txt`.

`zeros.py n` (the first `n` ordinates, `zeros_<n>.npy`; about 3 minutes for 20000),
`explicit.py vec_<l>.pkl zeros_<n>.npy`, `model.py vec_<l>.pkl zeros_<n>.npy star0.5 star star2 star4 star16 star64`,
`inject.py l zeros_50000.npy B H1 H2 …` (`B = 40, 80` at `l = 1.6`; `B = 60` and `H = (1, 1.25, 1.5, 1.75, 2, 2.5, 3)·T*`
for `inject_grid.txt`),
with `vec_<l>.pkl` from `../20261113_window_zero_modes_v1/sweep.py` (`SAVE_VEC=1 python3 sweep.py DIR 60 l`;
pickles are not committed). python-flint, numpy, scipy.
