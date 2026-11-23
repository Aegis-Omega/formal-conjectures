# Quadratic gain, moment diagonal 59/20, and the eight-block comb at width 1/32

## What is new

There are three modules:

* `WeilDiagonalQuadGainV1.lean`, which imports `WeilDiagonalMeanGainV1` (`20261122_seven_block_comb_v1`);
* `WeilDiagonalQuadMomentV1.lean`, which imports the module above and `WeilDiagonalMomentGainV1`;
* `WeilEightBlockCombV1.lean`, which imports the module above and `WeilSevenBlockCombV1`.

They take the fixed-width comb from seven blocks to **eight**, across the first resonance gap `k = 7`.

The seven-block README said that the per-gap norm bound cannot reach eight blocks. That was true for the diagonal
`2.19 · E` proved there. With the diagonal `2.99 · E` proved here, the norm bound is enough at gap 7, and no
phase-preserving estimate is needed for eight blocks.

### 1. Quadratic gain (`WeilDiagonalQuadGainV1`, Mathlib only)

Let `h` be continuous and vanish outside `[a, b]`, with `w = b − a`. Write `E = ∫‖h‖²`, `M = ∫ h`,
`C(s) = ∫ h(x+s) conj(h x)`, and let `Q = qMom h c` be the real quantity

    Q = Σ_{f = Re h, Im h} [ (∫ (x−c)² f)(∫ f) − (∫ (x−c) f)² ].

It does not depend on `c`. If `s ↦ (E − Re C(s))/s` is integrable on `(0, w]`, then

    (log 2 + 4/3) · E − 3‖M‖²/(2w) + 4Q/w³  ≤  ∫_{(0,w]} (E − Re C(s))/s ds        (quad_gain)

The proof replaces the constant `1/w` of the mean gain by `p(s) = (3 − 4(s/w)²)/w`. On `(0, w]` this still
satisfies `p(s) ≤ 1/s`, because `1 − 3u + 4u³ = (2u − 1)²(u + 1)`.

* **The `p` part is exact** (`setIntegral_Ioc_p_part`). It equals `(5/3) E − 3‖M‖²/(2w) + 4Q/w³`.
  * `∫_{(0,w]} s² Re C(s) ds = Q` comes from the second-moment identity
    `∫ s² A(s) ds = 2(∫(x−c)² a)(∫ a) − 2(∫(x−c) a)²` for the autocorrelation `A` of a real `a`
    (`integral_sq_autocorr`, by Fubini), together with evenness of `Re C`.
* **The `(1/s − p)` part** repeats the S1 column argument with the weight
  `wt2(s) = 1/s − 3/w + 4s²/w³ ≥ 0`.
  * The column weights sum to `−log P + 4P − 5/3`, where `P = (b−x)(x−a)/w² ≤ 1/4`.
  * This is at least `2 log 2 − 2/3` (`column_wt2`), which gives `(log 2 − 1/3) · E`.

### 2. Moment-zero diagonal `59/20` (`WeilDiagonalQuadMomentV1`)

For `WeilMomentConditionsV1 g`, both moments `∫ e^{±(t−a)/2} · logLift g` vanish (`moment_plus_centre`,
`moment_minus_centre`). Any combination of `e^{±(t−a)/2}` may therefore be subtracted from a weight
(`integral_kill`). With `N = ∫ ‖logLift g‖` and `|t − a| ≤ 1/64` on the support:

* `mean_le`: `M = ∫ (1 − cosh((t−a)/2)) · logLift g`, so `‖M‖ ≤ N/16384`;
* `first_moment_le`: `∫ (t−a) · logLift g = ∫ ((t−a) − 2 sinh((t−a)/2)) · logLift g`, so its norm is at most
  `N/8192`;
* both use `Real.abs_exp_sub_one_sub_id_le`;
* `qMom_lower`: `Q ≥ −N²/16777216`;
* `l1_sq_le`: `N² ≤ E/32` (Cauchy–Schwarz).

Each correction term in `quad_gain` is then at most `E/4096`. This gives:

* `diagonal_quad_moment_v1`:
  `E · (tail − κ − small + e^{−1/32}(log 2 + 4/3 − 1/2048)) ≤ −Re B(g, g)`;
* `quad_moment_constant_gt`: that constant exceeds `59/20`. The rational lower bound used is
  `32449/31500 + (31/32)(693/1000 + 4/3 − 1/2048) = 2.99266`;
* `width_diagonal_59_over_20`: `(59/20) · E ≤ −Re B(g, g)`. The hypotheses are width `1/32` and both moments.

### 3. Eight blocks (`WeilEightBlockCombV1`)

The blocks are `blk g j = T_{j log 2} g` for `j = 0, …, 7`.

* **`prime_window7`.** In the log-window of radius `1/32` around `7 log 2`, every positive integer is
  `125 = 5³`, `127`, `128 = 2⁷`, `131`, or has `Λ = 0`. The others are `126`, `129`, `130` and `132`.
* **`term_norm_le`.** Off the centre the mixed value is not known exactly. It is bounded through the V28 identity
  `e^{u/2} · mixed(e^u) = C(u + d₂ − d₁)` and `‖C‖ ≤ E` (V25):

      ‖Λ(m) · (mixed(m) + m⁻¹ · mixed(1/m))‖  ≤  Λ(m) · m^{−1/2} · E.

* **`prime_sum7_norm`.** The prime sum at gap 7 reduces to the four terms above (`tsum_eq_sum`).
  * The masses are bounded by `mass_125`, `mass_127`, `mass_128` and `mass_131`. They use
    `log m ≤ 7 log 2 + (m/128 − 1)` and rational bounds on `m^{−1/2}`.
  * The total is `‖prime sum‖ ≤ 1.06115 · E`; the floating-point value is `1.06102`.
* **`blk_cross_norm_gap7`.** Adding the Archimedean bound `E/200` (V32) gives `‖B‖ ≤ (1067/1000) · E` at gap 7.
  Gaps `1, …, 6` keep the seven-block ceilings (`cbar8_eq`).
* **`blk_diag8`.** The diagonal is `59/20 · E`.
* **`eight_ceiling_quadratic`.** This is the unweighted Schur test. The largest row sum of the ceilings is
  `2.586 ≤ 13/5`.
* **`eight_block_gram_bound`.** For every `z : Fin 8 → ℂ`,

      Re Σ_{i,j} z_i conj(z_j) B(blk g i, blk g j)  ≤  −(1/4) · E · Σ ‖z_i‖².

## Numbers

These are floating-point checks (class (d)).

| quantity | value |
|---|---|
| moment-zero diagonal, rational lower bound proved here | 2.9927 |
| same constant with the true values of the tail, `log 4π`, `γ`, `e^{−1/32}` | 2.9985 |
| true moment-zero diagonal (PR #835 §3, `n = 96`) | 3.65 |
| resonance mass `Σ Λ(m)/√m`, gap 7 (`125, 127, 128, 131`) | 1.0610 |
| resonance mass, gap 8 (`251, 256, 257, 263`) | 1.0818 |
| resonance mass, gap 9 (`499, 503, 509, 512, 521, 523`) | 1.4101 |
| spectral radius, eight blocks, ceilings `cbar8` | 2.3439 |
| spectral radius, nine blocks, ceilings `mass + 1/200` | 2.9648 |
| spectral radius, ten blocks, ceilings `mass + 1/200` | 3.8993 |

* **Nine blocks** look reachable by the same route. The ceilings must then be rational bounds close to
  `mass + 1/200`; the rounded `cbar8` values give `2.9962`. The Schur test must also be weighted. The margin is
  small, about `0.03`. This is not done here.
* **Ten blocks** are out of reach of any per-gap norm bound. The spectral radius `3.90` exceeds even the true
  moment-zero diagonal `3.65`. From gap 9 on, the resonance terms need signed estimates that keep the phases
  (edge E2 of PR #835).

## Not done here

* **Nine blocks** (gap 8), as described above.
* **Gaps `k ≥ 9`** (edge E2): phase-preserving bounds.
* **Combs versus the full class** (edge E3): no link from combs to general packets of the same width.
* **The sharp moment-zero diagonal.** The proved value is `2.99`, against about `3.65`.
* No window statement. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and the earlier
  checkpoints.
* All three modules were built at default trust and again with `--trust=0`.
* Every run exits 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built sources:

    613e1d220ea7a64f207e5d2bde20ecd26ad007f2d40f54978f8e63cc8da45a1d  WeilDiagonalQuadGainV1.lean
    8aa6f5c39339ece3fe6cd1c0dc72f52066b93ba6d5e1c406570bf219503d4758  WeilDiagonalQuadMomentV1.lean
    80a77aafa0bd254e5940b1c5ad09e02007900dc0cd16a0b236454dc7601af070  WeilEightBlockCombV1.lean
