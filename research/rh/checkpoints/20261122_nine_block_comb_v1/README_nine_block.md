# The nine-block comb at width 1/32, with the gap-7 and gap-8 resonances

## What is new

There is one module, `WeilNineBlockCombV1.lean`. It imports `WeilEightBlockCombV1` (`20261122_eight_block_comb_v1`).

It takes the fixed-width comb from eight blocks to **nine**. This is the last comb size that a per-gap norm bound
can reach (see Numbers).

* **Diagonal `299/100`.** `width_diagonal_299_over_100` restates the constant of
  `WeilDiagonalQuadMomentV1.diagonal_quad_moment_v1` with the sharper `e^{−1/32} > 63/65`
  (`exp_neg_one_div_32_gt`). The rational lower bound is `2.99364`.
* **Gap 8** (`prime_window8`). The log-window of radius `1/32` around `8 log 2` holds `249, …, 264`. Of these,
  `251`, `256 = 2⁸`, `257` and `263` are prime powers. The other twelve integers have two distinct prime factors,
  so `Λ = 0`.
* **`prime_sum8_norm`.** As at gap 7, each term is bounded by `Λ(m) · m^{−1/2} · E` (`term_norm_le`).
  * The bounds use `log m ≤ 8 log 2 + (m/256 − 1)` and rational bounds on `m^{−1/2}`
    (`mass_251`, `mass_256`, `mass_257`, `mass_263`).
  * The total is `‖prime sum‖ ≤ 1.081922 · E`; the floating-point value is `1.081821`.
* **Sharper ceilings** (`cbar9`).
  * For `k = 1, …, 6` the ceiling is within `10⁻⁴` of `log 2 · 2^{−k/2} + 1/200` (`prime_coeff_le9`, with
    `2^{−1/2} ≤ 0.70711`).
  * For `k = 7` it is `1.0662`, and for `k = 8` it is `1.0870`. Both are the resonance mass plus `E/200` (V32).
  * The eight-block ceilings were too coarse here: they give a spectral radius `2.9962`, which is above `2.99`.
* **`nine_ceiling_quadratic`.** This is a weighted Schur test with weights
  `(1, 829/1000, 577/1000, 59/100, 297/500, 59/100, 577/1000, 829/1000, 1)`, close to the Perron vector.
  * The largest weighted row sum is `2.96594 ≤ 297/100`.
  * The spectral radius of the ceiling matrix is `2.96527`.
* **`nine_block_gram_bound`.** For every `z : Fin 9 → ℂ`,

      Re Σ_{i,j} z_i conj(z_j) B(blk g i, blk g j)  ≤  −(1/50) · E · Σ ‖z_i‖².

  * The margin is small: `2.99 − 2.97 = 1/50`.
  * This theorem needs `set_option maxHeartbeats 1600000` for the 81-term expansion.

## Numbers

These are floating-point checks (class (d)).

| quantity | value |
|---|---|
| moment-zero diagonal, rational lower bound | 2.9936 |
| true moment-zero diagonal (PR #835 §3, `n = 96`) | 3.65 |
| spectral radius, nine blocks, ceilings `cbar9` | 2.9653 |
| spectral radius, ten blocks, ceilings `mass + 1/200` | 3.8993 |
| resonance mass, gap 9 (`499, 503, 509, 512, 521, 523`) | 1.4101 |

* **Ten blocks** are out of reach of any per-gap norm bound. The spectral radius `3.90` exceeds even the true
  moment-zero diagonal `3.65`.
* From gap 9 on, the resonance terms need signed estimates that keep the phases (edge E2 of PR #835).
* So the comb route with norm bounds stops at nine blocks.

## Not done here

* **Gaps `k ≥ 9`** (edge E2): phase-preserving bounds.
* **Combs versus the full class** (edge E3): no link from combs to general packets of the same width.
* **The sharp moment-zero diagonal.** The proved value is `2.99`, against about `3.65`.
* No window statement. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and the earlier
  checkpoints.
* The module was built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built source:

    953865aeaed1205eac47032a22d5662d01efcd810670226cde7f84370f8ed5e8  WeilNineBlockCombV1.lean
