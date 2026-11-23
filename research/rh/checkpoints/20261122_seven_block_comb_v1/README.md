# Mean gain, moment diagonal 109/50, and the seven-block comb at width 1/32

## What is new

There are three modules:

* `WeilDiagonalMeanGainV1.lean`, which imports S1 (`20261122_diagonal_log_gain_v1`) and `WeilLogCorrelationL1V1`
  (`20261121_arch_l1_v32`);
* `WeilDiagonalMomentGainV1.lean`, which imports the module above and `WeilDiagonalLogGainV1`;
* `WeilSevenBlockCombV1.lean`, which imports the module above and `WeilFiveBlockCombV1` (`20261122_five_block_comb_v1`).

They take the fixed-width comb from five blocks to **seven**, which is the last gap before the first resonance.
PR #835 §4.4 proposed to reach seven blocks with a Legendre-mode gain (about `3.16 · E`). The route here is
elementary and gives a smaller constant (`2.19 · E`), which is enough for seven blocks.

### 1. Mean gain (`WeilDiagonalMeanGainV1`, Mathlib only)

Let `h` be continuous and vanish outside `[a, b]`, with `w = b − a`. Write `E = ∫‖h‖²`, `M = ∫ h` and
`C(s) = ∫ h(x+s) conj(h x)`. Then

    (log 2 + 1/2) · E − ‖M‖²/(2w)  ≤  ∫⁻_{(0,w]} (E − Re C(s))/s ds        (mean_gain_lintegral)

The proof splits `1/s = 1/w + (1/s − 1/w)` on `(0, w]`.

* **The `1/w` part is exact** (`setIntegral_Ioc_reCorr`): `∫_{(0,w]} Re C = ‖M‖²/2`. The steps are:
  1. `Re C` is the sum of the autocorrelations of `Re h` and `Im h`.
  2. Fubini for each of them is `WeilLogCorrelationL1V1.integral_autocorr_real`.
  3. `Re C` is even and vanishes beyond `w`.
* **The `(1/s − 1/w)` part** repeats the S1 column argument (`row_key`, `column_wt`).
  * The column weights are now `log(w/(b−x)) − (x−a)/w` and `log(w/(x−a)) − (b−x)/w`.
  * They sum to `L(x) − 1 ≥ 2 log 2 − 1`, which gives `(log 2 − 1/2) · E`.

### 2. Moment-zero diagonal `109/50` (`WeilDiagonalMomentGainV1`)

* `mean_sq_le`: for `WeilMomentConditionsV1 g` the moment `∫ e^{t/2} · logLift g = 0` gives
  `M = ∫ (1 − e^{(t−a)/2}) · logLift g`.
  * On the support `|1 − e^{(t−a)/2}| ≤ 1/64` (`Real.abs_exp_sub_one_le`).
  * Cauchy–Schwarz then gives `‖M‖² ≤ E/(32 · 4096)`.
* `diagonal_moment_gain_v1`:
  `E · (tail − κ − small + e^{−1/32}(log 2 + 1/2 − 1/8192)) ≤ −Re B(g, g)`.
  The constant is `2.19117` numerically.
* `width_diagonal_109_over_50`: `(109/50) · E ≤ −Re B(g, g)`. The hypotheses are width `1/32` and both moments.

### 3. Seven blocks (`WeilSevenBlockCombV1`)

The blocks are `blk g j = T_{j log 2} g` for `j = 0, …, 6`.

* **`prime_window`.** For a gap `k ≤ 6`, every positive integer in the log-window of radius `1/32` around
  `k log 2` is either `2^k` or has `Λ = 0`.
  * The extra integers are `33 = 3·11` at `k = 5`, and `63 = 3²·7`, `65 = 5·13`, `66 = 2·3·11` at `k = 6`.
  * They are excluded through `isPrimePow_iff_unique_prime_dvd`.
* **`blk_prime_sum6`.** The prime part is still exactly `log 2 · 2^{−k/2} · E`.
* **`blk_cross_norm7`.** The ceilings `cbar7` are `101/200, 71/200, 51/200, 9/50, 13/100, 47/500` for `k = 1, …, 6`.
  Each is the prime part plus the Archimedean bound `E/200` (V32).
* **`blk_diag7`.** The diagonal is `109/50 · E`. Moments are preserved by translation.
* **`seven_ceiling_quadratic`.** This is the Schur test with weights `(7/10, 17/20, 19/20, 1, 19/20, 17/20, 7/10)`. The
  largest weighted row sum is `1.97 ≤ 2`.
* **`seven_block_gram_bound`.** For every `z : Fin 7 → ℂ`,

      Re Σ_{i,j} z_i conj(z_j) B(blk g i, blk g j)  ≤  −(1/10) · E · Σ ‖z_i‖².

## Numbers

These are floating-point checks (class (d)).

| quantity | value |
|---|---|
| moment-zero diagonal proved here | 2.1912 |
| true moment-zero diagonal (PR #835 §3, `n = 96`) | 3.65 |
| spectral radius, seven blocks, ceilings `log 2 · 2^{−k/2} + 1/200` | 1.9231 |
| spectral radius, eight blocks, same ceilings | 2.0868 |

* At eight blocks the gap `k = 7` enters, and the window around `7 log 2` holds `125, 127, 128, 131`.
* The prime mass there is `1.061`, against `0.061` for `2^7` alone (PR #835 §3).
* So the per-gap norm bound used here cannot reach eight blocks, even though the diagonal would allow it if only
  `2^7` were present.
* This is the resonance frontier, edge E2 of PR #835. It needs signed estimates that keep the phases.

## Not done here

* **Gaps `k ≥ 7`** (edge E2).
* **Combs versus the full class** (edge E3): no link from combs to general packets of the same width.
* **The sharp moment-zero diagonal.** The proved value is `2.19`, against about `3.65`. The Legendre identity of
  §4.2 is not formalised.
* No window statement. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and the earlier
  checkpoints.
* All three modules were built at default trust and again with `--trust=0`.
* Every run exits 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built sources:

    0ca4a2bd0cf59cafb230010b766853caab0f27e2c2e08bceba6227e50404fa8c  WeilDiagonalMeanGainV1.lean
    8e236f1783f60bb5b249782735462111d251c7045c2adb86afaf2d1b3868d2d3  WeilDiagonalMomentGainV1.lean
    c4503cf75fd0133bed71e2d059882d445dd047685fe15eb71ff22a7a0b670e16  WeilSevenBlockCombV1.lean
