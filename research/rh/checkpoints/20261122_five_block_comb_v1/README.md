# Five-block dyadic comb at width 1/32

## What is new

There is one module, `WeilFiveBlockCombV1.lean`. It imports:

* `WeilSeparatedArchL1BridgeV32`, from checkpoint `20261121_arch_l1_v32`;
* `WeilDiagonalLogGainV1`, from checkpoint `20261122_diagonal_log_gain_v1`.

It implements step 3 of the "key next step" in `research/rh/atomic_map_v1` (AEGIS-OMEGA PR #835, §4.5): the
five-block fixed-width comb, with margin `1/10 · E`.

### Setting

* `g : WeilCompactSmoothGV1` with `WidthOneThirtyTwoAt g a` (total log-width `1/32`) and `WeilMomentConditionsV1 g`.
* The blocks are `blk g j = translatePacket g (j · log 2)` for `j = 0, …, 4`.

### Theorems

1. `nat_eq_pow_of_log_window`: if `k ≤ 4`, `m > 0` and `|log m − k log 2| ≤ 1/32`, then `m = 2^k`. The inputs are
   `exp(1/32) < 65/63` and `exp(−1/32) > 63/65` (V1 coth tail). The bound `k ≤ 4` is where this simple argument
   stops: at `k = 5` the window `(31.015, 32.99)` still holds only `32`, but `32·2/63 > 1`.
2. `blk_mixed_nat_zero` and `blk_mixed_inv_nat_zero`: the mixed correlation of blocks `i < j` vanishes at every
   positive integer, and at every reciprocal integer except `2^{−(j−i)}`. These generalise V29 from gaps `1, 2` to
   gaps `≤ 4`.
3. `blk_mixed_center` and `blk_prime_sum` give the exact prime part:
   `WeilPrimeSumV1 (mixed (blk g i) (blk g j)) = log 2 · e^{−k log 2/2} · E` with `k = j − i`. This generalises V30.
4. `blk_cross_norm` bounds every pair `i ≠ j` by `‖B(blk i, blk j)‖ ≤ cbar(|i−j|) · E`.
   * The ceilings are `cbar = 101/200, 71/200, 51/200, 9/50` for `k = 1, …, 4`.
   * Each ceiling is the prime part plus the Archimedean bound `E/200` from
     `WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_l1`.
   * Pairs with `i > j` follow from `B_hermitian`.
5. `blk_diag`: `17/10 · E ≤ −Re B(blk j, blk j)`, from `width_diagonal_17_over_10`.
6. `five_ceiling_quadratic` is a weighted Schur test. With weights `(4/5, 19/20, 1, 19/20, 4/5)` it shows that the
   off-diagonal ceilings sum to at most `8/5 · Σ x_i²`. The exact maximal weighted row sum is `611/400`.
7. **`five_block_gram_bound`**: for every `z : Fin 5 → ℂ`,

       Re Σ_{i,j} z_i · conj(z_j) · B(blk g i, blk g j)  ≤  −(1/10) · E · Σ_i ‖z_i‖².

   * By `RHGramExpansionV13.B_packetSum`, the left side is `Re B(Σ z_i blk_i, Σ z_i blk_i)`.
   * The blocks have disjoint log-supports, since their gap is `log 2 − 1/32 > 0`. Additivity of the energy over
     such blocks is not restated here.

## Numbers

These are floating-point checks (class (d)), with `c_k = log 2 · 2^{−k/2} + 1/200`:

| quantity | value |
|---|---|
| spectral radius of the ceiling matrix, five blocks | 1.5018 |
| spectral radius of the ceiling matrix, six blocks | 1.7304 |
| diagonal | 1.7067 |

So five blocks is the limit of this argument with the moment-free diagonal. PR #835 §3 reaches the same conclusion.
Six blocks need the moment gain of §4.4.

## Not done here

* **Six or more blocks.** These need the second-stage diagonal of §4.4 (about `3.16`, using the moments), and a
  window argument for gaps `5, 6`.
* **Gaps `k ≥ 7`.** Other prime powers enter there (125, 127, 131 at `k = 7`), and the per-gap norm bound used
  here fails numerically (PR #835 §3). This is edge E2 of PR #835.
* **The comb class is not the full class.** This is edge E3. No density or approximation link from combs to general
  packets of the same width exists in the repository.
* No window statement. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans, V32 and the
  diagonal-log-gain modules.
* Built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built source:

    8800aaef74602e9b56867114430839a2827d2b303339409e3ffeead9ec1d9bb7  WeilFiveBlockCombV1.lean
