# The diagonal of a moment-zero atom of log-width 1/128: 43/10

## What is new

There is one module, `WeilFineDiagonalQuadV1.lean`. It imports `WeilDiagonalQuadMomentV1`
(`20261122_eight_block_comb_v1`).

The hypotheses are:

* `LogSupportIn g (a − 1/256) (a + 1/256)`. This is definitionally `WidthOneOneTwentyEightAt g a` of
  `RHRationalNinePacketPrimeWindowV1`.
* `WeilMomentConditionsV1 g`.

These are exactly the properties of the atoms built by
`AEGISOverlay/RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_with_support`, the fine Gram
decomposition of every moment-zero packet. For those atoms the operator's chain uses
`RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3`, which gives `1.7722`.

### The proof

The Archimedean inner window `(0, 1/32]` is split at `1/128`.

* **`(1/128, 1/32]`** (`middle_integral_le`).
  * The log correlation vanishes there (`fine_corr_zero`), so the integrand is exactly `−E/sinh u`.
  * With `sinh u ≤ u e^u` this gives `∫ ≤ −e^{−1/32} · log 4 · E`, a gain of `1.3436 · E`.
  * The exact value of this piece is `1.3862 · E`. V3 bounds it pointwise and keeps `95/128 = 0.742 · E`.
* **`(0, 1/128]`** (`inner_fine_integral_le`).
  * This applies `WeilDiagonalQuadGainV1.quad_gain` on the window of width `1/128`.
  * The moment losses come from `WeilDiagonalQuadMomentV1` (`mean_le`, `qMom_lower`) together with the fine
    Cauchy–Schwarz `N² ≤ E/128` (`l1_sq_le_fine`). They cost at most `E/128`.
  * The gain is `e^{−1/32} (log 2 + 4/3 − 1/128) · E`, against the trivial cost `(1/128)(e^{1/64}/2) · E`.

### Theorems

* `fine_diagonal_quad_v1`:

      E · (tail − κ − e^{1/64}/256 + e^{−1/32} (3 log 2 + 4/3 − 1/128))  ≤  −Re B(g, g).

* `fine_constant_gt`: that constant exceeds `43/10`. The rational lower bound used is
  `32449/31500 + 3/256 + (63/65)(3 · 693/1000 + 4/3 − 1/128) = 4.3416`.
* `fine_diagonal_43_over_10`: `(43/10) · E ≤ −Re B(g, g)`.

## Numbers

These are floating-point checks (class (d)).

| quantity | value |
|---|---|
| fine diagonal, operator chain (`RHFineDiagonalUpgradeV3`) | 1.7722 |
| fine diagonal, rational lower bound proved here | 4.3416 |
| same constant with the true values of the tail, `log 4π`, `γ` | 4.3470 |

## Consequence, arithmetic only

The PR92 independent-eleven composition (`MATHEMATICAL_COMPOSITION.md` of
`AEGIS_PR92_Independent_Eleven_Kernel_20261110`) concludes `Re B(F, F) ≤ −(D − S) Σ E(h_i)|z_i|²`, with
`D = 5671/3200` and the weighted-row load `S = 25289/35500`, so `D − S = 1.0598`.

For the same eleven-packet geometry and the same load, `D = 43/10` would give `D − S = 127361/35500 ≈ 3.588`.

This has not been compiled into the operator's modules, which I did not modify. The atoms of the fine Gram
decomposition satisfy the hypotheses above, so `fine_diagonal_43_over_10` applies to each of them.

`riemannHypothesis_of_one_actual_mixed_budget_per_packet` asks, for each packet, for one fine decomposition with
`actualMixedDefect ≤ (5671/3200) Σ E`. The same argument with the diagonal `43/10` would ask only for
`actualMixedDefect ≤ (43/10) Σ E`. That per-packet budget remains the open input. By
`RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget`, the sharp signed version of it is equivalent
to RH.

## Not done here

* No change to the operator's chain. Rewiring `5671/3200` to `43/10` there is a separate step.
* No off-diagonal or mixed-term estimate. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and the earlier
  checkpoints.
* The module was built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built source:

    a6161d23df909f49d05b7811a3953adb5a4aced1a229639cd632a0641b00b828  WeilFineDiagonalQuadV1.lean
