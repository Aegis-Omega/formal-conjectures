# The operator's fine Gram chain with the diagonal 43/10

## What is new

This checkpoint adds one module, `WeilFineChain43V1.lean`. It imports:

* `AEGISOverlay.RHActualUniversalFineGramV1`, the operator's module, unmodified, from the PR92 eleven-kernel
  packet;
* `WeilFineDiagonalQuadV1`, from checkpoint `20261122_fine_diagonal_quad_v1`.

The operator's partition (`every_moment_zero_packet_actual_fine_gram_with_support`) produces atoms `gs i` with
both moments and `WidthOneOneTwentyEightAt (gs i) (center i)`. By definition that is
`LogSupportIn (gs i) (center i − 1/256) (center i + 1/256)`, which is exactly the hypothesis of
`fine_diagonal_43_over_10`. So every atom of the constructed decomposition has the diagonal
`(43/10) E ≤ −Re B` in place of `5671/3200`.

### Theorems

| theorem | what it gives |
|---|---|
| `every_moment_zero_packet_fine_gram_43_10` | the operator's constructed decomposition, with diagonal `43/10` on every atom |
| `fine_mixed_defect_lower_bound_43` | `(43/10) Σ E − actualMixedDefect ≤ −Re Σ_{i,j} B`; every mixed entry is kept |
| `every_packet_fine_mixed_defect_lower_bound_43` | the same for every moment-zero packet, against `−Re W(g ⋆ g)` |
| `riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet` | a **conditional** consumer: RH follows if every packet has *some* width-1/128 moment-zero decomposition with `actualMixedDefect ≤ (43/10) Σ E` |
| `actual_fine_gram_coercive_of_signed_real_row_43` | the operator's signed real-row Schur consumer, for any row bound `R` with `2R + δ ≤ 43/10` (operator: `R ≤ 57430/65536`) |
| `actual_far_fine_gram_coercive_of_geometric_arch_prime_row_43` | the operator's far geometric-Arch consumer, for any prime row budget `R` with `2(R + 254/65536) + δ ≤ 43/10` (operator: `R ≤ 57176/65536`) |

In the last two theorems the diagonal is derived from width and moments, not assumed.

* For the far consumer, for example, `R = 2` with `δ = 29/100` is admissible.
* The admissible prime row budget grows by a factor of about 2.46.

## What this does not do

* **The per-packet budget `hcert` is not proved.** This module does not prove RH and must not be read as an
  unconditional proof.
* The operator's `rh_iff_one_actual_sharp_signed_budget` gives the exact equivalence with the sharp budget
  `actualMixedDefect ≤ −Σ Re B(gs i, gs i)`.
  * The `43/10` budget here implies that sharp budget.
  * It is still a stronger, merely sufficient, condition.
* **The form quantifying over ALL decompositions is deliberately not used.**
  * The pair decomposition `h + (−h)` of `AEGISOverlay.RHUniformBudgetObstructionV1` refutes it for `43/10` as
    well, because `fine_constant_gt` makes the margin strict.
  * This argument is not formalized here.
* **Free positions.** Prime costs for far-separated atoms at log-gap `d` grow roughly like `e^{d/2}/64`, so a
  free-position row bound is not available from norm estimates. The row consumers here only relax the constant.

## Build

* **Toolchain.** Lean 4.33.1 + Mathlib, at the revision checked by the packet's `replay.sh`.
* **Base chain.** All modules are built against the `--trust=0` replay of the PR92 eleven-kernel packet.
  * That is 186 of 186 modules, with `SHA256SUMS` checked.
  * `AEGISOverlay/RHActualUniversalFineGramV1.lean` has sha256 `1db180ef…5d34`.
* **Dependencies, rebuilt in the same chain.** Eight modules, each byte-identical (same git blob) to the copy
  already on this branch. They are not re-uploaded here.

  | checkpoint | modules |
  |---|---|
  | `20261121_arch_l1_v32` | `WeilLogCorrelationL1V1` |
  | `20261122_diagonal_log_gain_v1` | `WeilDiagonalLogGainS1V1`, `WeilDiagonalLogGainV1` |
  | `20261122_seven_block_comb_v1` | `WeilDiagonalMeanGainV1`, `WeilDiagonalMomentGainV1` |
  | `20261122_eight_block_comb_v1` | `WeilDiagonalQuadGainV1`, `WeilDiagonalQuadMomentV1` |
  | `20261122_fine_diagonal_quad_v1` | `WeilFineDiagonalQuadV1` |
* **Trust levels.** Every module was built at default trust and again with `--trust=0`.
* **Result.** Exit 0, no errors, no warnings, no `sorry`. Every `#print axioms` lists only
  `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the new source:

    c6dd52379dc5621815106546f2c5c2f9b4547adb9e9a708c47759707fbb710fa  WeilFineChain43V1.lean
