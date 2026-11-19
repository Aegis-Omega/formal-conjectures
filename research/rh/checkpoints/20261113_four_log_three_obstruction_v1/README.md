# The four-log-three reconstruction premise is false

Date: 2026-11-13. Evidence kind: `lean_kernel` (local) for the module here. Nothing is promoted.
**RH remains OPEN.**

## What it refutes

`AEGISOverlay/RHFourLogThreeWeightedRHBridgeV1.riemannHypothesis_of_weighted_four_log_three_reconstruction`
derives RH from

```lean
∀ source : WeilCompactSmoothGV1, WeilMomentConditionsV1 source → HasWeightedFourLogThreeReconstruction source
```

`HasWeightedFourLogThreeReconstruction source` asks for `source = packetSum z gs` with atoms
`WidthOneOneTwentyEightAt (gs i) (center i)` (log support in `[center i − 1/256, center i + 1/256]`),
`(65/32)·dist(i, j) ≤ center j − center i` for `i < j`, and further conditions (moments, a common mother
packet, centers at multiples of `4 log 3`). The first three conditions alone already fail: a sum of such
atoms vanishes in log coordinates outside intervals that are more than `2` apart, so it cannot be nonzero
at two log points at distance `1`, while `twoFine = gFine + translatePacket gFine 1` is moment-zero and
nonzero at `t₀` and `t₀ + 1`. So the consumer theorem can never be applied, as
`RHUniformBudgetObstructionV1` shows for `consumer_of_budget`. Nothing here concerns RH itself.

```lean
theorem AEGIS.RHSparseReconstructionObstructionV1.not_all_sparse_reconstructions :
    ¬ ∀ source : WeilCompactSmoothGV1, WeilMomentConditionsV1 source →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) (z : Fin (n + 1) → ℂ)
        (center : Fin (n + 1) → ℝ),
        source = packetSum z gs ∧
        (∀ i, WidthOneOneTwentyEightAt (gs i) (center i)) ∧
        (∀ i j : Fin (n + 1), i < j →
          1 ≤ Nat.dist i j ∧ (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
```

with `no_reconstruction_of_two_points` (the support argument) and `twoFine_moments`,
`twoFine_two_points` (the counterexample). The premise of the consumer implies the hypothesis of this
statement by dropping conjuncts; that one-line corollary (`¬ ∀ source, … → HasWeightedFourLogThreeReconstruction
source`) needs the 199-module import closure of `RHFourLogThreeWeightedRHBridgeV1` and is not compiled here.

## Receipt (local; Lean 4.33.1, Mathlib `0df444a`)

`RHSparseReconstructionObstructionV1.lean` compiles with default trust and with `--trust=0`: exit 0, no
errors, no warnings, no `sorry`; all three theorems report `[propext, Classical.choice, Quot.sound]`
(`AXIOMS_default.txt`, `AXIOMS_trust0.txt`). Its imports were built from the repository's source snapshots,
blob-identical to these tree files:

| module | blob | tree file |
|---|---|---|
| `RHRationalNinePacketPrimeWindowV1` | `7175f243` | `research/rh/aegis_pr721_fb983fd/lean/RHRationalNinePacketPrimeWindowV1.lean.src` |
| `RHFineMomentPacketV3` | `709bd274` | `research/rh/aegis_pr721_fb983fd/lean/RHFineMomentPacketV3.lean.src` |
| `RHGramExpansionV13` | `684a7e8b` | `research/rh/aegis_source_4d7578e/lean/RHGramExpansionV13.lean.src` |
| `RestrictedWeilCriterionKernelBridgeV10` | `f1733633` | `research/rh/aegis_source_4d7578e/lean/RestrictedWeilCriterionKernelBridgeV10.lean.src` |
| `WeilThreeBlockTranslatedPacketsV22` | `85d3ff56` | `research/rh/aegis_source_4d7578e/lean/WeilThreeBlockTranslatedPacketsV22.lean.src` |
| `WeilMixedAlgebraV2` | `0478a41a` | `research/rh/aegis_source_4d7578e/lean/WeilMixedAlgebraV2.lean.src` |
| `WeilLogCoordinateIsometryV21` | `481b2dce` | `research/rh/aegis_source_4d7578e/lean/WeilLogCoordinateIsometryV21.lean.src` |

The same-name copies under `AegisRH/PR606/` are different blobs (see
`../20261113_source_truth_graph_check_v1/` for how the lanes resolve names); a build of the corollary has to
compile this module against the sources its own closure uses.

## Context

Of the 52 theorems in `AEGISOverlay/` whose statement mentions `RiemannHypothesis`, two consumers are now known to
have false premises (`consumer_of_budget`, this one); no other premise among them is shown false here.
