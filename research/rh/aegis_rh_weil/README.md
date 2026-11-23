# AEGIS RH Weil chain: one Lake project

This directory is a single Lake package for the AEGIS Weil chain. One command builds it:

    cd research/rh/aegis_rh_weil && bash build.sh

It copies no Lean source. `lakefile.toml` points at files that are already on this branch, and `build.sh`
checks each file's SHA-256 before it builds.

## What it builds: 200 modules in 11 libraries

| library | modules | source |
|---|---|---|
| `PR92Closure` | 186 | the PR92 eleven-kernel packet, `../checkpoints/20261110_independent_eleven_analytic_closure_v1/AEGIS_PR92_Independent_Eleven_Kernel_20261110.zip` (SHA-256 `014879d4…5d6f`); `build.sh` unpacks it to `.pr92/` |
| `WeilArchL1` | `WeilLogCorrelationL1V1` | `../checkpoints/20261121_arch_l1_v32/` |
| `WeilDiagonalLogGain` | `WeilDiagonalLogGainS1V1`, `WeilDiagonalLogGainV1` | `../checkpoints/20261122_diagonal_log_gain_v1/` |
| `WeilSevenBlock` | `WeilDiagonalMeanGainV1`, `WeilDiagonalMomentGainV1` | `../checkpoints/20261122_seven_block_comb_v1/` |
| `WeilEightBlock` | `WeilDiagonalQuadGainV1`, `WeilDiagonalQuadMomentV1` | `../checkpoints/20261122_eight_block_comb_v1/` |
| `WeilFineDiagonal` | `WeilFineDiagonalQuadV1` | `../checkpoints/20261122_fine_diagonal_quad_v1/` |
| `WeilFineChain43` | `WeilFineChain43V1` | `../checkpoints/20261123_fine_chain_43_v1/` |
| `WeilFineBudgetEquiv` | `WeilFineBudgetEquivV1` | `../checkpoints/20261123_fine_budget_equiv_v1/` |
| `WeilStrictSign` | `WeilStrictSignNondegV1`, `WeilStrictSignMellinV1` | `../checkpoints/20261123_strict_sign_nondeg_v1/` |
| `WeilMellinZeroDensity` | `WeilMellinZeroDensityV1` | `../checkpoints/20261123_mellin_zero_density_v1/` |
| `AegisRHWeilCheck` | `AegisAlpogeBridgeCheckV1` | this directory |

`AegisAlpogeBridgeCheckV1` is new. It imports the chain and restates its Weil-side consequences as `example`s,
with RH as an explicit hypothesis `hRH`.

Main theorems:

* `AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive` — the endpoint of the PR92 packet.
* `AEGIS.WeilFineChain43V1.riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet`.
* `AEGIS.WeilFineBudgetEquivV1.fineBudget_iff_strictWeilSign`: `c ≤ 43/10 → (FineBudget c ↔ StrictWeilSign)`.
* `AEGIS.WeilFineBudgetEquivV1.riemannHypothesis_of_strictWeilSign`.
* `AEGIS.WeilStrictSignNondegV1.strictWeilSign_iff_rh_and_nondeg`: `StrictWeilSign ↔ RH ∧ WeilNondegenerate`.
* `AEGIS.WeilStrictSignMellinV1.strictWeilSign_iff_rh_and_mellin`: `StrictWeilSign ↔ RH ∧ MellinZeroNonvanishing`.
* `AEGIS.WeilMellinZeroDensityV1.mellinZeroNonvanishing_of_distinctZeroSuperlinear`:
  `DistinctZeroSuperlinear → MellinZeroNonvanishing`, where `DistinctZeroSuperlinear` says that the number of
  distinct nontrivial zeros of `ζ` of modulus `≤ R` is not `O(R)`.

## Requirements

* `elan`. `lean-toolchain` selects Lean 4.33.1.
* Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. `lake-manifest.json` has the same package pins as the
  repository's root `lake-manifest.json`; only the package name differs.
* `unzip` and `sha256sum`.
* `build.sh` runs `lake exe cache get` to download the Mathlib build. `bash build.sh --no-cache` skips that step.

## Verification (2026-11-23)

* **Full compile.** The same 199 sources, byte-identical, were compiled in one Lake package against the same
  Lean and Mathlib.
  * `lake build`: exit 0, `Build completed successfully (8905 jobs)`, 887 s, 0 errors.
  * There is no `sorry`. Warnings occur in 43 files of the PR92 packet and in none of the other 13 modules.
  * 759 `#print axioms` reports list only `propext`, `Classical.choice` and `Quot.sound`; one more reports no
    axioms.
* **This layout.**
  * The source checks in `build.sh` pass.
  * `lake build --no-build` with the oleans of that compile ends with `All targets up-to-date (8914 jobs)`,
    exit 0. So Lake resolves every module through this `lakefile.toml`, and the module traces match the compiled
    build.
* **`WeilMellinZeroDensityV1`** (added later the same day).
  * It was compiled with `lean` against the oleans of the other 199 modules: exit 0, no errors, no warnings, at
    default trust and with `--trust=0`.
  * In this layout `lake build --no-build` reports it as the only out-of-date target (exit 3). So Lake resolves
    it, but it has not been compiled through Lake.
* **Not run in this layout:** a fresh `lake exe cache get` and a fresh compile.
* **Trust level.** The Lake build uses default trust. The `--trust=0` builds are separate:
  * the PR92 packet: 186 of 186 modules;
  * the thirteen checkpoint modules: recorded in each checkpoint's README.

## What this does not do

* It does not prove RH. `StrictWeilSign`, `WeilNondegenerate`, `MellinZeroNonvanishing` and
  `DistinctZeroSuperlinear` are not proved.
* It does not import Levent Alpöge's Lean library. The `AegisRHWeilCheck` examples keep RH as a hypothesis.
