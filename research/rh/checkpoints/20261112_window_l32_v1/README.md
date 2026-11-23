# The window 2r ≤ 3/2 and the exhaustion step with frontier 3/4

Date: 2026-11-12. Status: **kernel-checked locally**, default trust and `--trust=0`. Not run in CI.
**RH remains OPEN.** The windows `L > 3/4` are not proved.

## Result

```lean
theorem AEGIS.CvSWindowL32V1.window_L32 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 3 / 2) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

theorem AEGIS.RHWindowL32ExhaustionV1.window_le_three_quarters {L : ℝ} (hL : L ≤ 3 / 4) :
    WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL32ExhaustionV1.final_sign_iff_windows_above_three_quarters :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 3 / 4 < L → WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL32ExhaustionV1.rh_iff_windows_above_three_quarters :
    RiemannHypothesis ↔ ∀ L : ℝ, 3 / 4 < L → WindowArithmeticNonpositiveV1 L
```

`RiemannHypothesis` is Mathlib's (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`), through
`V13Scratch.final_sign_iff_rh_v13`. The last theorem is a reduction, not RH: it moves the open part
from the windows `L > 11/16` (`../20261031_window_l118/RHWindowL118ExhaustionV1.lean`) to the windows
`L > 3/4`.

## How

`CvSWindowL32V1.window_L32` is `CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment` with
`M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`, no correction terms, and these inputs:

| premise | source |
|---|---|
| `3/2 < log 5` | `log_five_gt` (here, from `Real.exp_one_lt_d9`) |
| trace family of the 299 atoms and the two exponentials | `augment_family`, `augment_cont` (here) |
| slack, trace bound, `66 ≤ (2π)²·(3/2)·(33/20 − T/(2π))` | `CvSTraceCertL32V1.trace_premises_L32` (`../20261110_window_l32_trace_port_v1/`) |
| atoms `ctr i = i − 149`, `\|ctr i\| ≤ 149 < 151` | `CvSRelRowFormL32V1.ctr` |
| `\|τ_n\| ≤ 15` for `\|n\| ≥ 151` | `CvSTauFarL32V1.tau_abs_le_far` (`../20261112_window_l32_rowcert_v1/`) |
| rows `NP = 900`, `Brow 4 ≤ 60 Q_CvS 4`, `0 ≤ Q_CvS 4` | `CvSRelRowHBL32V1.hB`, `Q_nonneg` (same checkpoint) |

The row condition `Brow/(2π·LT)/gap ≤ 2π·Q` follows from `hB`, `Q_nonneg` and the `κ = 66` bound.
`RHWindowL32ExhaustionV1` is `RHWindowL118ExhaustionV1` with `window_L32` in place of `window_L118`
and `3/4` in place of `11/16`.

## Replay

Lab closure: the 922-module closure of `CvSActualMomentWindowJoinV1` plus the 97 further modules of
`V13Scratch` and `WeilWindowExhaustionV1` (from the full lab plan), built with
`../20261020_row_budget_bridge/window_l65_source/build.py`: 1019 / 1019 PASS. Then the L32 modules
of the four earlier L32 checkpoints, then

```
lean CvSWindowL32V1.lean
lean RHWindowL32ExhaustionV1.lean
```

## Receipt (local, 2026-11-12; Lean 4.33.1, Mathlib `0df444a`)

| module | default (s) | `--trust=0` (s) | errors | `sorry` |
|---|---:|---:|---:|---:|
| `CvSWindowL32V1` | 18 | 17 | 0 | 0 |
| `RHWindowL32ExhaustionV1` | 7 | 7 | 0 | 0 |

At `--trust=0` the imported L32 modules (trace, τ, diagonal, row certificate, far τ bound) are
the `--trust=0` builds of their checkpoints; the lab modules (`CvSActualMomentWindowJoinV1`,
`V13Scratch`, `WeilWindowExhaustionV1` and their closure) are the default-trust builds above.

```
'AEGIS.CvSWindowL32V1.augment_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSWindowL32V1.window_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL32ExhaustionV1.window_le_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL32ExhaustionV1.final_sign_iff_windows_above_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL32ExhaustionV1.rh_iff_windows_above_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence kind: `lean_kernel` (local).

## Remaining

The windows `L > 3/4`. Not RH.
