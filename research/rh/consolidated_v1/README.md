# The Riemann Hypothesis, consolidated into one statement

`src/RHConsolidatedV1.lean` collects every proved RH result of this repository into one theorem.
All of it is kernel-checked from the sources listed in `manifest.json`, with axioms
`[propext, Classical.choice, Quot.sound]` and no `sorry`.

```lean
theorem consolidated :
    (∀ L : ℝ, 0 ≤ L → L < 21 / 40 → WindowArithmeticNonpositiveV1 L) ∧
    (RiemannHypothesis ↔ ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L) ∧
    (∃ t₁ … t₉, 14 ≤ t₁ < ⋯ < t₉ ≤ 48.9 ∧ ζ(1/2 + tᵢ i) = 0 for every i)
```

* **`rh_iff_all_windows`**: `RiemannHypothesis ↔ ∀ L > 0, WindowArithmeticNonpositiveV1 L`.
  `WindowArithmeticNonpositiveV1 L` says that for every smooth compactly supported `g` on `(0, ∞)`
  with vanishing moments and log-support in `[-L, L]`, the arithmetic side of Weil's explicit
  formula for `g * g̃` has nonpositive real part. The chain is `rh_iff_final_sign_v13`
  (RH ⇔ nonnegativity of the zero-side quadratic form), `final_sign_residual_iff_weil_negativity_v1`
  and `weil_compact_smooth_negativity_iff_all_windows_v1`.
* **`windows_below_21_40`**: the condition holds for every `0 ≤ L < 21/40`. The proof is the
  `L = 21/20` Krein certificate: 133 batch modules, each a `decide +kernel` check of a cell of
  `[0, 3000]`, glued in `RHKreinL105AllV1`, with an analytic tail beyond `3000`.
* **`rh_iff_windows_from_21_40`**: hence `RiemannHypothesis` is equivalent to the window condition
  for `L ≥ 21/40` alone.
* **`nine_zeros`**: nine zeros of `ζ` on the critical line, from `research/rh/critical_line_v1`.

## What is open

One statement: `∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L`. By
`rh_iff_windows_from_21_40` it is equivalent to the Riemann Hypothesis, so this directory does
**not** prove RH; it reduces it to that statement. `WindowArithmeticNonpositiveV1` is monotone
downward only (`windowArithmeticNonpositive_mono_v1`); no theorem here extends a window upward.

## Sources

`manifest.json` lists all 317 modules in import order. Each entry is one file pinned by SHA-256:

| where | modules |
|---|---|
| `research/rh/consolidated_v1/src/` | 165: `RHConsolidatedV1`, 31 modules of the V10–V13 explicit-formula and Krein chain that are not on `main`, and the 133 `L = 21/20` batch modules (machine-generated `decide +kernel` certificates) |
| already on `main` (`AegisRH/`, `AEGISOverlay/`, `research/rh/krein_*`, `FormalConjectures/Millennium/RHSnowflakeLog23.lean`) | 102, referenced in place, not copied |
| `research/rh/critical_line_v1/` | 23 (nine zeros; 5 already on `main`) |
| `.li/` (checked out by CI) | 27: [nicholasbulka/li-criterion-rh-equivalence-lean](https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean) at `35df682` (Apache-2.0), with `li-provider.patch`: three one-line Mathlib API updates in `Hadamard/General/Factorization.lean` |

Nothing is fetched from another branch or from the AEGIS repository.

Six files of `src/` are committed as plain text (`RHConsolidatedV1`, `RHEulerGammaV13`,
`RHDyadicDiagonalV13`, `RHKreinPairingV13`, `RHKreinDeltaPairingV1`, `RHKreinCertificateV1`). The
other 177 new files (26 chain modules, the 133 batch modules and 18 `critical_line_v1` modules,
about 950 KB) are committed as one xz archive in ten base64 parts, `sources.b64.0`–`.9`
(93 KB compressed). Unpack them with
`cat research/rh/consolidated_v1/sources.b64.* | base64 -d | xz -d | tar -x` from the repository
root; `build.py` refuses to run unless every file matches its SHA-256 in `manifest.json`.

## Build

From the repository root, with the pinned toolchain and Mathlib (`lake exe cache get`) and the
provider checked out and patched at `.li`:

```
cat research/rh/consolidated_v1/sources.b64.* | base64 -d | xz -d | tar -x
lake env python3 research/rh/consolidated_v1/build.py OUT_DIR consolidated.log 3
```

`build.py` checks every SHA-256, compiles the modules in import order (independent ones in
parallel), fails on any error or `sorry`, and checks that every `#print axioms` report is within
the standard three and that the four headline theorems are reported.
`.github/workflows/rh-consolidated-v1.yml` runs exactly this. The batch modules dominate the cost
(about 9 CPU-hours).

AUTHORITY_EFFECT = NONE.
