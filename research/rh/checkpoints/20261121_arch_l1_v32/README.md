# L¹ correlation bound for the Archimedean mixed term (V3.2)

## What is new

Two modules:
- `WeilLogCorrelationL1V1.lean`: abstract real analysis, imports only Mathlib.
- `WeilSeparatedArchL1BridgeV32.lean`: imports `WeilSeparatedArchBridgeV31` and the module above.

Up to now every Archimedean mixed-term bound in the chain (`WeilSeparatedArchBridgeV31`, and
`separated_arch_decay_bound` / `separated_arch_decay_any_positive_gap` in
`AEGISOverlay/RHActualMixedDefectV1.lean`) uses the pointwise bound `‖C(u)‖ ≤ E`, multiplied by the length
of the support-difference interval. That interval is twice the packet width. Bounding the L¹ norm of the
correlation directly removes this factor 2.

### Lemmas in `WeilLogCorrelationL1V1`

- `l1_autocorr_le`: for `h` supported on `[c, c + w]`,
  `∫ u, ‖∫ v, h (v + u) conj (h v)‖ ≤ w · ∫ ‖h‖²`.
- `l1_crosscorr_le`: for `h`, `k` supported on intervals of length `w`,
  `∫ u, ‖∫ v, h (v + u) conj (k v)‖ ≤ (w/2)(∫ ‖h‖² + ∫ ‖k‖²)`.
- Proof:
  1. Fubini through `integral_convolution` gives `∫∫ |h(v+u)| |k(v)| = (∫ |h|)(∫ |k|)`.
  2. Cauchy–Schwarz on the support, taken from the discriminant of `t ↦ ∫_I (|h| − t)²`, gives
     `(∫ |h|)² ≤ w ∫ |h|²`.

### Theorems in `WeilSeparatedArchL1BridgeV32`

The bridge combines these lemmas with the existing kernel estimates.

Generic theorem:
- `separated_arch_norm_le_of_kernel` takes the kernel bound `|K(u) − c·e^{−u/2}| ≤ κ` beyond the gap and
  gives `‖Arch(mixed p q)‖ ≤ κ · ∫ ‖logCross p q‖`. It uses V31's moment cancellation unchanged.

The three retained translates (V22/V31 setting, width 1/32):
- `three_arch_bounds_l1` gives `≤ E/200` for all three mixed terms. V31 gives `E/100`.

Dyadic decay of translates at shift `D = d₂ − d₁ ≥ log 2`:
- `translated_arch_norm_bound_dyadic`: `‖Arch‖ ≤ (30/649) · exp(−5D/2) · E`.
- `dyadic_arch_decay` states the same at `D = k log 2`: `‖Arch‖ ≤ (30/649) · 2^{−5k/2} · E`.
- The constant is exact, not rounded. It is `(64/59)/(11/15)/32`, from `exp x < 1/(1−x)` at `x = 5/64` and
  `exp(1/16) < 16/15`.
- This is the operator's stated AEGIS bound `(30/649)·2^{−5k/2}·E`, now proved in Lean.
- Numerically, the best possible constant is `max_k R(k log 2 − 1/32)/32/2^{−5k/2} = 0.046042…`, reached at
  `k = 1`.

Two different packets of log-width `w` at support gap `δ > 0`:
- `distinct_arch_norm_bound_gap_l1`: `‖Arch(mixed p q)‖ ≤ R(δ) · (w/2) · (E(p) + E(q))`, where
  `R(δ) = e^{−5δ/2}/(1 − e^{−2δ})`. The moment conditions are needed on `p` only.
- For width-1/128 packets this is `(1/256)·R(δ)·(E(p)+E(q))`. The pointwise route in
  `distinct_fine_arch_decay_any_positive_gap` gives `(1/128)·R(δ)·(E(p)+E(q))`.

## Not done here

- **Downstream constants are not re-derived.** These still consume the old Archimedean bounds:
  - the V30 cross/three-block assembly (`51/100`, `9/25`, `−1/10`), which takes `1/100`;
  - the `RHActualMixedDefectV1` budgets (`q16`, `13/384·(2/37)^k`, …).

  The new bounds are stronger statements under the same hypotheses, so plugging them in only adds slack.
- **Archimedean side only.** There is no prime-side estimate and no global Weil sign. RH is not proved.

## Build

- Built with Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans.
- Both modules built at default trust and again with `--trust=0`.
- Both runs exit 0 with no errors and no `sorry`.
- Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built sources:

    36719509b93448775ee0b87b65ef947f1fb2696171e7f4dbc1556ae4c7779565  WeilLogCorrelationL1V1.lean
    6099db235b013f12d087d57dda494cac96e4e12b17197e539a23a5e0b272962d  WeilSeparatedArchL1BridgeV32.lean
