# Rank-two pivots of the 9/5 moment-zero basis, in Lean, and a Coq check of the existing Coq theories

## Lean (`CvSPivotRankTwoV1.lean`)

- `pivot_moment_zero`: both moments of every basis vector `e_m + U₀(m) e₀ + U₁(m) e₁` of the 9/5
  Feshbach blocks vanish, with the real rational pivots
  - `U₀(m) = ((m − 1)/4)/(1/4 + ω²m²)`
  - `U₁(m) = −m(1/4 + ω²)/(1/4 + ω²m²)`
  - `ω = 2π/L`, `s = ±1/2`; the common factor `e^{sL} − 1` is dropped.
  - `pivot_cleared` is the same statement with the denominators cleared, proved by `linear_combination`
    with `i² = −1`.
- `one_le_det`: `det(1 + UUᵀ) ≥ 1` for every real `2 × ι` matrix (Cauchy–Schwarz).
- `woodbury`: `(1 + UᵀU)⁻¹ = 1 − Uᵀ(1 + UUᵀ)⁻¹U`.
- Together, the Gram block `G11 = 1 + UᵀU` of the basis is inverted through a 2 × 2 matrix whose
  determinant is at least 1. This is the Lean counterpart of `../20261116_moment_killer_inverse_v1/`
  (closed forms and the Arb benchmark).

The module was built on Lean 4.33.1 with Mathlib, at default trust and with `--trust=0`. Both runs exit 0
with no errors or warnings. All three theorems have axioms `[propext, Classical.choice, Quot.sound]`.
sha256: `bb35ac171f4ea6e75579022794e27a43f690280aa9616093bad7b4e4f827c586`.

## Coq: an independent compile of `research/rh/aegis_source_4d7578e/coq/`

Setup: Coq 8.18.0 with the Ubuntu 24.04 packages `libcoq-corn` and `libcoq-coquelicot`. Each `.v` file
was compiled in dependency order (`coqc -R <dir> <name>`), from a copy outside the checkout.
- 21 of 22 files compile. Among them are the Weil files `FiniteBridge`, `FiniteEntryDictionary`,
  `Globalization`, `WeilCriterion`, `O0` and `AnalyticDefinitions`, and the `O0*Probe` files.
- `ConcreteFiniteGuinandWeilSemanticsV1` does not compile: it requires `VonMangoldtCanonicalBridge`, which
  is not in the snapshot.
- `Print Assumptions` gives "Closed under the global context" for the following theorems: no axioms.
  - `prime_offdiag_matches_divided_difference`, `pole_closed_template_factorizes` and
    `prime_pole_offdiag_dictionary` (`FiniteEntryDictionary`);
  - `finite_lower_bound_v1_specialize`, `o0_plus_minus_cancel_v1`, `o0_rational_half_balance_v1` and
    `globalization_ready_implies_global_weil_positivity_v1` (`Globalization`).
- The last of these is an implication: global positivity follows from the hypothesis
  `GlobalizationReadyV1`, that is, convergence, `ε → 0` and lower bounds for the actual form. Proving
  that hypothesis is the open part.
- The Coq module `HolonCvSPivotRankTwoV1.v` (HOLON V5) was not available here and is not checked. Its
  algebra is the content of the Lean module above.

Not RH.
