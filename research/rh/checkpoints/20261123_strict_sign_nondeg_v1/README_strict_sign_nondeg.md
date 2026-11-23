# The strict Weil sign is RH plus nondegeneracy of the Weil form

## What is new

This checkpoint adds two modules. The first, `WeilStrictSignNondegV1.lean`, imports:

* `WeilFineBudgetEquivV1`, from checkpoint `20261123_fine_budget_equiv_v1`;
* `WeilRHImpliesFinalSignV13`, from the PR92 packet.

### Definition

`WeilNondegenerate`: if a moment-zero packet `g` has `Re B(g, h) = 0` for every moment-zero packet `h`, then
`g = 0`.

### Theorems

| theorem | statement |
|---|---|
| `re_B_add_scale` | `Re B(g + t h, g + t h) = Re B(g, g) + 2t Re B(g, h) + t² Re B(h, h)` for real `t` |
| `strictWeilSign_of_rh_nondeg` | `RH → WeilNondegenerate → StrictWeilSign` |
| `rh_and_nondeg_of_strictWeilSign` | `StrictWeilSign → RH ∧ WeilNondegenerate` |
| `strictWeilSign_iff_rh_and_nondeg` | `StrictWeilSign ↔ RH ∧ WeilNondegenerate` |
| `fineBudget_iff_rh_and_nondeg` | `c ≤ 43/10 → (FineBudget c ↔ RH ∧ WeilNondegenerate)` |

The key step is `strictWeilSign_of_rh_nondeg`. It runs as follows:

* Under RH, `−Re B` is positive semidefinite on moment-zero packets (`rh_implies_final_sign_residual_v13`).
* If `Re B(g, g) = 0`, then `2t Re B(g, h) + t² Re B(h, h) ≤ 0` for every real `t`.
* Taking `t = Re B(g, h) / (1 − Re B(h, h))` forces `Re B(g, h) = 0`.
* `WeilNondegenerate` then gives `g = 0`.

### Through the zeros: `WeilStrictSignMellinV1.lean`

A second module, `WeilStrictSignMellinV1.lean`, imports `WeilStrictSignNondegV1` and
`RestrictedWeilCriterionResidueCoefficientV11`.

* **Definition.** `MellinZeroNonvanishing`: the Mellin transform of every nonzero moment-zero packet is nonzero
  at some nontrivial zero of `ζ`.
* **Ingredients from the PR92 packet.**
  * Under RH, `−Re W(g ⋆ g) = Σ_ρ m(ρ) |M g(ρ)|²` (`autocorrelation_explicit_formula_v10`,
    `rh_zero_summand_eq_normSq_v13`).
  * Every multiplicity `m(ρ)` is positive (`zeta_analyticOrderNatAt_ne_zero_v11`).

| theorem | statement |
|---|---|
| `strictWeilSign_iff_rh_and_mellin` | `StrictWeilSign ↔ RH ∧ MellinZeroNonvanishing` |
| `nondeg_iff_mellin_of_rh` | `RH → (WeilNondegenerate ↔ MellinZeroNonvanishing)` |
| `fineBudget_iff_rh_and_mellin` | `c ≤ 43/10 → (FineBudget c ↔ RH ∧ MellinZeroNonvanishing)` |

## What this means

Combined with `20261123_fine_budget_equiv_v1`, for every constant `c ≤ 43/10` (the operator's `5671/3200`
included) the per-packet fine mixed budget is exactly RH together with either of two equivalent extra
conditions:

* nondegeneracy of the Weil form on moment-zero packets;
* under RH, equivalently, no nonzero moment-zero packet has a Mellin transform vanishing at every nontrivial
  zero.

### External context (not used in this checkpoint)

* On 2026-11-21 the Lean FRO and the Mathlib Initiative issued a joint statement certifying a Lean proof of
  Mathlib's `RiemannHypothesis`, released by Levent Alpöge on 2026-11-20.
* That library is **not** imported, built or replayed here. Every theorem in this checkpoint keeps RH as an
  explicit hypothesis.
* Combined with that external result, the theorems above would give, for `c ≤ 43/10`:

      FineBudget c  ↔  WeilNondegenerate  ↔  MellinZeroNonvanishing

  The remaining content of the Weil route would then be `MellinZeroNonvanishing`, whose statement does not
  involve RH.

## What this does not do

* **`WeilNondegenerate` and `MellinZeroNonvanishing` are not proved.**
* **Expected argument, not formalized.**
  * The Mellin transform of a compactly supported packet is entire of exponential type, so it has `O(T)`
    zeros up to height `T`.
  * The nontrivial zeros of `ζ` number `N(T) ~ (T/2π) log T`.
  * This needs zero counting for `ζ` and Jensen-type bounds, which are not in this chain.
* Not RH.

## Build

* **Base.** Lean 4.33.1 + Mathlib, against the `--trust=0` replay of the PR92 eleven-kernel packet (186 of 186
  modules), with the dependencies of `20261123_fine_budget_equiv_v1`.
* **Trust levels.** Built at default trust and again with `--trust=0`.
* **Result.** Exit 0, no errors, no warnings, no `sorry`. Every `#print axioms` lists only
  `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the sources:

    6749602f61a591904b26064f1982d35970a5b6c647812f459ae8bce5f2070a75  WeilStrictSignNondegV1.lean
    493d6e434bb64aabb1939808c101bcac0cffa574c11e441f73efb361273ff34d  WeilStrictSignMellinV1.lean
