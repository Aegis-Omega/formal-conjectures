# `MellinZeroNonvanishing` from a count of the distinct zeros of ζ

## What is new

This checkpoint adds one module, `WeilMellinZeroDensityV1.lean`. It imports:

* `WeilStrictSignMellinV1`, from checkpoint `20261123_strict_sign_nondeg_v1`;
* `WeilMellinInversionV1` and `Hadamard.OrderOne.ZeroCountingBounds`, from the PR92 packet.

### Definition

`DistinctZeroSuperlinear`: for every real `C` there is a radius `R ≥ 1` and a finite set of more than `C · R`
distinct nontrivial zeros of `ζ`, each of modulus at most `R`. The statement involves only `ζ`.

### Theorems

| theorem | statement |
|---|---|
| `support_bounds` | a packet vanishes outside some `[A, B]` with `0 < A` |
| `mellin_differentiable` | the Mellin transform of a packet is entire |
| `norm_mellin_le` | `‖M g(s)‖ ≤ exp(c (‖s‖ + 1)) · ∫ ‖g‖` with `c` from `A` and `B`: exponential type |
| `exists_mellin_ne_zero` | `g ≠ 0 → ∃ s, M g(s) ≠ 0` (Mellin inversion) |
| `mellinZeroNonvanishing_of_distinctZeroSuperlinear` | `DistinctZeroSuperlinear → MellinZeroNonvanishing` |
| `strictWeilSign_of_rh_distinct` | `RH → DistinctZeroSuperlinear → StrictWeilSign` |
| `fineBudget_of_rh_distinct` | `c ≤ 43/10 → RH → DistinctZeroSuperlinear → FineBudget c` |

### How the reduction is proved

* Fix a nonzero moment-zero packet `g` and suppose `M g` vanishes at every nontrivial zero.
* Choose `s₀` with `M g(s₀) ≠ 0` and set `f(z) = M g(z + s₀)`.
* Jensen's formula (`Hadamard.ZeroCounting.card_zeros_le_of_max_one_maxModulus`) together with the
  exponential-type bound gives at most `α R + β` distinct zeros of `f` in `‖u‖ ≤ R/2`, for constants `α, β` that
  depend only on `g`.
* The map `ρ ↦ ρ − s₀` sends distinct zeros of `ζ` with `‖ρ‖ ≤ R'` injectively into these zeros, with
  `R = 2(R' + ‖s₀‖)`.
* `DistinctZeroSuperlinear` with `C = 2α + |2α‖s₀‖ + β|` gives more of them than that bound allows.

## What this means

For every `c ≤ 43/10`, combined with checkpoints `20261123_fine_budget_equiv_v1` and
`20261123_strict_sign_nondeg_v1`:

    RH ∧ DistinctZeroSuperlinear  →  StrictWeilSign  ↔  FineBudget c

The extra condition next to RH is now a statement about the zeros of ζ alone. It no longer involves packets,
Mellin transforms or the Weil form.

## What this does not do

* **`DistinctZeroSuperlinear` is not proved.**
* It is a known theorem, but a deep one, and nothing here formalizes it:
  * unconditionally, Selberg (1942) gives `≫ T log T` sign changes of Hardy's `Z`-function on `[0, T]`; each
    sign change is a distinct zero on the critical line;
  * under RH, Littlewood's multiplicity bound `O(log T / log log T)` together with `N(T) ~ (T/2π) log T` also
    gives it.
* A search of the 199 modules of `research/rh/aegis_rh_weil/` finds only upper bounds on numbers of zeros (Jensen),
  no lower bound.
* Not RH.

## Build

* **Base.** Lean 4.33.1 + Mathlib `0df444a3`, against the compiled oleans of the 199 modules of
  `research/rh/aegis_rh_weil/`.
* **Trust levels.** Built at default trust and again with `--trust=0`.
* **Result.** Exit 0, no errors, no warnings, no `sorry`. Every `#print axioms` lists only
  `[propext, Classical.choice, Quot.sound]`.
* **Lake project.** The module is also added to `research/rh/aegis_rh_weil/` as library
  `WeilMellinZeroDensity`.

SHA-256 of the source:

    52f37a55a309ed7b4b80fbe4925a1171a1709f0d062e24929f247565447d74fb  WeilMellinZeroDensityV1.lean
