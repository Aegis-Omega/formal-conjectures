# The per-packet fine mixed budget does not depend on its constant

## What is new

This checkpoint adds one module, `WeilFineBudgetEquivV1.lean`. It imports:

* `AEGISOverlay.RHActualUniversalFineGramV1`, the operator's module, unmodified;
* `RestrictedWeilCriterionKernelBridgeV10`, from the PR92 packet;
* `WeilFineDiagonalQuadV1`, from checkpoint `20261122_fine_diagonal_quad_v1`.

### Definitions

* `FineBudget c`: every moment-zero packet `g` has **some** decomposition into moment-zero atoms of log-width
  1/128 with `actualMixedDefect ≤ c · Σ E`. This is the hypothesis of
  `riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet` (checkpoint `20261123_fine_chain_43_v1`) with
  constant `c`.
* `StrictWeilSign`: `Re W(g ⋆ g) < 0` for every moment-zero packet with `g ≠ 0`.

### Theorems

| theorem | statement |
|---|---|
| `strictWeilSign_of_fineBudget` | `c ≤ 43/10 → FineBudget c → StrictWeilSign` |
| `fineBudget_of_strictWeilSign` | `StrictWeilSign → FineBudget c`, for **every** real `c` |
| `fineBudget_iff_strictWeilSign` | `c ≤ 43/10 → (FineBudget c ↔ StrictWeilSign)` |
| `fineBudget_5671_iff_43` | `FineBudget (5671/3200) ↔ FineBudget (43/10)` |
| `operator_per_packet_hcert_of_strictWeilSign` | `StrictWeilSign` implies the hypothesis `hcert` of the operator's `riemannHypothesis_of_one_actual_mixed_budget_per_packet` |
| `riemannHypothesis_of_strictWeilSign` | `StrictWeilSign → RiemannHypothesis` |

### How the two directions are proved

* **From the budget to the strict sign.**
  * Every width-1/128 moment-zero atom has diagonal constant strictly above `43/10` (`fine_constant_gt`).
  * `Σ E > 0` whenever `g ≠ 0` (`energy_pos_of_ne`).
  * Hence `Re W ≤ (c − C) Σ E < 0`.
* **From the strict sign to the budget.** Take the operator's constructed decomposition of `g ≠ 0` and replace
  every atom by `K` copies scaled by `1/K` (`copyPacket`).
  * The packet and the Gram total are unchanged (`copy_packetSum`).
  * The diagonal and the energies shrink by `1/K` (`copy_defect`, `copy_energy`).
  * Since `Re W(g ⋆ g) < 0`, a large `K` meets any budget constant.
  * The zero packet takes the one-atom decomposition.

## What this means

* For the per-packet existential form with width-1/128 atoms, the constant carries no quantitative information.
  The condition is exactly the strict Weil sign, for `5671/3200`, for `43/10`, and for every constant in between.
* Improving the diagonal therefore does **not** bring this consumer closer. It does help the row/Schur
  consumers of `20261123_fine_chain_43_v1`, where the decomposition and the cross bounds are fixed.

## What this does not do

* **`StrictWeilSign` is not proved.**
* **RH → `StrictWeilSign` is not formalized.** Checkpoint `20261123_strict_sign_nondeg_v1` reduces it to
  `MellinZeroNonvanishing`.
* **What a proof would need (correction, 2026-11-23).** An earlier version of this README claimed that
  `N(T) ~ (T/2π) log T` against the `O(T)` zeros of the Mellin transform settles this. That is not enough:
  * the strict sign only sees the zero **set**, since the summands are `m(ρ) |M g(ρ)|²`;
  * on the critical strip the Mellin transform of a packet of log-width `L` behaves like a Fourier transform of
    width `L`, so it can have about `L·T/π` zeros up to height `T`, linear with an arbitrary constant;
  * so one needs the number of **distinct** zeros up to height `T` to grow faster than linearly;
  * `N(T)` together with the multiplicity bound `O(log T)` gives only a linear lower bound;
  * superlinear distinct-zero counts are known only through deeper results: Selberg's `≫ T log T` sign changes
    on the critical line, or, under RH, Littlewood's multiplicity bound `O(log T / log log T)`.

  None of this is formalized in this chain or in Mathlib.
* Not RH.

## Build

* **Base.** Lean 4.33.1 + Mathlib, against the `--trust=0` replay of the PR92 eleven-kernel packet (186 of 186
  modules). The dependencies are the same as for `20261123_fine_chain_43_v1`.
* **Trust levels.** Built at default trust and again with `--trust=0`.
* **Result.** Exit 0, no errors, no warnings, no `sorry`. Every `#print axioms` lists only
  `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the source:

    6a82adc31f443dc675cfbe81d1569ee4aca83c6861c898d70ce6969e63451f7a  WeilFineBudgetEquivV1.lean
