# Distance-dependent log-free row charge on a 1/192 lattice

## What is new

There are two modules:

* `RHLogFreeRowDecayV1.lean` imports `WeilSeparatedArchL1BridgeV32`, from checkpoint `20261121_arch_l1_v32`.
* `RHLatticeFinePartitionV1.lean` imports Mathlib and the module above.

### The problem

In `AEGISOverlay/RHPrimeFreeRecompositionJoinV1.lean`:

* `combinedFineCost` charges every log-free pair of width-1/128 atoms the same constant, `676/65536`.
* `eighty_five_log_free_links_exceed_fixed_row_budget` records that 85 such links already exceed the row budget
  `57430/65536`.

The partition in `RHFiniteFinePartitionV1.exists_finite_smooth_local_partition` takes its centres from an arbitrary
finite subcover. Nothing therefore bounds how many log-free links one row carries.

### What these modules do

They change two things: the partition and the charge.

**The partition.** `exists_finite_smooth_lattice_partition` gives, for every real `L`, a finite smooth partition of
unity on `[−L, L]`:

* the centres are the lattice points `c_i = −L + i/192`;
* each cutoff `χ_i` has `tsupport χ_i ⊆ [c_i − 1/256, c_i + 1/256]`, which is the support radius of
  `WidthOneOneTwentyEightAt`.

`riemannHypothesis_of_canonical_resonance_producer` lets the caller choose one decomposition for each packet, so a
lattice decomposition is an admissible choice.

**The charge.** On a log-free pair the prime sum vanishes, so the Weil entry is the Archimedean term alone. By
`WeilSeparatedArchL1BridgeV32.distinct_arch_norm_bound_gap_l1` with `w = 1/128`, a pair at centre distance `d` costs
at most `R(d − 1/128)/256` per unit of `E(p) + E(q)`, where

    R(δ) = e^{−5δ/2} / (1 − e^{−2δ}).

This charge decays geometrically in `d`.

### Theorems in `RHLogFreeRowDecayV1`

| theorem | statement |
|---|---|
| `archRemainder_le_geom` | `R(m/192 − 1/128) ≤ C · q^{m−53}` for `m ≥ 53`, with `q = e^{−5/384}` |
| `offsets_row_charge_le` | for every finite set `D ⊂ ℤ` with `\|d\| ≥ 53` on `D`: `Σ_{d∈D} R(\|d\|/192 − 1/128)/256 ≤ 4/5` |
| `four_fifths_lt_row_budget` | `4/5 < 57430/65536` |

### Theorems in `RHLatticeFinePartitionV1`

| theorem | statement |
|---|---|
| `exists_finite_smooth_lattice_partition` | the lattice partition described above |
| `lattice_row_charge_le` | for every row `i` and every set `S` of columns with `\|c_j − c_i\| ≥ 35/128` (the left end of `FineLogFreeGap`), `Σ_{j∈S} R(\|c_j − c_i\| − 1/128)/256 ≤ 4/5` |

## Numbers

These are floating-point checks (class (d)) on the same lattice:

| quantity | value |
|---|---|
| log-free links per row (`FineLogFreeGap`, both sides) | 308 |
| uniform charge `308 · 676/65536` | 3.177, over the budget 0.876 |
| distance-dependent charge, log-free set only | 0.4385 |
| distance-dependent charge, all `\|d\| ≥ 53` (the set Lean bounds by `4/5`) | 0.4870 |

## Not done here

* **Not wired into the operator's chain.** `combinedFineCost` and the producer hypothesis of
  `riemannHypothesis_of_canonical_resonance_producer` still use the uniform log-free cost. Using the bound above
  requires the producer to accept a distance-dependent cost. I did not modify those modules.
* **Log-free entries only.** The resonant pairs, where a prime power falls in the support difference, remain the
  open obligation.
* **The remaining budget is tight.** The row budget left for resonant pairs is `57430/65536 − 4/5 ≈ 0.076` in
  Lean, or about `0.39` with the numerical value `0.487`.
* Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and V32.
* Both modules were built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built sources:

    5fcd0552b3944ac2e14e925ce2722bd610b638d90163a0436396ad395aace236  RHLogFreeRowDecayV1.lean
    549995804357a8f3e126847df1e27f0b54ef76c5cb0bff556d32adf62fed382f  RHLatticeFinePartitionV1.lean
