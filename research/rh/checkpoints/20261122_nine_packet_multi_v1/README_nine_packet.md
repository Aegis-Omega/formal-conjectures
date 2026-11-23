# Nine independent packets on the dyadic lattice at width 1/32

## What is new

There is one module, `WeilNineBlockMultiV1.lean`. It imports `WeilNineBlockCombV1` (`20261122_nine_block_comb_v1`).

The comb modules treat `F = Σ_j z_j · T_{j log 2} g` for **one** packet `g`. This module lets the nine blocks
carry **nine independent packets**:

    f_j = T_{j log 2} g_j,   j = 0, …, 8.

Each `g_j` has log-support in `[a − 1/64, a + 1/64]`, with one common `a`, and satisfies both moment conditions.
The comb is the special case `g_j = z_j · g`. This is a first step on edge E3 of PR #835 (from combs to general
packets). The blocks are still pinned to the dyadic lattice.

### What changes for two different packets `p, q`

* **`logCross_translate2`.** `logCross(T_{d₁} p, T_{d₂} q)(u) = logCross(p, q)(u + d₂ − d₁)`.
* **`logCross_zero2`.** `logCross(p, q)` vanishes for `|u| > 1/32`. So the prime windows are the same as for the
  comb: only `2^k` for `k ≤ 6`, and the resonances at `k = 7, 8`.
* **`cross_norm_le2`.** The centre value is no longer the energy. Every prime term is bounded through the weighted
  Cauchy–Schwarz inequality

      ‖logCross(p, q)(s)‖  ≤  ((β/α) E(p) + (α/β) E(q)) / 2,     α, β > 0.

  The proof is pointwise, from `(βx − αy)² ≥ 0`, followed by integration.
* **`arch2`.** The Archimedean cross term is at most `(E(p) + E(q))/400`. This uses V32
  (`logCross_l1_le_distinct`, `separated_arch_norm_bound_l1`).
* **`cross2`.** For `i < j ≤ i + 8`:

      ‖B(T_i p, T_j q)‖ ≤ (cbar9(j−i) − 1/200) · ((β/α) E(p) + (α/β) E(q))/2 + (E(p) + E(q))/400.

* **`diag2`.** `Re B(T_d p, T_d p) ≤ −(299/100) E(p)`, from `width_diagonal_299_over_100`.

### The Schur test

The weights `α, β` are the Schur weights
`wv = (1, 827/1000, 571/1000, 583/1000, 587/1000, 583/1000, 571/1000, 827/1000, 1)`.

* After summing, the coefficient of `E(g_i)` is
  `−299/100 + Σ_{j≠i} (cbar9 − 1/200) · wv_j/wv_i + 8/200`.
* Its largest value over `i` is `−2.99 + 2.96911`, which is below `−1/50`.
* `nine_packet_gram_bound`:

      Re Σ_{i,j} B(f_i, f_j)  ≤  −(1/50) · Σ_j E(g_j).

## Numbers

These are floating-point checks (class (d)).

| quantity | value |
|---|---|
| spectral radius of the prime ceilings `cbar9 − 1/200`, nine blocks | 2.9277 |
| plus the Archimedean row charge `8/200` | 2.9677 |
| largest weighted row coefficient with `wv` (exact rational check) | 2.96911 |
| diagonal used | 2.99 |

## Not done here

* **Free positions.** The blocks are fixed at `j log 2` with a common base `a`. Packets at arbitrary separations
  need the log-free row charge of `20261121_logfree_row_v1` in place of the dyadic windows.
* **Gaps `k ≥ 9`** (edge E2): phase-preserving bounds.
* **The sharp moment-zero diagonal.** The proved value is `2.99`, against about `3.65`.
* No window statement. Not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans and the earlier
  checkpoints.
* The module was built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors, no warnings and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.
* `nine_packet_gram_bound` uses `set_option maxHeartbeats 1600000` for the 81-term expansion.

SHA-256 of the built source:

    0c3c29f068ac1a5445800a82ede710fc5374e9da3fe5142e302be965ff18849a  WeilNineBlockMultiV1.lean
