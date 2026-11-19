# HOLON V6 → V7: Arb check of the rank-two projection, and a V7 candidate for the Feshbach blocks

Reply to the V6 task of PR #92 (comment 6907501295), tag `AEGIS-HOLON-V6-CLAUDE-REPLY`. Branch head at test time:
`b0ec94321a429a9e86606b763275570979148dc3`.

## Inputs tested

| file | identity |
|---|---|
| original `research/feshbach_arb_v2/feshbach_blocks_arb.py` (snapshot `aegis_source_0c1477f`) | git blob `22e6048ed1c74b500b6c8ad23a3f9a4a72d71d77` |
| `cvs_entries.py`, `schur_arb.py` (same snapshot) | blobs `d34e81c7…`, `60f44fee…` |
| V3 candidate (from the V6 zip) | sha256 `721f1ce0066a6ff873514a58a841d2d0d33651d1bd68a6f40387b3d280cf4c16` |
| V6 candidate | sha256 `ac0b4be3ece76fae67924a0293123ab1acff1d90ff0d840af08886055c0ab283` |
| `AEGIS_HOLON_CROSS_LOOP_V6_20261116.zip` | sha256 `4d5e3a0b98ec59b1ef8dbb06803be94c8c14066bf90b3236813bb965545413a8` |

Inside the zip: `VERIFY_BUNDLE.py` gives PASS on 18/18 files. `patch_source.py` reproduces the V6 sha256.
`verify_rank2_v6.py` was rerun with SymPy 1.14: the exact cases k = 3, 5, 7, 11 match `V6_RECEIPT.json`.

## Verdict on V6: PASS, no error found

- **Algebra.** `Zᴴ X Z = X_FF + X_FP U + Uᴴ X_PF + Uᴴ X_PP U` holds for every square `X`, not only Hermitian ones.
  It is a pointwise identity, so evaluating it in interval arithmetic encloses the same true matrix.
- **Arb, entry by entry.** Runs used python-flint 0.9.0 and 0.8.0 at the scripts' 192 bits. Every entry of
  `A11`, `G11` and `C_B` was compared as a ball against the original. The same check was run for V3, V6 and V7.

  | case | original | V3 | V6 | V7 | non-overlapping entries |
  |---|---|---|---|---|---|
  | L = 1.8, N = 40, NP = 400, order-8 tail, uniform (flint 0.8.0) | 4.1 s | 2.1 s | 2.0 s | 0.7 s | 0 / 3·79² |
  | L = 1.2, N = 100, NP = 3000, order-1 tail, uniform (0.9.0) | 25.9 s | 20.7 s | 21.7 s | 7.0 s | 0 / 3·199² |

  `tail_weights` (1/5 ×5), and the balls `K2`, `Amax` and `Eco`, agree in all four versions. At L = 1.2 and
  NP = 3000 the Schur step fails identically in all four: pivot 101,
  `−0.0518028517303494121479810430980832550…` to the last common digit. The C_B radius is
  6.5e-52 (original), 5.1e-53 (V3/V6) and 7.6e-55 (V7).
- **Kernel.** `CvSPivotCongruenceV1.congruence` (Lean 4.33.1 + Mathlib, below) proves the four-block identity
  for any `X` over a commutative star ring. Its axioms are `[propext, Classical.choice, Quot.sound]`.

### What the V6 numbers do and do not show

- The "≈20×" is the congruence step alone, measured in NumPy. In Arb at k = 199 that step takes 0.21 s (V3) and
  0.06 s (V6), out of about 21 s in total. At k = 399 (L = 1.8, N = 200, NP = 1000, order 8) V6 runs in 27.4 s.
  Of that, the projection is 0.29 s, the Woodbury correction 0.75 s, and the row evaluation 15.7 s.
- The dominant cost is not `RᵀR`. It is evaluating the row entries: each entry computes `2·#{q}` sines, and
  `seqs(|n|)` is recomputed for `±n`. At k = 399 the rows take 15.7 s and `RᵀR` 3.0 s.
- At k = 799 (N = 400) V6 still forms dense `acb` k × k products and 2K + 2 dense outer products. Under a 1.3 GB
  address-space cap it stops with `MemoryError` (GMP) after the tail terms. The production run needs far more
  memory than the blocks it outputs.

## V7 candidate (`feshbach_blocks_arb_candidate_v7.py`)

It has the same row model, the same tail bound and the same JSON. Each change evaluates the same function of the
true inputs, so every enclosure stays valid.

1. **Rows.** For `n ≠ m`, `pole − wr − wp = pole + (α_m − α_n)/(π(n − m))`, with
   `α_n = −(sS(n) + Σ_q w_q sin(2πn y_q/L))`. This is the `alpha` the tail bound already uses. Sines are
   evaluated once per index, and `seqs` once per `|n|`.
2. **V⊥ is spanned by the pole vectors.** Let `M = [avec, bvec]`, where `a_j = 1/(j²+β²)` and
   `b_j = j/(j²+β²)`. Then `Mᵀ Z = 0` (Lean: `perp_a`, `perp_b`) and
   `P_V = I − M(MᵀM)⁻¹Mᵀ` (Lean: `projector_split`). Since `RR = QbᵀQb + RoutᵀRout`,

       C_B = Zᵀ(RR + Tail + Ib)Z − A11 G11⁻¹ A11 = Zᵀ(RoutᵀRout + Tail + Ib)Z + Wᵀ(MᵀM)⁻¹W,   W = MᵀQbZ

   (Lean: `cb_eq`). The new form has no k × k inverse, no `A11·A11`, and no difference of two large blocks.
3. `A11`, `Zᵀ X Z` (the V6 congruence) and `G11 = I + UᵀU` are all formed with two pivot rows.
4. `RoutᵀRout` is summed over blocks of 2000 rows. `Tail` is formed as one product `T diag(c/p) Tᵀ`, without
   storing 2K + 2 dense outer products. All matrices are real `arb_mat`.

Results (python-flint 0.9.0; one thread; blocks capped at 1.3 GB, `schur_arb.py` at 1.9 GB):

| run | result |
|---|---|
| L = 1.2 certificate (N = 100, NP = 10000) | blocks in 23 s. `schur_arb.py` at the receipt's `c_∞ = 1.92058314848`: μ = 5e-5 **POSITIVE DEFINITE** (min pivot 0.0062166914822…), μ = 6e-5 FAILED. Same outcome as `L1.2/RECEIPT.json`. The original script stops with `MemoryError` in `RᵀR` under the same 1.3 GB cap. |
| L = 1.8 production (N = 400, NP = 16000, order-8 tail, mixed weights) | blocks in 222 s. At `c_∞ = 0.97991957971`: μ = 4e-17 **POSITIVE DEFINITE** (min pivot 6.3242311e-8; receipt 6.3212145e-8), μ = 4.2e-17 FAILED. Same outcome as `L1.8/RECEIPT.json`. |
| k = 799, NP = 1000 | 20 s (V6: `MemoryError`) |

Lean (`CvSPivotCongruenceV1.lean`, imports `../20261116_pivot_rank_two_v1/CvSPivotRankTwoV1`): Lean 4.33.1 with this
repository's Mathlib, default trust, exit 0, no errors, no warnings, no `sorry`. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for `congruence`, `gram_det_pos`, `perp_a`, `perp_b` and `cb_eq`.
`cb_eq` uses `projector_split`. `gram_eq` is proved by rewriting.

## Findings beyond V6

1. **The float64 diagnostics are wrong at this scale.**
   - `scipy.linalg.eigh` on `mid(A11), mid(G11)` gives λ₁ = 4.75e-16 in the L = 1.8 `blocks.log` (6.18e-16 in V7).
   - The Ritz value at working precision is 4.53361503180e-17 ± 4e-29. V7 computes it with `RITZ=1`, by inverse
     iteration; the receipt's `bottom_ritz.log` has 4.533615032e-17.
   - The "mixed" tail weights are derived from that float64 vector. They differ between the original and V7
     (0.3385/0.2098 vs 0.3194/0.2292 for the first two). Both are valid, since any fixed p is. But the L = 1.8
     receipt cannot be reproduced bit for bit except on the same float64/BLAS path. With `uniform`, the weights are
     identical.
2. **Breakdown of `C_B(u₁)` at L = 1.8** (u₁ the Ritz vector, divided by `u₁ᵀG11u₁`):
   - `Rout` (rows N < |n| ≤ 16000) 2.144e-18, **70%**;
   - `Tail` (bound for |n| > 16000) 9.31e-19, 30%;
   - `Eco·G11` 3e-26;
   - in-band rank-two part 2e-33;
   - total 3.075e-18.

   Since `S ⪰ 0` requires `u₁ᵀ S u₁ ≥ 0` and every other part is ≥ 0, this Schur certificate (N = 400,
   `c_∞ = 0.97992`) cannot pass any `μ > λ₁ − Rout(u₁)/(c_∞ − μ) ≈ 4.3148e-17`. That holds for any tail weights
   and any NP, because a valid bound for the rows |n| > NP covers at least the true rows NP < |n| ≤ 16000 that
   `Rout` counts here. Tail work can move μ from 4e-17 to at most about 4.31e-17. Anything further needs a larger N
   or a larger `c_∞`. At L = 1.2 the picture is the reverse: `Eco·G11` is 86% of `C_B(u₁)`, so the tail bound
   limits μ there.
3. **Weights tuned to u₁ alone break the certificate.** With `RITZ=weights` (mixed weights built from the exact
   u₁), `Tail(u₁)` falls 56%, to 4.08e-19, and `C_B(u₁)` to 2.552e-18. But `schur_arb.py` then fails at every
   μ ∈ {1e-17, 3e-17, 4e-17, 4.1e-17, 4.2e-17, 4.3e-17}, always at pivot 407 with about −0.0054. The weight of
   the order-0 α term drops to 0.026, so its coefficient grows 38× in directions other than u₁. The original
   weights pass at 4e-17.

## Next experiment

Choose the tail weights p for the Schur matrix, not for a single vector:
1. Compute the bottom r ≈ 10–20 Ritz pairs of (A11, G11) at working precision.
2. Maximise the smallest eigenvalue of the projected
   `A11 − μG11 − Σ_i (c_i/p_i)(ZᵀT_iZ)/(c_∞ − μ) − (rest)` over p (a small convex problem in 1/p).
3. Fix p as rationals and certify with the unchanged `schur_arb.py`.

The ceiling above bounds the possible gain at N = 400 (≤ 4.31e-17). The same run at N = 500 measures how fast
`Rout(u₁)` falls with the band, which is the quantity that limits L = 1.8.

## Reproduce

From this directory, with `cvs_entries.py` and `schur_arb.py` from `aegis_source_0c1477f/research/feshbach_arb_v2/`
in the run directory:

    TAIL_ORDER=8 TAIL_WEIGHTS=mixed RITZ=1 python3 -I feshbach_blocks_arb_candidate_v7.py 1.8 400 16000
    python3 -I schur_arb.py blocks_N400_NP16000.json 0.97991957971 4e-17 4.2e-17
    python3 -I compare_blocks.py <original blocks json> <candidate blocks json>   # ball overlap
    python3 time_blocks.py feshbach_blocks_arb.py timed.py                     # prints only; stage times

`RECEIPT.json` lists every run, its arguments and its outputs. Evidence kind: interval arithmetic (Arb) for the
blocks and the Schur step; `lean_kernel` (local) for the five identities. The block-matrix inequalities themselves
remain `INTERVAL_CERTIFIED_NOT_LEAN`. Not RH.
