# Fast kernel replay of `bigCheck` (checkpoint, 2026-10-20)

Status: the kernel replay of `bigCheck` compiles locally. Not RH.

## What is proved (standard axioms, no `sorry`)

- `FastKronV1.lean` — generic lemmas:
  - strict CPS forcing (`fL_eq`, …);
  - Horner packing (`packS_eq`, `packZ_eq`);
  - a strict dot product (`ldotS_eq`);
  - signed Kronecker extraction (`unpackZ_getD`) and digit-range extraction (`unpackR_getD`);
  - CPS transpose (`transC_eq`, `transP_getD`).
- `CvSProjectedEntryFastL12V1.lean` — a row-chunked check `chunkCheck a n : Bool`:
  - `rowOk_of_chunk : chunkCheck a n = true → ∀ p < n, RowOk (a + p)`.
  - `bigCheck_of_rows : (∀ i < 139, RowOk i) → bigCheck = true`.
  - The X columns come from `certR` (`xsF_getD`), and the packed X rows are `xpF_getD`.
  - `H = K X` packed (`hpF_getD`).
  - Each row's packed value is `Σ_j Em i j · B0^j` (`row_value_of`).
  - The collision-free `ivF` implies `ivOk` (`ivF_ivOk`).
  - `colOk`, `neI = Em` and `entryOk` hold for all `i ≤ j < 139`.
- `CvSProjectedEntryReplayL12V1.lean`:
  - `chunk0_true` … `chunk4_true` by `decide +kernel` (rows 0–27, 28–55, 56–83, 84–111, 112–138).
  - `bigCheck_true : bigCheck = true`.
  - `instance bigCheck_fact : Fact (bigCheck = true)`.
  - `projectedEntry_mem_certI {M} (hM : 3 ≤ M) : ∀ i j : Fin 139, (Im certI i j).Mem certQ (projectedEntry M i j)`. This holds unconditionally.
  - `projected_lower_L12`: the packed lower bound with its interval hypothesis discharged.

All three main theorems depend on `[propext, Classical.choice, Quot.sound]`.

## Local result

| Module | Result |
|---|---|
| Replay module (`-DwarningAsError=true`) | rc = 0, 327 s, peak RSS 7.3 GB |
| Each chunk | about 70 s |

`set_option Elab.async false` makes the chunks check one after another, so each kernel cache is
freed before the next chunk starts. A single undivided check peaked above 13 GB.

## What this does and does not give

This gives the interval hypothesis hIv for the projected 139×139 certificate at L = 6/5. It is
one input of the low-block bridge. The remaining inputs, the row budget (`hBrow`/`hbeta`) and
the composition with the checked low bridge, are separate. Not RH.

## Kernel finding

Lean's kernel caches every `whnf` result. The hash of a large `Nat` literal effectively depends only
on its low word. Packing with a power-of-two base produces many literals with identical low bits:
`acc · 2^k` always ends in zero words. These collide in the cache and turn the cache into a linear
list.

Measured, Nat multiply-add loop, 3200 steps:

| base | time |
|---|---|
| `2^64` | 36.6 s |
| `2^64 + 12345` | 0.64 s |

On the 64-column packing it was 51 s with the power-of-two base and 3 s with the odd base.

Rules used in the fast check:

- Use odd bases (`B0 = 2^580 + 1`).
- Never multiply many values by large powers of two inside a loop. The constants involved are:
  - `C2 = 3·2^70`;
  - `SR = 2^192`;
  - `T64 = 2^64`;
  - `DE = 2^282·DEo`.

The fast check works with their odd parts. Interval tests compare `⌊e/2^90⌋` and `⌈e/2^90⌉`
instead, which `ivF_ivOk` proves equivalent.
