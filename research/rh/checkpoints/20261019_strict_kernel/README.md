# Strict kernel replay of `CvSProjectedEntryL12V1.bigCheck` (work in progress)

Goal: a `decide +kernel` proof of `bigCheck = true`, which turns
`CvSProjectedEntryL12V1.projectedEntry_mem_certI_of_check` (pushed in c8c51cb, analytic bridge fully
proved, standard axioms) into an unconditional `hIv` for the packed 139x139 certificate at L = 6/5.
That is one window; it is NOT RH.

Nothing in this folder is imported or compiled by CI.

## Findings

1. The original `bigCheck` (getD-based `xI`, 423-long packed vectors) needs > 13 GB in the kernel
   (killed by the memory limit) and roughly 1 GB per column.
2. The Lean kernel reduces lazily and its caches do not prevent recomputation in this workload:
   consuming the same computed list four times costs about four times as much. Int results stay as
   unevaluated `Int.ofNat (...)` payloads, so every consumer recomputes `hF`, `kPk`, and the packs.
3. Fix: continuation-style forcing (`fN`, `fI`, `fL`, `fP` in `StrictCheckDraftV1.lean`). Each one
   binds the kernel-normalised literal once and is definitionally the identity (`fN_eq`, `fI_eq`,
   `fL_eq`, `fP_eq`), so soundness is proved on the readable spec (`colOf`, `colSpec`).
4. Measured (local, Lean 4.33.1):
   - forcing `kPk` once: ~20 s
   - X columns by streaming transpose + second differences: ~0.2 s per 10 columns
   - forced H-hat (141 packed products per column): ~1.75 s per column
   - a single gramEntry with literal arguments: ~2-3 ms
5. The full strict benchmark (`FastReplayBenchV1.lean`) still grows to > 13 GB anonymous memory
   after ~25 minutes. Suspected cause: the per-entry 282-long packed product (372 kbit products and
   quotients) for 9730 entries, all retained by kernel caches.

## Plan

- Reduce per-entry memory: either a naive forced Int dot product (no giant products), or split the
  entry loop into several theorems (the kernel caches are freed between declarations), with the
  column data recomputed or stored compactly.
- Replace the computational layer of `CvSProjectedEntryL12V1` with the strict form. Keep the names and
  statements `xI`, `hI`, `neI`, `radI`, `ivOk`, so the analytic proof (`entry_error`, `X_err`,
  `H_err`, `Ehat_eq`, ...) is unchanged. Only `xI_eq` replaces the old `rfl`, and the unpacking
  lemmas (`bigCheck_parts`, column parts, `neI_eq`) are re-proved via `StrictSoundDraftV1.lean`.
- Exact mirror: `tools/gen_projected_entry.py` (9730/9730 entries, 0 failures).

Algebraic note: H_ki = -(25 SI n_k^2 + C68) U_ki - 50 SI Lambda n_k w_ki with
U_ki = sum_{l != k} Lambda/(k-l) w_li holds (sum w = sum n w = 0 for second differences). It does not
shrink the packs, which are dominated by Lambda/(k-l) ~ 2^205; the cost is kernel steps per product.
