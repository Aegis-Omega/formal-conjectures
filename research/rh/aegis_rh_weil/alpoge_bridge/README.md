# Bridge to Levent Alpöge's Lean proof: NOT BUILT

`AegisAlpogeBridgeV1.lean` has **not been built**. It is not part of the Lake package in `..`.

## What it is

The file imports `Main` from Alpöge's library: branch `original`, commit `40e56bab`, of
`github.com/Deicyde/riemann-hypothesis`. It instantiates AEGIS Weil-side theorems with his
`riemannHypothesis : RiemannHypothesis`.

| theorem | statement |
|---|---|
| `aegis_final_sign` | `FinalSignResidualV1`: `Re W(g ⋆ g) ≤ 0` for every moment-zero packet |
| `aegis_weil_sign` | the same, for one packet |
| `aegis_zero_quadratic_nonnegative` | the zero quadratic is nonnegative for every packet |
| `aegis_strict_sign_iff_mellin` | `StrictWeilSign ↔ MellinZeroNonvanishing` |
| `aegis_nondeg_iff_mellin` | `WeilNondegenerate ↔ MellinZeroNonvanishing` |
| `aegis_fineBudget_iff_mellin` | `c ≤ 43/10 → (FineBudget c ↔ MellinZeroNonvanishing)` |

## What has been checked

* **The same terms are built with RH as a hypothesis.** `../AegisAlpogeBridgeCheckV1.lean` contains them with
  `riemannHypothesis` replaced by a hypothesis `hRH : RiemannHypothesis`. It is part of the Lake package and is
  built (see `../README.md`).
* **Same statement of RH.** Both libraries use Mathlib's `RiemannHypothesis` at the same Mathlib commit,
  `0df444a3`. Alpöge's `riemannHypothesis` is a root-level theorem in `src/Main.lean`. None of the 200 modules in
  `..` declares a constant with that name.
* **No module-name clash.** None of the 201 module names (the 200 of `..` plus this bridge) is among the 174,793
  module names under `src/` of commit `40e56bab`. No top-level prefix is shared either. Declaration names were
  not compared.

## Why it is not built here

From Alpöge's repository (`origin/main`, `c900e67c`):

* `src/` of commit `40e56bab` holds 174,793 Lean files;
* `README.md`: "A full build takes hours";
* `verification/CI-RUNNERS.md`: "ideally 128 GiB RAM; at least 250 GiB free SSD";
* `verification/NOTES.md`: the solution export is 61,570,614,651 bytes.

The machine used for this chain has 15 GB of RAM and about 2 GB of free disk.

## What it would not change

* The RH content would come entirely from Alpöge's theorem, not from the AEGIS chain.
* `MellinZeroNonvanishing` and `DistinctZeroSuperlinear` (`WeilMellinZeroDensityV1`) would remain open.

SHA-256 of the source:

    2543df6f73f2aa51ef69df46be328e9909be2349a7852e2287ee3468085b3342  AegisAlpogeBridgeV1.lean
