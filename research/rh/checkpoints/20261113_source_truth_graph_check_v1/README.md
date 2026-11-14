# The unified source truth graph of 2026-10-30, checked against the window chain

Date: 2026-11-13. A provenance check of Git blobs and build plans; no mathematical claim, nothing
promoted. **RH remains OPEN.**

## The report

`AEGIS_RH_UNIFIED_SOURCE_TRUTH_GRAPH_20261030.json` is the report as received (5407 bytes, sha256
`30a35786b3955181fe5da9739598398121e715a05b91f94fffe26c95f783992f`, verified). It is bound to
`054bed1834e0e8ed68aed6d123b68ce1f10d78d7` and counts 780 Lean module aliases, 826 source
occurrences, 806,414 declarations in the imported environment and 72,684 declarations reachable from
107 DAG roots. It does not list the 107 roots, and its two input archives
(`graph_zip_sha256 d3321f4a…`, `cofinal_zip_sha256 a50f72ac…`) are not in this repository (no archive
here has either hash), so the two declaration counts cannot be regenerated from it; they stay
`external_claim`. Its canonical-target section finds no closed term of the RH type
(`closed_canonical_rh_declarations: []`, `has_finished_RH_proof: null`).

## Checks at `054bed18` and at the head of this branch (`00d9b406`)

* The eight blobs of `divergent_module_details` are exactly the tree blobs at both commits (the four
  marked `bytes_verified: false` included).
* `RHFixIntervalV1`: the two copies differ only in their imports (`Mathlib` against
  `Mathlib.Analysis.Complex.Norm` and `Mathlib.Algebra.Order.BigOperators.Ring.Finset`); the bodies are
  equal. The window chain compiles `critical_line_v1/RHFixIntervalV1.lean` (`0ee94b9b`), the blob that
  `rh-feshbach-schur-v1.yml` and `rh-row-budget-native-replay.yml` pin.
* `RHDyadicDiagonalV13`, `RHEulerGammaV13`, `RHKreinPairingV13` and the unresolved import
  `RHHardyNormalizationV1` are not in the import closure of the exhaustion theorems; no file
  `RHHardyNormalizationV1.lean` exists at either commit.

## The window chain's own source selection

The exhaustion theorems (`RHWindowL…ExhaustionV1`) build on the 1019-module lab closure that
`../20261020_row_budget_bridge/window_l65_source/plan.py` selects (as `rh-cvs-window-l65-source.yml`
runs it) and `build.py` compiles; the local plan of the windows `3/2` to `39/25` (sha256
`793b899f…`) passed 1019 / 1019. `check_plan_sources.py` compares every compiled source with every
same-name `.lean` file in the tree (`PLAN_SOURCES_00d9b406.txt`; a qualified module name `A.B.M` is
looked up as `M.lean` since 2026-11-14 — this plan has no qualified names and the report is
unchanged byte for byte):

* 873 modules are extracted from the committed `ACTUAL_INPUT_SOURCES.zip` and `FULL_TABLE_SOURCES.zip`
  (manifest hash checks in `plan.py`); 70 come from the Krein ring closure list, each checked by blob
  (`krein_ring_closure.json`; its `.lean.src` snapshots are staged under `.lake/ringstage`).
* Of 235 pairs (compiled source, tree copy of the same name), 172 are identical and 30 differ only in
  the licence header or imports.
* 16 modules are compiled from a source whose body differs from a same-name copy in the tree, all in
  the 96-module closure of `V13Scratch` (whose `final_sign_iff_rh_v13` links the windows to Mathlib's
  `RiemannHypothesis`): twelve `AegisRH/PR606/Compat` modules, chosen before `Source` and the
  `PR606` port by `plan.py` (lines 108–111), and four `WeilFixedLine*Gamma*V10` modules from `.lean.src`
  snapshots, whose statements assume `0 < c` where the `AegisRH/PR606` copies assume `1 < c`.
* `scripts/rh_pr63_proved_window_prebuild.sh` (the small-window producer) resolves the same names in
  the opposite order (the `PR606` port before `Compat`, except `WeilZeroTwoPointV11`), so the two lanes
  compile different sources under the same module names.

So the report's `HOLD` on divergent blobs applies to the window chain in sixteen places it did not
scan (`AegisRH/` is outside its scope). The chain's choice is fixed by `plan.py` and its blob checks,
and each compiled source is kernel-checked in its own build, so the receipts stand; but a module
resolved by name alone, as a DAG over aliases does, is not always the module that was compiled. A
declaration index of the chain has to be taken from the built environment of this plan, with its
roots listed.

Replay (repository root, after `plan.py` has written `.lake/real_plan.json`):
`python3 research/rh/checkpoints/20261113_source_truth_graph_check_v1/check_plan_sources.py .lake/real_plan.json 00d9b406`.
