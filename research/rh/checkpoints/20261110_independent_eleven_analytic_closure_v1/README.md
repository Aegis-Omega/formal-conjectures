# PR92: checked independent-eleven analytic composition

Source context: Aegis-Omega/formal-conjectures PR92 at
`023e7239e9af3df93fe2456a3be5e7a655a2f8e3`.

This packet preserves and kernel-checks the existing independent-shape argument
published at `c8fb2ffa5d5f12de0bd4627de6835e8e32d63940`. It does not introduce
new Schur weights, a new RH equivalence, or an assumed mixed-form bound.
The endpoint is
`AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive`.
Its full elaborated type is in `evidence/ACTUAL_FINAL_TYPE.txt`.

For eleven independently chosen smooth legal mother packets in the same closed
logarithmic interval `[a-1/256,a+1/256]`, both actual moments zero, translate
packet i by `i*log(33/16)`. For every eleven complex coefficients the full
arithmetic Weil form satisfies

    Re B(F,F) <= -(1203957/1136000) * sum_i E(h_i)*|z_i|^2.

All mixed terms are included. No hcross, hselect, hprime, RH, or universal
positivity hypothesis occurs in this theorem. The support geometry and moment
hypotheses remain explicit; arbitrary legal packets are not asserted to have
this geometry. The older arbitrary-packet finite fine decomposition is valid
but does not place all its pieces into these eleven specified windows.

## Actual verification

* Lean 4.33.1, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
* Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
* Full custom source closure: **186** modules. **24** were freshly compiled
  with `--trust=0`; **162** used verified, exact-source-closed checkpoint imports.
  Earlier prose counts 184/160 were inaccurate; the original machine receipts
  already recorded 186/162. The additive count amendment preserves the record.
* All six port/audit modules passed again with `-DwarningAsError=true`. The only changed original proof source
  is the gap-nine/ten adapter; all twelve declaration headers were preserved.
* Actual endpoint axiom list: `propext`, `Classical.choice`, `Quot.sound`.
  The 23 recorded axiom outputs are probes, not 23 new mathematical discoveries.
* A separate fresh endpoint compile passed. A separate `leanchecker` endpoint
  replay against the verified imports passed. Both used the same runtime.
* `leanchecker --fresh` for the full imported environment timed out after
  360 seconds. It is **not** recorded as a successful clean replay.
* The unchanged existing `NineFacesAcceptanceCheck` was really attempted:
  its six `exact?` calls did not solve their goals. This is neither a disproof
  nor an exhaustive proof search.

## Atomic source and instruction audit

The repository is a conjecture catalog. Its actual instructions allow the
catalog `by sorry` to remain when a genuine external proof has separately
passed the submission gate. The catalog placeholder alone does not establish
that an external proof is absent.

The recovered native checkpoint inspected 806481 elaborated declarations in
its imported environment. Its sole exact-RH candidate was the catalog theorem
with `sorryAx`; it found no closed exact-RH candidate in that environment.
The native receipt, source hashes and artifact identity are preserved here.
A further fresh elaborated-type inspection examined 60104 custom declarations
for six specific global producer types; it found no matches in that scope.
Neither inspection covers every unimported branch, repository or archive.

The PR97 direct-target receipt at `34325ef91faad247ba84cc10e8d87931e2783147`
rejected the catalog proof body, after the supporting module compilation had
succeeded. This packet does not weaken that gate or change existing checks.

## RH status and continuation

`RH_FINAL_EVIDENCE.json` deliberately has `rh_proven: false`.
No unrestricted RH theorem has been constructed in this execution.
The route-specific next task is to compose a producer covering the full actual
moment-zero class with the existing global consumer; this eleven-window
endpoint alone supplies no arbitrary-packet reconstruction/global signed budget.
This statement concerns this verified composition, not nonexistence of a proof
elsewhere. Existing V7 arithmetic integrability, V8 reflected-kernel identities,
finite fine reconstruction and restricted-window sign results remain preserved.

`MATHEMATICAL_COMPOSITION.md` gives the argument. `closure/` contains exact source
bytes for the dependency closure, `SOURCE_MANIFEST.json` identifies each module,
and `BUILD_ORDER.txt` gives topological order. `evidence/` contains real compiler
outputs, receipts and source snapshots, including explicitly rejected attempts.
Only the final source files in `closure/` define the accepted theorem. Rejected
attempts and the catalog placeholder are not premises of that theorem.

`replay.sh` is an optional full custom-source replay using an existing pinned
Mathlib cache. It does not install dependencies or build Mathlib. This complete
186-module source replay has not been run in this publication; the executed
scope is the 24 fresh modules plus 162 verified checkpoint imports above.
