# AEGIS Ω — official RH submission checkpoint (2026-10-21)

## Existing, merged lineage

- PR #91 exact head `d6dc5256a0a73773438cad49da222ff239b3aaf6` (source headers) is already an ancestor of PR #90. No replayed merge is necessary.
- PR #89 head `5d7425dcc6f4137b2cf3f57bc953504135a388e6` is already an ancestor of PR #90.
- PR #88 head `aacdd511877e3e725dbee05b1167ee38b681ab31` is already an ancestor of PR #90.
- Current working PR: [#90](https://github.com/tarikskalic33/formal-conjectures/pull/90). Protected main is unchanged.

## Cached evidence, not replaced

- [Cofinal exact-head kernel run 39661635889](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39661635889), artifact `12375461938`, digest `sha256:99f5da3b6482da932053376369bbc40c1f312387ec4b7762eadb03e15cc929c7`.
- [Cofinal kernel run 39642016784](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39642016784), artifact `12372237289`, digest `sha256:3ac6b4ffe6a58e8de56c130a50745028da4eb1d1e7253ee89ca5ef2865cf213c`.
- Workflow cache `.rh-cofinal-checkpoint`: source-blobs, sha256 of `.olean` objects and exact head; import reuse is verified by `scripts/rh_restore_source_bound_oleans.py`.
- Pinned Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

These historical artifacts prove their recorded source-bound scope. No statement of unconditional RH follows from a green workflow alone.

## DeepMind submission contract pinned on 2026-10-22

The current upstream reference checked for this handoff is
`google-deepmind/formal-conjectures@a7b87c8d0bb60e73782045d614d4a24907b87b8a`.

- Official RH source Git blob: `5b1dcd5c46ab4a5f449d7d4a5c5ddce7c89c3542`.
- Upstream `PROOFS.md` Git blob: `edf4eb1afdbf0182fd9ac603d0f23adf97003d4c`.
- The RH theorem remains `RiemannHypothesis.riemannHypothesis : RiemannHypothesis := by sorry` in the statement repository.
- DeepMind's current contribution rules require a solved problem to change
  `category research open` to `category research solved` and attach a stable
  `formal_proof using lean4 at "..."` link.
- Their proof policy requires opening the exact linked declaration, checking that
  it implies the repository statement, checking for `sorry` and custom axioms,
  and running `#print axioms`. A green build alone is explicitly insufficient.

The generated upstream patch therefore remains unavailable unless the exact-head
kernel census finds a body-bearing declaration definitionally equal to
`_root_.RiemannHypothesis`, the independent probe compiles it at that exact type,
and its axioms are a subset of `propext`, `Classical.choice`, and `Quot.sound`.
When those checks pass, the generated patch marks the theorem `research solved`
and links the exact immutable fork commit, source path, and declaration line.

## Submission packaging from the existing replay

The cofinal workflow now runs `scripts/rh_submission_from_checkpoint.py` **after** its original proof-graph exporter, reusing its already compiled `.olean` environment. It adds `RH_OFFICIAL_SUBMISSION.json` and `RH_OFFICIAL_SUBMISSION.md` to the existing evidence artifact.

If the current Lean environment contains an exact `_root_.RiemannHypothesis` theorem with a body and only standard axioms, the script selects its tracked, hash-bound source, independently compiles `example : _root_.RiemannHypothesis := ...`, audits `#print axioms`, and renders `upstream-formal-proof.patch` with an immutable commit and source line. A failed witness/axiom audit is an error, not an accepted submission.

If no exact proof term is present, the receipt records the **bounded imported-environment** result and does not fabricate an official proof link or assume anything about unchecked repositories. An official pull request still requires human review and the repository's contributor requirements.

## Official repository

[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — [PROOFS.md](https://github.com/google-deepmind/formal-conjectures/blob/main/PROOFS.md). Use `formal_proof using lean4 at` with an immutable external source declaration; do not replace the catalog placeholder with a large proof or link a conditional theorem.
