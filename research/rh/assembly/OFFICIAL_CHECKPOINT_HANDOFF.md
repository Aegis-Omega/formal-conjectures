# RH submission handoff

Working branch: [PR #90](https://github.com/tarikskalic33/formal-conjectures/pull/90).

## Source and checkpoint identities

- Ancestor commits: PR #91 `d6dc5256a0a73773438cad49da222ff239b3aaf6`; PR #89 `5d7425dcc6f4137b2cf3f57bc953504135a388e6`; PR #88 `aacdd511877e3e725dbee05b1167ee38b681ab31`.
- [Cofinal replay 39661635889](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39661635889): artifact `12375461938`, SHA-256 `99f5da3b6482da932053376369bbc40c1f312387ec4b7762eadb03e15cc929c7`.
- [Cofinal replay 39642016784](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39642016784): artifact `12372237289`, SHA-256 `3ac6b4ffe6a58e8de56c130a50745028da4eb1d1e7253ee89ca5ef2865cf213c`.
- Source-bound `.olean` cache: `.rh-cofinal-checkpoint`; restore verifier: `scripts/rh_restore_source_bound_oleans.py`.
- Toolchain: Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

## Official target

- Target repository/base: `google-deepmind/formal-conjectures:main`.
- Inspected upstream commit: `a7b87c8d0bb60e73782045d614d4a24907b87b8a`.
- RH source Git blob: `5b1dcd5c46ab4a5f449d7d4a5c5ddce7c89c3542`.
- `PROOFS.md` Git blob: `edf4eb1afdbf0182fd9ac603d0f23adf97003d4c`.
- Target declaration: `RiemannHypothesis.riemannHypothesis : _root_.RiemannHypothesis`.
- Submission format: `@[category research solved, AMS 11, formal_proof using lean4 at "<immutable declaration link>"]`.

## Kernel evidence to emit the patch

`scripts/rh_submission_from_checkpoint.py` reads the existing proof-graph export, verifies the exact official target source, checks a tracked body-bearing theorem definitionally equal to `_root_.RiemannHypothesis`, compiles a separate direct-application probe, and compares its `#print axioms` output with the exported dependency audit. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Outputs: `RH_OFFICIAL_SUBMISSION.json`, `RH_OFFICIAL_SUBMISSION.md`, and, after successful direct proof verification, `upstream-formal-proof.patch`.

## Upstream PR layout

The previous [upstream PR #7031](https://github.com/google-deepmind/formal-conjectures/pull/7031) was closed without merge. Review identified a remaining Lean goal, unresolved imports, and a 590-file diff. Use a new branch based on upstream `main`, not the existing RH working branch.

When the exact RH term passes the kernel/axiom gate, the upstream PR changes only `FormalConjectures/Millennium/RiemannHypothesis.lean`, retaining the catalog's `by sorry` and linking the externally verified declaration. Build against the upstream toolchain and follow [CONTRIBUTING.md](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md) and [PROOFS.md](https://github.com/google-deepmind/formal-conjectures/blob/main/PROOFS.md).
