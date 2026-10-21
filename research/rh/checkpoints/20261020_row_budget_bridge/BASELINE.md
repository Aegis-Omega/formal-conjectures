> Latest execution: CI39543410933 freshly accepted CvSKreinScalarUniformV1 (standard axioms), then failed at the window's Nat-zero rewrite. CI39556612118 at external commit d40702a2 also failed at that rewrite. That commit is preserved as an ancestor. The exact failing expression was reproduced locally; the archived source now uses a passing `simpa only [Nat.cast_zero, hz, Finset.sum_empty] using h` repair. A new original-import window replay is required. Historical "being checked" statements below refer to those completed runs.

# Continuation baseline

Repository: tarikskalic33/formal-conjectures. Existing branch: proof/rh-feshbach-schur-v1. Mathematical source snapshot: 7cc836ab5f6dff66b5643c9838d9c79d330ab68e. PR89 API head: 5d7425dcc6f4137b2cf3f57bc953504135a388e6; PR90 API head: 7fc73ce1ae0eb2afbaac778ae8ca8e7fbac07fcc. Neither is changed by this continuation.

Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are the active pins. The canonical RH definition remains unchanged. The existing external provider and PR53 build recipe are recorded in the workflow and machine receipts.

Original packed-checker/generator/handoff bytes were recovered from commit4fabfb66; no separate Claude filesystem is assumed mounted. H140 is a Hilbert stress test, not the actual CvS matrix. See ../../feshbach_lean_v1/H140_RECOVERY_REPORT.md for original/reconstructed hashes and replay evidence.

Actual finite dimensions: 139 atoms, 141 low frequencies, 301 residual rows. Full table kernel verification, actual analytic input membership, original-coordinate transport and hfin/hB are complete. Their exact-SHA scope and failed-later-run distinction are recorded in AEGIS_RH_MATHEMATICAL_ALIGNMENT.md and the named kernel receipts.

The new scalar/window wrapper is under original-import CI39543410933. The pending analytic target is its concrete all-real-t Krein witness and trace<=6, followed by a genuine universal/cofinal producer. No unconditional RH proof is asserted. This is not a completed inventory of every repository, PR or connected archive.

Preserve the unrelated untracked AEGISOverlay/RHSchurRowObstructionV1.lean, SHA256 354a915be730b80941fb9a5a029bc66b6e0e9a1c017650f728d49ed5f64ee004. Local *_REAUDIT.lean and *_REUSE_RECEIPT.json files are generated execution outputs; do not add them blindly.
