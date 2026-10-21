> Latest execution: CI39543410933 freshly accepted CvSKreinScalarUniformV1 (standard axioms), then failed at the window's Nat-zero rewrite. CI39556612118 at external commit d40702a2 also failed at that rewrite. That commit is preserved as an ancestor. The exact failing expression was reproduced locally; the archived source now uses a passing `simpa only [Nat.cast_zero, hz, Finset.sum_empty] using h` repair. A new original-import window replay is required. Historical "being checked" statements below refer to those completed runs.

# Active continuation

Read the result of CI39543410933 at 7cc836ab5f6dff66b5643c9838d9c79d330ab68e on the existing proof/rh-feshbach-schur-v1 branch. It validates 431 previously accepted actual-input modules, freshly checks the uniform scalar lemma and repaired window wrapper (433 planned modules total), then exports the strict original-import declaration graph.

Already kernel proved: the entire 19,321-entry finite certificate, actual analytic input memberships, correct inverse-2pi normalization, basis transport, and original-vector hfin/hB. Do not reconstruct or reclassify these as missing. Read ACTUAL_SOURCE_BUDGET_KERNEL_PASS.json and HFIN_HB_KERNEL_PASS.json for their source-bound types, logs, axioms and precise scope.

If replay fails, inspect the exact source error. Preserve and validate the successful module prefix with reuse_actual_input_prefix.py; never reuse a failed module or a dependant of changed source. Fresh data-definition axiom audits remain required. Do not mix native narrowed-import binaries with original-import binaries. Original cache artifacts and validated binaries are preserved locally; the existing workflow uploads its partial state on failure.

If the wrapper passes, preserve its full types, axiom audits, actual dependency graph and source hashes. If only graph metadata export fails, record the successful mathematical module independently and repair the graph exporter.

The next mathematical obligation is the concrete Krein certificate and trace<=6 for window_of_trace_le_six, with m>=31/16 and its regularity/support requirements. UNTRUSTED_KREIN_* is newly reconstructed numerical evidence only; validator PASS is not Lean PASS. After a fixed-window instantiation, a universal/cofinal producer is still required for RH.

Push coherent verified checkpoints to the existing branch after checking the remote head. Do not force-push, create branches, merge PRs or alter protected main. Preserve unrelated untracked AEGISOverlay/RHSchurRowObstructionV1.lean (SHA256354a915be730b80941fb9a5a029bc66b6e0e9a1c017650f728d49ed5f64ee004).
