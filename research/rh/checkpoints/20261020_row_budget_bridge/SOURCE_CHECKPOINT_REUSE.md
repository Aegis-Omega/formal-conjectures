# Source-bound compilation checkpoint reuse

Run 39463716271 at f8ff0e20 compiled the complete original-import first-column continuation. Its final audit failed because two packed soundness outputs are in ring.log while it searched only actual-row-bridge.log. The old overall CI remains FAIL. All 105 actual compiler axiom outputs pass the corrected audit; the exact raw log, extracted audit input and source compile manifest are preserved.

The artifact has ID 12286013964, 174309882 bytes, SHA256 8f251ff3df3412556be71d45df7988c2f3a1e98301639d8ee497e9f5a3df3097. Local validation confirms all source files, 166 binary hashes, both log hashes and 105 standard-axiom roots. It also checks the complete Git tree difference so archived .lean.src files, generators, JSON proof inputs and configuration cannot change unnoticed. Only listed report/workflow metadata and new non-shadowing checkpoint files are allowed. Lean/Mathlib/provider pins must match.

The repaired existing workflow reuses that state only if every check passes. It generates and compiles a fresh import/type/axiom audit of the 105 roots. Reused dependencies are labelled as reused, rather than freshly source-compiled. Any failed validation falls back to the full original source build under set -euo pipefail and warningAsError. Missing packed outputs and injected sorryAx are independently rejected by regression checks. The cache does not assert any analytic premise, full hI, window positivity or RH.

No new job, branch, repository, paid resource or billing setting is introduced. The source archive and compiler evidence are permanently committed; large binary artifacts keep the existing one-day retention and can expire safely because full source replay remains available.
