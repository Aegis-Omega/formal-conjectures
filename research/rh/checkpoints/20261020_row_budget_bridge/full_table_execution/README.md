# Full-table continuation, preserved during execution

This continues b133be9d on the existing Feshbach branch. It does not restart H140 or alter the certificate. The data are the original exact Q96 inputs, Q48 projection and Q80 target boxes. The archive contains all generated Lean source candidates and the exact input JSON; no compiled binary is needed to recover their bytes.

CvSCachedColumnV1 and CvSCachedEnvelopeJoinV1 compiled with Lean 4.33.1 and the pinned Mathlib. Their six printed axiom audits contain only propext, Classical.choice and Quot.sound. They prove exact cached dot evaluation, exact reduction of every original envelope entry, and transfer of checked containment to real membership. Every source identity, signed bound, length and carry hypothesis is explicit. They do not assume positivity or RH.

The first checked Gram-product module also passes. The bulk cache/input/product/output replay is in progress. Generated `by decide +kernel` declarations in the archive are candidates until the receipt records their successful compilation. SOURCE_MANIFEST.json records the snapshot scope; it is not a full-matrix PASS receipt. The existing 105-root green CI does not certify this extension.

The generators use the input JSON from the archive. Run generate_full_table.py, generate_products_and_checks.py and make_aggregate_interface.py in that order. Existing native dependencies are archived in ../NATIVE_PACKED_COLUMN_GRAPH.zip. replay_full_table.py uses the existing pinned repository and those native dependency directories. It fails on a compiler error or a nonstandard printed axiom and records source/log hashes.

Next: finish all input cache proofs, all 278 original Gram-column product checks, and all 19,321 ordered output comparisons; compose the resulting complete finite enclosure. Then identify the literal inputs with the proved analytic source formulas. The all-real-t Krein and universal Weil obligations require their own proofs.
