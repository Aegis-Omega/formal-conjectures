# Complete finite row-envelope verification

The native Lean kernel accepted all 19321 ordered entries of the unchanged 139 by 139 Q80 target. It also accepted all cached input preparation identities, 278 original Gram-column products, the original-envelope identity, real enclosure transfer and a quantitative complex budget. The exact positive margin is 167597168023440173239 / 604462909807314587353088.

The terminal `CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs` retains exactly the input memberships and real q/g symmetry. It has no unverified output-check or output-positivity premise. This is not yet an unconditional actual-CvS theorem or RH proof. The literal inputs must still be identified with the existing analytic source formulas. The fixed-window Krein and universal Weil obligations are separate.

FULL_TABLE_SOURCES.zip preserves all exact Lean sources and the input JSON. SOURCE_MANIFEST.json binds their bytes and the per-module native status. FULL_TABLE_KERNEL_RECEIPT.json records 445 successful source-module executions at this snapshot; compiler logs are in FULL_TABLE_COMPILER_LOGS.zip. FULL_TABLE_PROOF_GRAPH.zip contains the raw 12-root dependency graph and exporter. The condensed DAG is FULL_TABLE_PROOF_GRAPH.json. Only standard axioms occur.

Reconstruct the inputs with reconstruct_exact_inputs.py. It verifies byte-for-byte equality with the original committed source and Q48 projection, without executing a floating fit. Extract the sources from the archive for replay; the generators are also preserved. Existing native custom dependencies are in ../NATIVE_PACKED_COLUMN_GRAPH.zip. replay_full_table.py uses the pinned repository and those native dependency directories. The actual CI commands are in run_ci_full_table.py and the existing rh-cvs-actual-row-replay.yml workflow. Native narrowed imports are documented in the receipt; a prior green CI is not attributed to the new sources.

SOURCE_BINDING_NEXT_INPUTS.zip contains the exact reconstructed E, Y, Lambda and X*Lambda arrays for the next input-membership step. No Lean analytic membership is claimed for this auxiliary archive.
