# Reuse optimized weights and supply the independent-shape mixed estimate

Read `WEIGHTED_SHAPE_COMPOSITION.md` for the complete ordinary argument and
its exact function class. It proves the394709/1136000 margin on the stated
eleven-window family without an extra mixed-bound hypothesis. It does not
assert universal Weil positivity or RH.

The original source's weights are reused unchanged. This package contains
an analytic composition, a source-bound exact data extraction, and a
standalone kernel arithmetic component. It is not the previously mentioned
ZIP or an altered copy of an unavailable adapter.

## Reproduce the arithmetic with the exact original source

In a checkout containing commit1f70364296eee931d0cae5ecc16a0c9810c0c4cc:

```bash
git show 1f70364296eee931d0cae5ecc16a0c9810c0c4cc:AEGISOverlay/RHActualElevenLatticeV1.lean > RHActualElevenLatticeV1.source
python3 verify_source_and_emit_arithmetic.py --source RHActualElevenLatticeV1.source
lean --trust=0 -DwarningAsError=true -o WeightedIndependentShapeArithmetic.olean WeightedIndependentShapeArithmetic.lean
LEAN_PATH="$PWD" leanchecker --fresh -v WeightedIndependentShapeArithmetic
```

Use Lean4.33.1, compiler819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
No Mathlib import, network download, full Lake build, or hosted workflow is
needed for this standalone arithmetic replay. The source extractor requires
the exact original Git blob and rejects a different source before emitting.

`ARITHMETIC_KERNEL_RECEIPT.json` records two clean compilations and fresh
replays already executed here. Their complete logs are included. Four
declarations use standard `propext`; three use no axioms. No `sorryAx` or
new mathematical axiom is present in these arithmetic declarations.

The actual-B analytic bridge needs its separate Mathlib/AEGIS formal port
and replay. The ordinary proof is not relabeled as that replay.
