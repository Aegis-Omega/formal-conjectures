Exact packed interval execution
===============================

`packedIntervalDot_eq` reuses the existing signed `gramEntry_eq` theorem. Its four exact signed dot products reproduce the center and radius of the original interval dot; all floor/ceiling operations remain unchanged. The digit/carry bound is explicit. `cachedIntervalDot_eq` permits shared forward/reverse packed rows only after exact preparation equalities. There is no assumed finite-width overflow behavior or floating-point proof.

The actual unchanged 301-element residual column Z0 supplies a native kernel pilot. B=2^128 and base=2^280 satisfy the checked component and carry bounds. Kernel evaluation verifies the complete cache, computes the dot endpoints, proves equality to the old list evaluator, and rejects a one-unit corruption of the packed middle row. All six pilot audits pass; 3.440 seconds and 2,227,376 KiB maximum child RSS. This is a correctness pilot, not a measured full-matrix speedup or a full table/analytic/RH proof.

The source is new work reusing the recovered library, not recovered Claude bytes. Current full original-import CI covers the first-column continuation separately; this packed extension is native-verified and not included in that CI run.
