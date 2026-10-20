Exact mixed-column execution
============================

`envelope_pair_eq` proves the original finite interval envelope entry equals a list execution using a cached right Gram column. It holds at every finite size with explicit length and weighted-column identities. It assumes no positivity or symmetry. `check_sound` transports a successful concrete first-column check back to that original envelope expression.

The native proofs pass with standard axioms only. The 14 concrete batches are being verified sequentially and are not certified by the generic theorem alone. They reuse the unchanged X0/GX0/GDX0 from the previously kernel-verified first-cell source, use Q96 arithmetic and Q80 outward downscaling, and compare against the original stored target column.

The original-import actual source input enclosures pass separately at commit 177dcd64, CI 39455515829. Connecting their formulas to these literal data, the rest of the output matrix, the finite hB producer and universal Weil positivity remain separate obligations.
