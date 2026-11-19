# AEGIS Suzuki source-composition continuation, 2026-11-03

`rh_proven=false`. No final canonical Lean RH proof is supplied here.

The prior checkpoint is commit
`4af47485db18d261974e75a46cfa2f7473bf6a68` in
`Aegis-Omega/formal-conjectures`. It is preserved unchanged.
This additive checkpoint recovers exact Suzuki source conditions,
corrects an actual older printed derivative, checks that correction
with Arb and a separate mpmath diagnostic, and records why two
specific existing compositions do not supply the global sign.
Existing finite-a spectral theorems are retained as proved in the
literature. No novelty claim is made for their mathematical contents.

Read `SUZUKI_SOURCE_COMPOSITION.md` for the analytic derivation and
precise trust boundary. `RECOVERED_LITERATURE_SCOPE.md` records the
newer public signed-bound paper and its finite domain. Its archive
manifest was checked; its mathematical certificate was NOT replayed.

For the normalization check use Python with python-flint 0.9.0 and
the exact source PDF at
https://export.arxiv.org/pdf/2206.03682v4.pdf
(required SHA-256 is in SOURCE_MANIFEST.json). Then run, choosing a
new output path:

    python3 verify_suzuki_normalization.py SUZUKI_2206_03682v4.pdf FRESH_RECEIPT.json

The checker uses 300-bit outward balls and an explicit infinite series
tail. It rejects a changed PDF and an existing receipt. The negative
source test also rejected under `python -O`; no Python assertion
provides an acceptance condition. The separate mpmath check is
diagnostic only, not a certified bound. No new Lean compilation or
axiom audit is claimed for these analytic assertions.

Primary PDFs, third-party reproduction ZIPs and private Drive handoffs
are not included. Their absence from the public package does not imply
that they were inaccessible locally. The manifest and source URLs
identify the public inputs precisely. Raw private content was not
republished.

The exact selected producer still missing on this route is eventual
nonnegativity of the actual Psi_0 from Suzuki (1.1). The existing
Theorem 11.1 already provides its implication to RH. The weaker
subexponential negative-part criterion is also already in the recovered
literature, and has not been proved unconditionally here. Neither is
silently assumed. No claim is made that this is the unique obstruction
for all other AEGIS routes or that unreviewed sources contain no proof.
