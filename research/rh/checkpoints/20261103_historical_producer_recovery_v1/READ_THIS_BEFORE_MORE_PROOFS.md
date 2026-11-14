# Reuse the existing proofs before constructing another argument

2026-11-03. This is a recovery/reuse correction, not another RH criterion
or a new theorem. The earlier checkpoints are preserved.

The previous source-body directory covered selected branch/PR tips. It did
not include every intermediate historical mathematical source. A fresh
read-only fetch recovered 101 current fork heads and 674 AEGIS-OMEGA heads.
Traversing their locally available Git history, including the prior PR
refs, recovered 1260 additional distinct mathematical source blobs:
804 Lean, 111 Coq, 150 Python and 195 Markdown. These are byte-distinct
versions, not 1260 new mathematical results. Some coincide with separate
already saved local work. Git blob checks passed for every body.

HISTORY_INTAKE_MANIFEST.json.gz records the source paths, repositories,
Git blob identities, byte counts and SHA-256 hashes. Its compressed and
uncompressed hashes are in TARGETED_REVIEW.json. Full source bodies remain
in the local intake and the source Git histories; no claim is made that
this manifest is a complete semantic audit.

## Existing results: do not reconstruct them

* Commit 574c92ccf43fc6fe13c7b466a74f9cff21b4a8e8 already proves
  `AEGIS.WeightedSchur.weighted_gram_variable_energy` for unequal energies.
* Commit ae5a2f289ab7a51e7eb08c54f99599468a11eb72 already applies the
  optimized bound to arbitrary unequal-energy actual Weil Gram families.
* Commit 8b7627cbfcaf707b775d4132173ab8b5acaaf9a4 already retains the
  exact diagonal and signed defect through
  `actual_signed_defect_iff_packet_nonpositive`, and pays it on the
  stated cluster geometry. This direction is not a new proposal.
* `RHCvSActualWeilInteropV1.actual_signed_budget_of_zero_side` already
  constructs the genuine signed budget for the very same packet from
  that packet's zero-side sign. It is not necessary to invent hselect
  in a second architecture if an actual sign producer is available.
* `RHGlobalizationChainV13.globalization_limit_nonneg` already proves
  the abstract limit passage. It does not need another mathematical proof.

## Actual composition examined in this continuation

The complete bodies of the CvS interop and historical cofinal adapters
were read, including historical blobs
665722f84a710f1453dc75fdf10b519db6fe22f0 and
5a9d6dbe53abc7b7a35ba34815158b2d7878ce5c. The former already composes
the source's projected certificate with the actual low-block quadratic
using the existing finite congruence. Preserve that result under its
actual quantifiers: M>=3, every v in Fin139->Complex, fixed length6/5.

`actual_signed_budget_of_exact_projectedQ` then accepts the explicit
equality between projectedQ M v and the true zero quadratic of g.
`riemannHypothesis_of_universal_actual_cvs_cofinal` instead accepts the
displayed scalar convergence for every g. Neither equality nor universal
convergence is constructed by those inspected proof bodies themselves.

The previously written actual-function approximation on expanding CvS
spaces is a different proved ordinary result. Its dimension grows; it
cannot be silently supplied as a sequence in the fixed Fin139 source
of this historical adapter. That is an exact domain mismatch, not an
absence of a Lean build and not an assertion that a producer cannot
exist elsewhere.

This targeted review has not closed the global composition. Searches
for the displayed structure constructors also covered the added
historical bodies, but literal searches are not elaborated-type scans
and do not exclude aliases or arguments in unreviewed manuscripts.
Do not turn this scoped result into a global nonexistence claim.

No new mathematical theorem was written or compiled in this intake.
No archived candidate code was executed. No historical proof was marked
false merely because a replay was absent. The bodies and hypotheses
above, rather than status labels, determine the recorded scope.

## Recover a listed source body

After fetching the source repository's heads and relevant PR histories,
use `git cat-file blob BLOB_SHA` for an entry from the manifest. Verify
both its recorded SHA-256 and its Git blob identity before use. A bare
Git fetch changes no remote branch, main, workflow or permissions.
Objects unavailable to another session must be reported as unavailable,
not recreated and attributed to the original bytes.

RH remains unproved in this continuation. This intake is a checkpoint
for continuing actual source composition, not completion of the mission.
