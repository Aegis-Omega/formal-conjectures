# Claude handoff: recovered results and actual proof attempts

The handoff at public formal-conjectures head
8686704f8d90853d5e0934d28db7964420ba847b was read in full. Its source
identities are in SOURCE_MANIFEST.json. Existing theorems are retained,
including the local window up to half-width 11/16; no replacement of that
proved interval by an older, smaller interval is intended.

## Four exact witnesses survived two different calculations

The pinned original certify.py was run at K=40 and 800-bit Arb precision
in four fresh directories, with newly constructed exact rational rho
tables. No existing pickle cache was loaded. Its rationalized trial
polynomials are saved as EXACT_WITNESS.json. Exact differentiation,
clamped endpoints and positive rational norms were checked. Vanishing
moments follow algebraically from those identities, not from interval
enclosures containing zero.

An independently written checker then evaluated each trial directly from
its monomial correlation polynomial. It imports no qwhp, cached matrix,
Legendre table, or eigenproblem. Final receipts all bind the same final
checker hash, with sixteen panels and explicit integration tolerances.
The underlying interval library is shared, so this is implementation
diversity, not an independent proof kernel. In particular these are NOT
Lean-certified numbers.

Safe convenient upper bounds for the two-moment Rayleigh infimum are:

| half-width a | rigorous convenient rational upper bound |
|---|---:|
| 3/4 | 77/10^11 |
| 1 | 2/10^18 |
| 5/4 | 5/10^23 |
| 3/2 | 43/10^27 |

The much tighter directed rational upper endpoints are in the final
receipts. Every bound includes all prime powers up to the certified
support cutoff and the infinite Archimedean tail analytically. The
same-support smooth moment-preserving approximation is proved in
DIRECT_WITNESS_SOUNDNESS.md. Hence the rough trial carrier is not being
silently substituted for the canonical legal smooth class.

There are two concrete corrections to the handoff:

1. The original nearest-decimal upper-endpoint formatting is not always
   outward. The literal printed 7.67846e-10 and 4.22158e-26 lie below
   their respective selected trial values. Also the coarser prose bounds
   1.9e-18 and 4.2e-26 do not follow from these trials. This does not
   refute those numerical bounds on the infimum; it invalidates the
   proposed inference from these particular witnesses. The table above
   uses conservative rational bounds actually verified.
2. A direct one-panel computation for the last two witnesses returned
   valid but very broad balls, approximately +/-0.104 and +/-0.142.
   Those runs did not certify the requested small upper bounds. A
   sixteen-panel partition resolves the enclosure loss; final direct
   values agree with the original matrix evaluation. No broad ball was
   called a successful small-margin certificate.

Fourteen malformed-input checks (seven cases, each ordinary Python and
python -O) reject zero trials, changed differential coefficients, changed
norms, wrong operator conventions, zero denominators, an unclamped but
differentially consistent potential, and duplicate JSON keys. All reject
before creating an acceptance receipt. Any different mathematically
valid witness remains admissible; this is not a claim that all altered
files must be invalid.

## Reuse the already existing Lean globalization proof

The complete body in Git blob caf80500f6347da25e8038cdce708275fc041951,
AEGISOverlay/RHGlobalizationChainV13.lean, was read. It already proves
globalization_limit_nonneg and uniform_lower_bound_collapses. These are
the Lean counterpart of the old Coq finite-to-limit theorem and the
degree-two scaling obstruction, respectively. They must not be reopened
as missing mathematical lemmas or needlessly ported a second time.

The pointwise-convergent actual CvS approximants from the previous
checkpoint can supply a convergence argument, but their sign is not
supplied by a positive trial Rayleigh value. Neither this calculation nor
the recovered theorem closes the finite-sign input. The manuscript
ACTUAL_CVS_CONVERGENCE_PRODUCER.md remains an ordinary proof, with its
formal port and independent analytic review status unchanged.

Targeted full-body review also covered the actual universal fine Gram,
optimized row selector, canonical resonance selector, signed global join,
and translated RKHS socket. The first gives actual decompositions and
diagonal margins. The latter consumers still display their actual mixed
budgets/selectors as arguments. The false ALL-decompositions budget is
already refuted in RHUniformBudgetObstructionV1; the existential selected
decomposition is a different statement. These source findings are not
an exhaustive nonexistence claim about every branch.

APPARENT_ENDPOINT_CENSUS.json records ten source-syntax matches for a
premise-free literal RH declaration in the recovered 941-tip source
scope. Two have explicit sorry; eight are short apply/exact probes of
consumers whose source types still require the displayed global input.
This census is a search aid, not a typecheck and not an audit of arbitrary
aliases or all historical commits. No final canonical proof term has been
accepted on its basis.

## The next mechanism was attacked, rather than renamed

A Perron/positivity-preserving-semigroup strategy on the odd half-line
block fails for the actual zeta form already at a=1/2. The new ordinary
proof in ../OddSemigroupAttack/ACTUAL_PRIME_REFLECTION_OBSTRUCTION.md
constructs disjoint nonnegative half-line profiles whose odd extensions
have a positive mixed Weil value. The reflected prime n=2 supplies
sqrt(2)*log(2); all Archimedean and polar contributions are bounded.
The smooth argument is uniform in the chosen normalized bump and does
not rely on numerics. The complete-form Arb values for an explicit H^1
profile are about 0.97501566 and 0.97763692 for two shrinking scales.
Independent Fourier-coordinate quadrature agrees on the Archimedean
term; its floating error estimates are diagnostic only.

This falsifies an extension mechanism, not RH, not local PSD, and not
every conceivable invariant-cone construction. It gives a precise reason
that generic positivity of prime weights cannot be turned into a Perron
argument on this parity cone. On the odd moment-zero class that cone
is in fact trivial; a different cone would require its own proof.

## Literature check and boundary

The primary text of Suzuki, arXiv:2610.32704 (October 2026), was recovered.
Its Theorems 1.1 and 1.2 explicitly ASSUME RH. The local unshifted form
becomes the global Hilbert-space embedding under that assumption. Thus
this new convergence result cannot discharge the remaining sign by
unconditional composition. The full primary extract is stored locally;
it has not been substituted for its hypotheses.

Connes--Consani--Moscovici, arXiv:2511.22755, Theorem 1.1 explicitly
requires simplicity and evenness of the minimum eigenvector. The
proposed large-window determinant convergence is a further argument,
not a consequence of one finite trial or the self-adjointness of the
finite approximants. No additional RH equivalence was formalized here.

The smallest outstanding mathematical producer on the active positive-
complement route remains, for EVERY integer radius R and every actual
balanced low vector v,

    Q(v) >= sup_(0 != V in V_R) |B_Q(v,V)|^2 / Q(V).

The full high-moment complement V_R and its positive lower bound were
constructed in the previous checkpoint. This statement is not assumed
proved and is not weakened to the finite trial space. The current work
discharges none of that universal sign by fiat. rh_proven=false.

## Reproduction

Install python-flint==0.9.0 (and mpmath for the original generator) in an
isolated Python environment. No Lean or Mathlib is required for the
numerical checker, and it does not claim to replace either.

    python check_exact_witness.py replay_a3_4_K40/EXACT_WITNESS.json new_a3_4.json --panels 16
    python check_exact_witness.py replay_a1_1_K40/EXACT_WITNESS.json new_a1_1.json --panels 16
    python check_exact_witness.py replay_a5_4_K40/EXACT_WITNESS.json new_a5_4.json --panels 16
    python check_exact_witness.py replay_a3_2_K40/EXACT_WITNESS.json new_a3_2.json --panels 16

The optional original generator refuses to overwrite existing witness
directories. Copy replay_original.py, certify.py and qwhp.py to a FRESH
directory and run `python replay_original.py 3 4`, etc. The wrapper's
qwhp lookup has been made relative after the original execution; the
actual certify.py/qwhp.py bytes and exact saved inputs are unchanged.
No external pre-existing pickle cache is part of the evidence.

The forty-three-lane historical bundle supplied later by the user was
also downloaded and verified locally: SHA-256, git bundle verify, and
all listed head identities pass, and all forty-three heads were already
present in the frozen index. Its private manifest and binary are not
republished in this public research checkpoint.
