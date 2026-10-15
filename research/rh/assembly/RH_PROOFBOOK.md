# AEGIS Ω source-bound proof assembly

This is a partial execution artifact. No unconditional RH theorem is asserted.
The constructor in AEGIS_RH_Unconditional.lean is restricted to the already
certified 693/2000 log-window class. The exact-head CI receipt, not this
committed snapshot, determines its kernel verification status.

## Canonical target

Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 defines:

```lean
RiemannHypothesis :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0)
    (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## Existing verified route

- PR83 head fed5269b549ec846a5c5d821ceca7af399b6b0fe has successful
  exact-source cofinal run 38567547533, job 115863986349. The original
  eventual/all-indices mismatch in RHFeshbachWeilClosureV2 is kernel-closed.
- PR86 parent efc691a1fddcc26ed1a057b3c748cb01709cfdfd has successful
  run 38577005420, job 115896640636: 212 modules compiled, standard axioms only.
  The first parser error was closed by opening ContDiff scope.
- RHKreinMultiplicativeTransportV1 supplies actual moment-zero packets;
  RHFiniteActualGramJoinV1.every_packet_actual_finite_gram gives the full
  genuine Weil Gram representation, including mixed entries.
- RHCofinalSchurAdapterV1.actual_zero_quadratic_nonnegative_of_gram_bounds
  consumes actual hdiag, hcross, hrow and hmargin estimates.
- RHFeshbachWeilClosureV2.packet_zero_quadratic_nonnegative transfers a valid
  PacketSchurFamily to the canonical zero sum. The V10 autocorrelation
  explicit formula converts its sign to the actual Weil arithmetic sign.
- RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families is the
  final consumer of the universal family producer recorded in RH_BLOCKER.json.

Representation and positivity are separate mathematical results.

## Concrete construction

Let A = -Re B(g,g) and E = energy(g). Set N(j)=j, a(j)=A,
normSq(j)=E, nv(j)=sqrt(E), c(j)=1 and re_b=q=nw=beta=mu=0.
The existing certified narrow-window theorem gives A>=0; the energy theorem
gives E>=0. The explicit formula identifies A with the actual canonical zero
quadratic. Constant convergence, norm boundedness and the zero-tail inequalities
discharge the structural fields. The Schur lower bound is
-invFourthError(0,j)*E <= 0 <= A.

This constructs the repository scalar family interface on that certified class.
It does not supply an arbitrary finite-matrix approximation for every packet.

The isolated probe attempts to use pi-window membership as the narrow-window
argument. CI writes its actual compiler result to RH_CLOSURE_PROBE.log and
RH_BLOCKER.json. An expected mismatch is not evidence until executed, and
the probe is not an RH success criterion.

## Other inspected source paths and scope limits

PR80 head 0f4415fa056e775d39b9c915733568fbdf248fc5 has successful consolidated
run 38139018737: the positive result is for 0<=L<21/40, while the large-window
terminal is an RH equivalence. PR47 head 43fc4ad926f244330117bf7041101afe54450896
has successful Mellin construction run 38558256890. PR39 head
5213510f3a6d5be92db4e334546272ab2a08c024 has successful paired/Li run
36962943809; its terminal retains WeightedPairedNonnegativityV1.

The Abjad source proves triadic/mod12 phase routing into the four-phase carrier;
its arithmetic type is not silently promoted to universal analytic positivity.
Finite Gram, local Krein and cofinal adapters are preserved with their actual
hypotheses.

The graph records compiled module imports and source theorem statements,
explicitly distinguished from elaborated proof-term edges. A complete
all-history repository census and elaborated declaration DAG have not been
completed. Eight historical root inputs have exact Git blob/source hashes
but no identified containing historical commit.

## Evidence and reproduction

The workflow generates all six requested artifact names in
evidence-cofinal/assembly, copies the exact compiled source bytes, records
source hashes, actual checkout SHA, Lean/Mathlib versions, run/job references,
printed axioms and the observed probe failure. Artifact names may contain a
synthetic PR merge SHA; the checkout receipt is authoritative.

RH_EXACT_HEAD_REPLAY.sh replays the pinned workflow shell steps on a fresh
normal Lean host. No sorry, admit, new custom axiom, existing theorem statement
change, protected-main mutation, merge or RH status promotion is made.


## Actual eleven-translate analytic assembly

`AEGIS.RHActualElevenLatticeV1.all_actual_eleven_mixed_bounds` derives all
110 directed off-diagonal bounds (55 Hermitian pairs) for eleven translates
of one moment-zero packet of total log width 1/128. Gaps 1–8 cost 1/100
of the common energy, gap 9 costs 57/100, and gap 10 costs 837/3700.
Every diagonal has gain 5671/3200. The existing actual Gram theorem then
gives `actual_eleven_lattice_arithmetic_nonpositive` for arbitrary complex
coefficients. This proof supplies analytic coefficients rather than
assuming the eleven SOS inputs. These declarations passed at exact head
`edac34b902d8deba6810a61a0e1816506369d9cc`, run `38627745660`,
job `116071121734`. This historical PASS is not the verdict for a newer head.

The finite lattice class is not an exhaustive support-local partition:
its atoms are translates of one mother packet at spacing log(33/16).
The local partition construction permits different atoms at unrelated
centers and nonuniform energies. Applying the lattice estimates to that
construction requires a proved connecting representation or a new mixed
estimate. The radius-9/64 result requires a common support window for its
four polarized sums, which separated lattice pairs do not satisfy.


## Constructed finite partitions and arbitrary-packet fine Gram

`RHFiniteFinePartitionV1.exists_finite_smooth_local_partition` uses a
finite subcover of a compact interval by arbitrarily small open intervals
and the pinned Mathlib smooth partition of unity. It returns actual smooth
complex cutoffs whose sum is one on that interval and whose closed supports
lie in the prescribed small intervals. The caller supplies no partition.

`RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram`
combines that construction at radius 1/256 with the existing finite log
window and actual Krein localization. For every admissible moment-zero
packet it returns moment-zero components, gain 5671/3200 for every
diagonal, exact packet reconstruction, and the full actual mixed Gram.
Its quantitative mixed-defect theorem retains every off-diagonal term.
These new declarations require their own observed exact-head kernel replay.

The remaining sign step is an upper bound on the actual mixed defect for
a suitable such decomposition, or an actual cofinal Schur construction.
The diagonal estimate and exact reconstruction do not assume that bound.

## Q16.16 outward-rounded actual eleven-packet certificate

`RHActualElevenLatticeV1.actual_eleven_lattice_q16_coercive` derives the actual Weil bound with margin `7339/8192` for every complex coefficient vector on eleven lattice translates of one fine moment-zero seed. The analytic costs are rounded upward to `656/65536` (gaps 1–8), `37356/65536` (gap 9), and `14826/65536` (gap 10). The diagonal is rounded downward to `116142/65536`; evaluating all eleven rows gives the sharper row budget `57430/65536`. The doubled one-sided budget `114860/65536` also retains margin `641/32768`, but is not used for the strongest theorem. All 55 mixed pairs remain included. The integer certificate uses trusted `decide`, not `native_decide`.

The local integer certificate has been checked separately using the official pinned Lean frontend. The complete actual-form theorem passed at exact head `edac34b902d8deba6810a61a0e1816506369d9cc` in run `38627745660`, job `116071121734`; later source changes need their own replay. These bounds apply to the stated eleven-translate domain; they do not assert the universal mixed-defect budget.

The exact rational counterpart `actual_eleven_lattice_coercive` gives the source SOS margin `106083/118400` on the same genuine analytic family. It reuses all derived analytic diagonals and mixed terms, and evaluates the actual row maximum `1621/1850` through the existing `gram_re_le` theorem. This exact rational declaration passed in that same exact-head replay.


## Retained geometry and sub-log-2 prime exclusion

`RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support`
returns the constructed centers and each atom's actual support containment at
radius 1/256, along with the existing moments, diagonal estimates, reconstruction
and full mixed Gram identity. The original public theorem is recovered by
projection. No partition or support certificate is supplied by its caller.

`RHActualMixedDefectV1.integer_log_avoids_below_log_two` proves that every
positive integer logarithm misses the fine correlation window when
`1/128 < b-a < log(2)-1/128`: for m=1 the logarithm is zero; for m>=2,
log(m)>=log(2). Thus `distinct_fine_prime_zero_below_log_two` proves the
entire actual von Mangoldt series zero. `distinct_fine_actual_B_below_log_two`
then retains the exact moment-zero Archimedean bound on the actual Weil B.
These are source candidates until their new exact-head replay is observed.

The graph exporter includes these constructions and the signed prime/Arch
row consumers. The constructed general partition does not assert that all
center gaps lie in a prime-free interval or in the far-spaced row domain.
The explicit next analytic obligation is to bound the full actual mixed
contribution for a suitable constructed family, including pairs whose
correlation windows meet genuine prime logarithms and near/overlapping pairs.
The narrow and nine-window sign theorems and the far Arch row theorem retain
their proven domains; no global sign is inferred from these interval results.
