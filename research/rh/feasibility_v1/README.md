# Universal RH route feasibility pilots

These are scoped research results. They do not prove RH or construct an
unconditional all-window certificate. The canonical Mathlib statement and
the official open-problem catalog are unchanged.

The baseline is PR #89 at `da0103e7afa0bb0ade1441f87d01e1b9416ef9c4`,
with the existing Feshbach branch at `9f6abc070b833df36e7fc7476ed306c9fef5ab14`.
The residual-transfer extension at `251b6636b1764f5bf243f59807ffc5ebed8ed782`
passed all three jobs of run
[39243519309](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39243519309).
That run does not certify later changes in this directory.

## Discoveries and countertests

* `CvSRowTailV1.exists_uniform_rows_tail_cutoff` composes the existing actual
  CvS row bound with its order-zero formula. For fixed `M`, `L > 0`, frequency
  radius `R`, and tolerance, one cutoff controls every later cutoff, every
  finite frequency subset of that radius, every complex coefficient vector,
  and every outer partial sum. The error is relative to squared coefficient
  **l1** mass. This is an actual-row truncation result, not a stable l2
  operator estimate as the window and dimension grow.
* `SignedCliqueObstruction.lean` proves that an `(n+1)`-clique of absolute
  costs at least `d` forces any common positive-weight Schur row ceiling `S`
  to satisfy `n*d <= S`. It also proves the exact Q16 implication and a
  negative rank-one signed-form identity. This rejects an overstrong
  all-decomposition admission rule; it does not refute existential `hselect`
  or the actual universal signed budget.
* `ReciprocalPairObstruction.lean` proves `2-(w+w^-1)<0` for positive real
  `w != 1`. This is an algebraic countertest to a symmetry-only positivity
  argument. It asserts no actual off-critical zeta zero and no sign theorem
  for general complex Li factors.

The standalone pilot proofs were compiled in pinned Lean 4.33.1 and
independently replayed before integration. Each printed axiom set contains
only `propext`, `Classical.choice`, and `Quot.sound`. Actual CvS import
integration and all new roots are checked by the existing Feshbach workflow
on the commit containing these changes; its result must be read separately.

## Exact universal obligations

**A: Cofinal windows.** The existing
`RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families` consumes
an actual `PacketSchurFamily` for every relevant moment-zero packet in every
positive `n*pi` window. Compact-support exhaustion and the cofinal limiting
argument are already proved. A fixed local window does not supply the
family constructor. The strict consolidated `L < 21/40` range also does not
include its endpoint by set union alone.

**B: Feshbach.** The closest fixed-window consumer is
`CvSRowTailV1.window_of_certificate_tail`. It still requires `hcert`, the
trace/slack estimate and positive complement gap, `hfin` for finite cross
rows plus the tail, and `hlow` for actual low-block dominance for every
coefficient vector. The new cutoff can reduce the tail term but cannot
replace the Schur inequality. A positive low block and positive complement
can have an indefinite full matrix: `[[1,2],[2,1]]` at `(1,-1)` is negative.

**C: Signed budget.** The existing
`RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget` requires
each moment-zero packet to have a finite actual reconstruction satisfying
`actualMixedDefect <= -sum(diagonal)`. Its exact recomposition identity makes
this equivalent to the source packet's actual Weil sign. No unconditional
cancellation inequality for every source packet was obtained. The existing
sharp `4 log 3` family has dimension-independent margin `20829/16384` but a
mother support radius that shrinks with the lattice horizon; it is not an
arbitrary-packet producer.

**D: Alternatives.** The Li bridge requires nonnegativity of all true Li
coefficients; spectral transport unit modulus is RH-equivalent; the dense
two/three detector sign is explicitly RH-equivalent; critical-strip and
exterior zero-free results do not exclude off-critical interior zeros.
Complementary Mellin mothers still need actual realization, density in the
topology controlling the actual Weil form, and cross-mother signed bounds.

## Feasibility decision

No route is promoted to universal closure. Continue focused work on B's
actual-row/Schur estimates and C's signed cancellation; hold A's global
producer and D's unsupported spectral/Li closures. In particular, the
executive Gate 2 is not passed for a complete RH proof route. The next
required mathematical result is an actual producer with controlled
complement and Schur bounds as the required windows grow. This conclusion
comes from missing estimates and quantified source interfaces, not from a
failed local import or finite numerical extrapolation.

## H140

The original Claude source `CvSPackedGramV1.lean`, generator, H140 data, and
14-theorem audit remain inaccessible. User screenshots identify H140 as a
Hilbert demonstration, not the actual CvS matrix. The recovery report in
`../feshbach_lean_v1/H140_RECOVERY_REPORT.md` preserves that distinction.
No original certificate bytes or margins have been invented.
