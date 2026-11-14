# Reuse audit of PR499 and PR523 at their actual heads

PR499: Aegis-Omega/AEGIS-OMEGA, closed,
1760f4ea290035784b2cc731cded4fe0cf2df037.
Its ConcreteFiniteGuinandWeilSemanticsV1 blob is
a2fe539ea09813f4b0b38d2b4cd5149cb81ff90f, identical to the recovered
PR580/archived source. Its finite semantic bundle is preserved; the actual
body does not construct a GlobalizationReady tuple or a universal sign.

PR523: closed,8633831e652e3622e3b3d3ace6cdcbafe3d67058.
Nine Lean source/spec bodies were read and byte-verified against their Git
blobs; see SOURCE_MANIFEST.json. No fresh transitive Lean replay is claimed.

## Results actually reused

* `weil_single_frequency_source_calculus_v1`: a finite sinusoidal-source
  quadratic equals alpha times its explicit Volterra/chord kernel.
* `weil_finite_source_measure_extension_v1` and
  `weil_finite_source_full_entry_identification_v1`: exact finite
  superposition/entry identification. These do not require positive weights
  and do not claim a sign.
* `weil_arch_finite_quadratic_scaled_cauchy_v1`: the fixed nonresonant-T
  Archimedean sine-source contraction equals its nonnegative scalar times
  the finite rank-two Cauchy Gram form.
* `weil_arch_finite_quadratic_nonnegative_v1`: preserves that genuine
  fixed-T positivity for positive L, all real finite coefficients and the
  stated nonresonance hypotheses.
* `weil_arch_weighted_tail_quadratic_nonnegative_v1`: integrates this
  positivity only when the actual weight is nonnegative over the interval.
* The same PR already supplies the nonpositive-weight version, plus
  `arch_weight_real_neg_at_quarter` and
  `arch_weight_digamma_neg_at_zero`. Thus the missing global sign is not
  discharged by pretending the actual digamma weight is everywhere positive.

These are existing proofs with their exact hypotheses, not newly opened
lemmas. The integral/source normalization and full scalar/prime terms still
have to match the actual Weil object; names alone do not do this.

## A finite counterexample to a tempting stronger source claim

The chord representation is not automatically a positive Gram kernel for
every positive atomic source. At alpha=1,omega=1/2, every off-diagonal
source entry is zero because sin(pi m)=0 at integer m. The diagonal entry
is cos(pi m)=(-1)^m. Taking just u_1=1 gives quadratic value-1.

Even the discrete clamped-potential constraints do not repair this generic
claim. Let rho=1/4 (physical window L=8pi), and choose potential coefficients

    beta_0=-1/4, beta_(+/-1)=1/4, beta_(+/-2)=-1/8.

Their sum and first discrete moment are both zero. The corresponding
potential on[0,L] is sin²(pi x/L)cos(2pi x/L), with value and first
derivative zero at both endpoints. Consequently H=D0 phi has BOTH actual
exponential moments zero. Its physical Fourier coefficients are

    u_0=8/128, u_(+/-1)=-10/128, u_(+/-2)=8/128.

The one-frequency chord quadratic at omega=1/2 is therefore EXACTLY

    (8²+2*8²-2*10²)/128²=-1/2048.

This is a genuine legal finite-potential shape, but a deliberately selected
single source frequency and weight, not the complete actual zeta source.
It refutes a universal positive-source lemma; it is not a negative value of
the actual Weil form or a counterexample to RH. The actual prime mapping,
gamma weights, polar conventions and every other source atom cannot be
discarded. Existing PR523 does not make the false stronger assertion.

## Consequence for composition

The fixed-T Cauchy/Archimedean positivity is reusable on its domain.
The generic finite-source calculus identifies the signed arithmetic source
exactly. Their combination still needs the actual signed budget; the
positive theorem cannot be substituted for the different full finite
Guinand–Weil quadratic. The new moment-complement estimate pays the
negative low-frequency weight and the whole bounded prime operator on its
specified complement, while the global low/cross budget remains open.
