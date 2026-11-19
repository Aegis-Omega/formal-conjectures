# Corrected compression: a pointwise transport obstruction

This continues the exact full-Weil defect derived in
`obstruction_transport_20261101/SPECIFICATION_AND_RH_MAP.md`. No new
independent certificate engine, numerical digamma approximation, or RH proof
is introduced. The argument below is ordinary analysis, with executable
exact-rational checks of its scalar consequences. It is not a Lean proof
of the digamma estimate or of the full Weil integral.

## Actual source symbol

Keep the exact source
`RHKreinZetaBridgeV3.ScertM M t`, with fixed finite M:

    S_M(t)=Re digamma(1/4+i t/2)-log(pi)
          -sum_(n<M) ppw(n) cos(t log(n+1)),
    ppw(n)=2 Lambda(n+1)/sqrt(n+1)>=0.

Every support-relevant prime power is retained. The finite cosine sum is
bounded in absolute value by A_M=sum_(n<M) ppw(n). The deliberately coarse
bound A_M<=M(M+1) follows from Lambda(m)<=log m<=m and sqrt(m)>=1.

For corrected compression `L_s f(x)=f(sx)`, s>1, write

    F_s(u)=(1/s)*((s²u²+1/4)/(u²+1/4))²,
    Delta_(s,M)(u)=F_s(u) S_M(su)-S_M(u).

The earlier spectral identity identifies the full-form change with the
integral of Delta against the actual nonnegative Fourier density, subject
to both moments and a common support-valid cutoff. The present test asks
whether the stronger *pointwise* domination Delta<=0 could prove that sign.

## A source-series derivation of logarithmic growth

`CvSDigammaSeriesV1.hplus_eq_tsum` and
`RHKreinDigammaLowerBoundV1.quarterTerm_eq_seriesTerm_re` provide the actual
quarter-line series. Set a=1/4, b=t/2, and

    f_t(x)=1/(x+1)-(x+a)/((x+a)²+b²).

Then Re digamma(a+ib)=-gamma+sum_(n>=0) f_t(n). For fixed t, both the sum
and improper integral converge absolutely, and direct integration gives

    integral_(0,infinity) f_t(x) dx = (1/2)log(a²+b²).

The standard unit-cell FTC estimate gives

    |sum f_t(n)-integral f_t| <= integral |f_t'|.

For b>=1>a, the variation of 1/(x+1) is 1. The function
q(x)=(x+a)/((x+a)²+b²) increases from q(0) to 1/(2b), then decreases to
zero, so its variation is 1/b-q(0)<=1/b. Therefore

    |Re digamma(1/4+it/2)+gamma-(1/2)log(1/16+t²/4)| <= 2,
    t>=2.

The source's `RHEulerGammaV13.gamma_lt` and `lt_gamma` imply 0<gamma<1.
Using 0<log2<1 and log(pi)<2, the preceding estimate implies the convenient
coarse bounds

    log(t)-4 <= Re digamma(1/4+it/2) <= log(t)+2,
    log(t)-6-A_M <= S_M(t) <= log(t)+2+A_M, t>=2.

In particular, for every *fixed* finite M,

    S_M(t)/log(t) -> 1 as t->infinity.

No limit with M=M(t) is taken. The finite prime-power sum is bounded, not
discarded. This avoids importing an unproved complex-digamma asymptotic
claim: the growth follows from the existing exact source series plus the
displayed ordinary sum-integral argument. Kernel formalization remains OPEN.

## Positive high-frequency defect

For fixed s>1, F_s(u)->s³. Thus

    Delta_(s,M)(u)/log(u) -> s³-1>0.

Consequently the pointwise condition Delta<=0 fails at all sufficiently
large positive u, for every fixed finite M.

A concrete scalar enclosure uses s=2, M=3, and u=2^64. For u>=1,
F_2(u)>=289/50. The amplitude bound is A_3<=12; hence

    S_3(2u)>=log(u)-18, S_3(u)<=log(u)+14.

Since log(2)>1/2, log(u)>32 and S_3(2u)>0. Therefore

    Delta_(2,3)(2^64)
      >=(289/50-1)*32-(289/50)*18-14
      =873/25>0.

The executable reuses the existing exact rational logarithm backend to check
log2>1/2, the multiplier comparison, and the final strict positivity. Its
stronger rational log bound is also stored. It also checks
log4>11/8: M=3 is a valid common source cutoff for packets in that width.
The analytic enclosure itself is established by the written argument above,
not inferred by testing the point 2^64.

## Constant amplitude normalization cannot repair the pointwise route

Allow arbitrary real or complex constant amplitude c; put C=|c|²>=0. Suppose

    C F_s(u) S_M(su) <= S_M(u) for every real u.

At zero, F_s(0)=1/s and S_M(0)<0. To see the latter directly from the same
series, each quarterTerm(0,n)=1/(n+1)-1/(n+1/4) is negative and the n=0
term is -3. Also gamma>=0, log(pi)>0, and ppw>=0. The zero-frequency
inequality therefore requires

    C>=s.

At positive infinity, division by log(u) and the preceding limit requires

    C s³<=1, equivalently C<=s^-3.

These are incompatible when s>1. Even a scalar renormalization of corrected
compression cannot satisfy this global pointwise symbol comparison.

## Stronger obstruction: no nonnegative frequency-dependent weight

The same actual symbol supports a stronger ordinary theorem:

    For fixed finite M and s>1, there is u>0 with
    S_M(u)<0 and S_M(su)>=0.
    Consequently no function w:R->R with w(u)>=0 everywhere can satisfy
    w(u) S_M(su)<=S_M(u) for every real u.

Here is a negative-witness transport proof. The actual digamma symbol is
continuous on the quarter line; its argument has strictly positive real
part and meets none of the digamma poles. The finite cosine sum preserves
continuity. Since S_M(0)<0, continuity supplies u0>0 with S_M(u0)<0.

The coarse source-series bound proves S_M(t)>0 for every sufficiently
large positive t. Since s>1, the geometric sequence s^n*u0 tends to
positive infinity. Therefore some term has nonnegative symbol. Choose the
least such index j. It satisfies j>=1, and

    S_M(s^(j-1)*u0)<0, S_M(s^j*u0)>=0.

Set u=s^(j-1)*u0. At this frequency, for ANY nonnegative weight w,

    w(u) S_M(su)>=0>S_M(u),

which contradicts the proposed pointwise comparison. Equivalently, that
comparison would force every negative witness to remain negative under
each multiplication by s, contradicting eventual positivity. This proof
does not assume monotonicity of S_M, and keeps all finite prime powers.

The statement applies in particular to the nonnegative weight
`w(u)=|c(u)|² F_s(u)` for arbitrary frequency-dependent amplitudes. Such a
pointwise multiplier cannot repair the attempted universal order. No
claim is made that an arbitrary multiplier preserves compact support or
the moment-zero carrier; the impossibility already holds in this larger
class, so it applies to any admissible subclass.

This strengthening is NEW ORDINARY RESULT in this checkpoint, with no
historical-originality claim. It is not a new kernel theorem. The scalar
Lean file formalizes only the earlier incompatible zero/tail inequalities.

This is a precise rejection of one proposed sufficient proof route, not a
rejection of corrected scaling itself or of RH. A signed pointwise defect
can still integrate to the desired value on a restricted family of actual
packet densities. No density/concentration argument transferring the
pointwise obstruction to a full-form counterexample has been proved here.

## Status

VERIFIED by ordinary derivation and exact scalar checks: the stated
pointwise obstruction, including the no-constant-normalization consequence.
VERIFIED by the ordinary continuity/geometric-iteration proof: impossibility
for every nonnegative frequency-dependent weight. The finite scalar script
does not by itself establish that general theorem.

OPEN: a complete kernel formalization of the sum-integral bound, the actual
spectral transport, and the weaker density-weighted integral sign question.

UNKNOWN: historical originality. This uses established series comparison,
quadratic forms and scaling mathematics; no novelty is claimed.
