# Refinement forces an actual packet-family margin to decay

Complete ordinary proof; no RH assumption and no numerical premise.
This tests the strategy of overcoming every mixed term by making an exact
local decomposition finer. Existing local moment inverses and packet
decompositions are reused, rather than reproved or declared missing.

## Precise statement

Fix a nonzero compactly supported smooth potential Psi on the logarithmic
line, put D0=1/4-D^2, and H=D0 Psi. Consider ANY finite exact decomposition

    H=sum_i H_i, H_i=D0 Psi_i,

where each smooth compact potential Psi_i is supported in an interval of
FULL length at most 2*delta, delta>0. Suppose at almost every point at
most m of these intervals occur, with integer m>=1. Then

    sum_i ||H_i||_2^2 >= 3/(4*m*delta^4) * ||Psi||_2^2.                 (1)

In particular, if the COMPLETE actual Weil form satisfies a family margin

    Q(H)>=eta*sum_i ||H_i||_2^2, eta>=0,

then necessarily

    eta <= [4*m*Q(H)/(3*||Psi||_2^2)]*delta^4.                        (2)

The conclusion concerns a fixed input H and all such decompositions,
including complex coefficients absorbed into H_i. It is not an assertion
that Q(H)>=0 without the displayed margin premise.

If m is fixed, no strictly positive eta independent of delta can work on
arbitrarily fine exact reconstructions of this same nonzero H. This
remains true on a window whose positivity is already proved: Q(H) is
finite and fixed, whereas the total local energy in (1) diverges.

## Proof with an elementary explicit constant

First, the potential reconstruction is automatic. If
Z=sum_i Psi_i-Psi, then D0 Z=0. Integration by parts yields

    0=<D0 Z,Z>=(1/4)||Z||_2^2+||Z'||_2^2,

so Z=0. No spectral completeness or RH is used.

For a single smooth potential p supported in [b,b+ell], its value and
first derivative vanish at b. Zero summands can be removed; a nonzero
smooth summand has ell>0. Hence

    p(x)=integral_b^x (x-t)p''(t) dt.

Cauchy--Schwarz, followed by integration over x, gives

    ||p||_2^2 <= ell^4/12 * ||p''||_2^2.

The factor is exact: integral_b^(b+ell) (x-b)^3/3 dx=ell^4/12.
The proof is valid for complex p as well. A second integration by parts
gives the exact moment-killer energy identity

    ||D0 p||_2^2
       =||p''||_2^2+(1/2)||p'||_2^2+(1/16)||p||_2^2
       >=12/ell^4 * ||p||_2^2
       >=3/(4*delta^4) * ||p||_2^2.

At almost every point, bounded overlap and Cauchy--Schwarz give

    |Psi(x)|^2=|sum_i Psi_i(x)|^2 <=m*sum_i |Psi_i(x)|^2.

There are only finitely many summands, so integration and summation
commute without a limiting argument. Summing the single-potential
estimate proves (1). Since eta>=0, multiply (1) by eta and use the
displayed family margin, then divide by the strictly positive
3||Psi||_2^2/(4m delta^4), to obtain (2).

The potential norm is positive because H!=0. Conversely D0 is injective
on compact potentials by the same energy identity, so nonzero Psi also
ensures H!=0. Thus no zero-object substitution or division by zero occurs.

## Independent analytic check and sharper constant

Dirichlet Poincare on an interval of length ell gives
||p'||_2^2>=(pi/ell)^2||p||_2^2. For smooth compact p this follows by
expanding in the sine basis: Parseval diagonalizes the derivative energy,
and every nonzero sine frequency is at least pi/ell. Applying this to

    <D0 p,p>=(1/4)||p||_2^2+||p'||_2^2

and using Cauchy--Schwarz proves

    ||D0 p||_2 >=[1/4+pi^2/ell^2]||p||_2.

This yields the stronger estimate

    sum_i ||H_i||_2^2
       >=(1/m)*[1/4+pi^2/(4delta^2)]^2 * ||Psi||_2^2,

and hence eta<=m Q(H)/([1/4+pi^2/(4delta^2)]^2||Psi||_2^2).
It independently confirms the delta^4 decay, with a stronger constant.
This is a second mathematical derivation, not a claim of a second agent
or a fresh formal kernel replay.

## Connection to the actual source and its limits

The existing compact moment-killer inverse supplies a potential inside
the same logarithmic interval for each legal local packet. Thus the
statement applies to actual locally moment-zero decompositions, not only
to an abstract chosen basis. The inverse is linear and compactly
supported; the injectivity proof above shows that the potentials sum
to the fixed inverse of H whenever the actual packets sum to H.

For the source lift H(x)=exp(x/2)*g(exp x), the change of variables y=exp x
gives ||H||_2^2=integral |g(y)|^2 dy, exactly the physical source energy.
FULL local length is 2delta. No half-width/full-width or Fourier 2pi
normalization is changed in (1) or (2). Every pole and prime term remains
inside Q(H); its finiteness follows from the fixed compact smooth input.

This is stronger than saying that an arbitrary decomposition may contain
h and -h: it controls every bounded-overlap decomposition at the stated
scale, including an optimized selector. It does not refute the existing
conditional Schur consumer, which remains a correct implication under
its stated hypotheses. Nor does it refute a selector at one fixed scale,
one with overlap m growing at least as fast as needed, or a semidefinite
argument with a scale-dependent margin tending to zero.

In particular local diagonal margins that grow like log(1/delta) do not
justify a fixed positive TOTAL family margin after reconstruction. The
true mixed terms must cancel almost all that large local energy. A
refinement-based global proof must retain those signed cancellations
with the precision quantified above. Dropping them or giving them a
constant row allowance cannot be justified by narrowness alone.

The all-radius actual Schur-sign producer remains open. This result
rejects a specific uniform-coercivity strategy, not RH, and introduces
no new RH equivalence.
