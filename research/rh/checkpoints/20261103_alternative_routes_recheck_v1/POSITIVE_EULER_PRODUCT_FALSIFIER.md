# Positive Euler weights still require the exact zeta normalization

Complete ordinary construction, not a counterexample to RH for zeta.
This tests a third candidate producer after the generic Hadamard and
positive-Mellin-kernel tests. It retains a convergent Euler product with
strictly positive prime-power logarithmic-derivative coefficients and
identifies EXACTLY which additional zeta-specific data it does not retain.
The construction does not assume RH or any individual zero on the line.

Let xi denote the actual completed Riemann function

    xi(s)=(1/2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s).

Use its already established entire continuation, real conjugation,
functional equation, order at most one, and location of its zeros in the
strict strip. These are ordinary established inputs, not a premise that
the zeros lie on the line. Define the NEW TEST FUNCTION

    F(s)=xi(s)*xi(2s-1/4)*xi(2s-3/4).

This is not substituted for the canonical target or for Mathlib zeta.
It is entire of order at most one, real under conjugation, and
F(1-s)=F(s): reflection swaps the last two factors and reflects the first.
Its zeros all lie strictly between real parts0 and1. Indeed each
nontrivial xi zero rho=beta+i*gamma, 0<beta<1, yields possible zeros

    rho,
    (rho+1/4)/2, real part in (1/8,5/8),
    (rho+3/4)/2, real part in (3/8,7/8),

and a finite product has no other zeros. For ANY such rho the last two
real parts differ by1/4. They cannot both equal1/2. Thus F has an off-line
zero without assuming the truth or falsehood of RH for xi.

Existence of at least one xi zero can be recovered without a new Hardy
input. A zero-free entire xi of order at most one would, by the existing
Hadamard factorization, be exp(A+B*s). Its functional equation forces
B=0: differentiation at s=1/2 gives a zero derivative, while the
exponential never vanishes. But xi(2)=pi/6 and xi(4)=pi^2/15 are unequal,
using the classical zeta(2),zeta(4),Gamma(1),Gamma(2) values and pi>5/2.
Hence xi is nonconstant and not zero-free. This applies the existing
Hadamard mechanism instead of silently presupposing a critical-line zero.

## Arithmetic product and its proven domain

The underlying meromorphic Euler-product function is

    L(s)=zeta(s)*zeta(2s-1/4)*zeta(2s-3/4).

For Re s>1 all three Euler products converge absolutely. Only in that
domain do we differentiate and rearrange their logarithmic series:

    -L'(s)/L(s)
      =sum_(m>=2) Lambda(m)*m^(-s)
       +2 sum_(n>=2) Lambda(n)*(n^(1/4)+n^(3/4))*n^(-2s)
      =sum_(m>=2) a_m*m^(-s),

    a_m=Lambda(m)
          +1_(m is a square)*2*Lambda(sqrt m)*(m^(1/8)+m^(3/8)).

Here Lambda vanishes outside integer prime powers. Every a_m is
nonnegative, and a_(p^k)>0 for every prime power p^k, including k=1.
Absolute convergence follows directly from the three standard
von-Mangoldt Dirichlet series: the shifted arguments have real parts
>7/4 and >5/4 when Re s>1. No Euler-product manipulation in the unknown
critical region is used. Analytic continuation comes separately from
the actual zeta/xi factors, not from convergence of those series there.

## Exact point where this is different from zeta

The coefficients are NOT the exact target Lambda(m). The meromorphic
L(s) has additional poles at s=5/8 and s=7/8, from the shifted zeta
factors. The other factors do not cancel them: their relevant real
arguments are respectively 5/8 and1/2, or7/8 and3/2, and zeta has no
real zero on (0,1) or (1,infinity). The first statement follows from
the positive alternating eta series divided by 1-2^(1-s)<0 on (0,1).
The completed F cancels these poles by its explicit polynomial factors.

Its gamma factors are also different:

    Gamma(s/2)*Gamma(s-1/8)*Gamma(s-3/8),

with the accompanying pi factor pi^(-(5s-1)/2) and the product of the
three explicit quadratic completion factors. It is not the single
Gamma(s/2) completion with only the actual zeta pole data. Its local
quadratic Euler factors also fail the normalized Satake/Ramanujan bound;
no Selberg-class or standard-conductor membership is asserted.

Therefore this does not disprove RH for zeta or a valid argument using
its exact prime coefficients, gamma factors and poles. It disproves a
proposed generic route that discards those exact identities and retains
only positivity of prime-power weights plus symmetry and finite order.

This matters for cross-route composition: replacing the actual signed
arithmetic object by a positive surrogate measure or invoking Euler
positivity without preserving its exact normalization would incorrectly
accept this test function as well. The counterexample is fully analytic,
not a finite numerical observation, and it does not declare the actual
Li, Suzuki, Weil or another AEGIS route exhausted.

No Lean port of this construction is claimed. The preserved canonical
RiemannHypothesis target remains unchanged; rh_proven=false.
