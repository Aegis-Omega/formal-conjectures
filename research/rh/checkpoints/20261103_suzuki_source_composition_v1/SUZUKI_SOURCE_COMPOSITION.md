# Suzuki continuation: primary-source composition and normalization

Date: 2026-11-03. RH remains unproved in this checkpoint. This file
preserves existing theorems; it does not add or formalize another RH
equivalence. No novelty is claimed for identities already implicit in
the cited sources. There is no new Lean RH proof term.

## Exact sources actually read

1. M. Suzuki, *Aspects of the screw function corresponding to the
   Riemann zeta-function*, arXiv:2206.03682v4, version header 30 May
   2023 and manuscript date 31 May 2023.
   The raw PDF is 433447 bytes, SHA-256
   `eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41`.
   Read: (1.1), Theorem 1.1, Section 3.3, Section 4.1, Sections 7.1-7.2,
   Theorems 8.1-8.2 and Section 11. Whole-paper semantic review is not
   claimed. A separately fetched HTML extraction displays a different
   date; its bytes are not assigned the PDF hash.
2. M. Suzuki, *Weil's quadratic form via the screw function*,
   arXiv:2606.09096v3, September 2026. Raw PDF 491037 bytes, SHA-256
   `75b8512f7081bd69152781c7a20f3b5dad4374fe0dfc80f3014f9223f044c81a`.
   Read: introduction, Theorems 1.1, 1.3-1.5, Corollaries 1.2 and 1.6,
   (2.5)-(2.8), and relevant assumptions in Section 7. Other sections
   are not independently verified by this audit.

Only the bibliographic identities, own analysis and checker are
published here. Full papers and private Drive handoffs are not included.

## Existing composition retained

The 2023 paper's Proposition 3.1 already identifies the derivative
transport of the actual screw-kernel form with the actual Weil form.
Its Theorems 1.7 and 11.1 already provide the scalar-sign criterion;
their proofs need not be redone. The 2026 paper's Theorem 1.1 identifies
the Friedrichs extension, and Corollary 1.2 supplies a smooth form core.
These are literature results under their stated hypotheses, not new
Lean kernel replays in this continuation.

The existing Claude/AEGIS angular Fourier convention is
`vhat(xi)=integral v(x) exp(-i xi*x) dx`, with multiplier

    Re digamma(1/4+i*xi/2)-log(pi).

Its full form also contains every prime-power correlation and the
polar contribution `2 Re(M_+ conjugate(M_-))`. On the two-moment legal
class the latter vanishes by a proved moment identity. This matches
the explicit formula in the corrected September 2026 source. A theorem
about the unrestricted closed form cannot be silently replaced by its
restriction to the two-moment class, nor conversely.

The Fourier sign that an August 2026 external report criticizes in v1
is already negative in (2.7) of the retrieved v3. It must not be
reported as a newly found defect of v3. The external report's claimed
bounded-support certificate is not independently replayed here and
is not an all-radius producer.

## An actual discrepancy in the older printed derivative

Write `psi=Gamma'/Gamma`, `x=exp(-t/2)` and `0<t<log(2)`.
There is no prime contribution in (1.1). The Lerch term is

    (1/4) sum_(j>=0) [1-exp(-(2j+1/2)t)]/(j+1/4)^2.

On every compact subinterval of t>0, the differentiated series and
each of its derivatives converge uniformly, by geometric domination.
Consequently its first derivative is

    2 sum_(j>=0) x^(4j+1)/(4j+1) = atanh(x)+atan(x).

Using `psi(1/4)=-gamma-pi/2-3 log(2)` gives the derivative of (1.1):

    Psi'(t)=2(exp(t/2)-exp(-t/2))
      +pi/4-(gamma+3 log(2)+log(pi))/2
      -atan(exp(t/2))+atanh(exp(-t/2)).

The literal constant printed in Section 4.1 omits `-log(pi)/2`.
Thus the printed expression exceeds the correct derivative by exactly
`log(pi)/2`, not by an error that can be absorbed into rounding.
This observation does not refute the theorem's conclusion or any
independent proof of local positivity. Its numerical critical points
must be interpreted using the correct derivative.

The enclosed checker compares the closed derivative with its
independently summed positive geometric/Lerch derivative, at three
exact rational points. For N terms the omitted tail is at most

    2*x^(4N+1)/((4N+1)*(1-x^4)).

At t=1/3 the correct derivative is strictly negative and the printed
expression strictly positive. The receipt uses 300-bit Arb outward
balls. This is a numerical cross-check of the written identity, not
a Lean theorem, an independent foundational checker, or an RH proof.

## Two concrete composition attempts and their exact stopping points

### Spectral realization

Theorem 1.5 (2026) really is unconditional: for each a>0 choose
`lambda<lambda_a`, set `T_a=A_a-lambda I`, and form the characteristic
function W(a,lambda,theta;z). Its zeros are real. This result is
retained and must not be reopened as an unproved theorem.

Applying Corollary 1.6, however, requires a specified choice of lambda,
theta and an analytic gauge, together with locally uniform upper-half-
plane convergence to `xi/(xi+xi')` at `1/2-i*z`. The source does not
prove this unconditional limit. Its Section 7 explicitly studies
`A_infinity>0`, and the introduction warns that the expected choice
`lambda=0` for all sufficiently large a is RH-equivalent. Choosing a
negative spectral shift to create a Hilbert norm does not discharge
that limit. This is the precise failed composition, not a claim that
the unconditional finite-a spectral theorem is false.

### Arithmetic shift transport

Section 11 (2023) proves unconditional positivity of Psi_omega for
omega>=1/2. The displayed transform T_eta satisfies

    (T_eta f)(t)=exp(-eta*t)f(t)
       +2eta integral_0^t exp(-eta*u)f(u) du
       +eta^2 integral_0^t (t-u)exp(-eta*u)f(u) du.

For eta>0 this preserves nonnegativity. The reverse step uses
eta<0 and has a negative integral coefficient. Reading and composing
the exact formula therefore does not produce the sign of the actual
Psi_0. No claim is made that the actual reverse image is negative;
that is precisely the sign to prove. The existing unconditional
PNT-scale estimate in Theorem 1.1(3) also permits growth
`exp(t/2-c*sqrt(t))` and supplies neither boundedness nor a sign.
Previously recorded losses of this same exponential scale are not
new failures and are not reconstructed here.

## One selected remaining mathematical producer, not a universal bottleneck

On this scalar Suzuki route, the exact producer still not supplied by
the inspected compositions is:

    exists T>0, forall real t>=T, Psi_0(t)>=0,

where Psi_0 is exactly (1.1), with all prime powers, the Lerch term,
the polar term and the constant `-log(pi)` retained. Its implication
to RH is already Theorem 11.1; no new equivalence is requested.
No unconditional proof of this producer has been found in the
reviewed sources. This is not a nonexistence statement about unreviewed
AEGIS sources, and Schur is not asserted to be the only possible route.

The named old `SUZUKI_SCREW_PRIMARY_EXTRACT` has not been located in
the recovered 941-tip source index or the targeted Drive search.
Those searches are not an exhaustive historical or prior-session
audit. Private handoffs were read locally and are not republished.

The next mathematical action is to find or prove a genuinely signed
arithmetic estimate for this actual Psi_0. More finite cells, a
negative spectral shift, a positive finite trial minimum, or another
RH equivalence do not supply it. No proof of that estimate is claimed
by the derivative correction above.
