# A genuine function-approximation producer on expanding actual CvS spaces

Status: new ordinary reconstruction and proof by the primary agent, not a
recovered historical proof or a freshly kernel-checked analytic theorem.
Existing compact D0 inversion and `CvSAtomInversionV1.atom_sum` are reused.
No RH or global sign assumption is made. The input is the actual smooth
compact two-exponential-moment class, not a redefined zeta or zero predicate.

## 1. Why the searched approximation criteria do not already supply this

The read `RHCertifiedApproximationV1.lean` asks for convergence of scalar
arithmetic VALUES along certified dyadic packets. It does not prove function
convergence. Its read companion `RHCertifiedApproximationTrivialityV1.lean`
already proves, under its negative witness, that this scalar condition has
the full universal sign content. That observation is reused, not reproved.

The fixed139 `UniversalActualCvSLowBlockApproximation` has the same
scalar-value limitation. The construction below uses increasing actual
CvS dimension and proves convergence of the FUNCTIONS in the logarithmic
form norm, and of their complete arithmetic values. It does not construct
the different fixed139 scalar producer or a certified sign sequence.

## 2. Fixed operators and explicit finite spaces

Use D0=D²-1/4. Let H in Cc-infinity(R;C) have both exponential moments zero.
The existing compact-inverse theorem supplies a unique compact smooth phi
with D0 phi=H, retaining the convex hull of support. The inverse is linear.
For example its ordinary Green formula is

    phi(x)=-integral exp(-|x-y|/2)H(y)dy.

The two moments make the two exterior exponential tails exactly zero;
the existing factor theorem supplies precisely this compact-support inverse.

Fix ONCE a smooth real chi supported in(-3/4,3/4), equal1 on[-1/2,1/2].
For each INTEGER R>=1 let

    E_R(x)=cos²(pi x/(2R)),
    F_R(x)=chi(x/R)phi(x),
    T_R(x)=F_R(x)/E_R(x) on(-R,R), zero near its endpoints,
    K_R=3^(R²).

There is no singular division: the numerator is identically zero outside
[-3R/4,3R/4], where the envelope is uniformly bounded away from zero.
T_R extends to a smooth2R-periodic function. Let S_(R,K) be its Fourier
partial sum through modes -K,...,K, with coefficients

    t_(R,k)=(1/(2R)) integral_[-R,R] T_R(x)exp(-i pi kx/R)dx.

Define, inside[-R,R] and zero outside,

    H_R=D0[E_R S_(R,K_R)].

This is an EXACT finite sum of the actual centered/phase-corrected source
CvS atoms V_k at L=2R, |k|<=K_R. It is not an arbitrary PSD matrix.
The potential and its first derivative vanish at BOTH endpoints. Thus
H_R has the two exact exponential moments, even though H_R may jump at
the endpoints. It belongs to the logarithmic Fourier form domain X.
All maps H->phi->F_R->T_R->S->H_R are linear. Consequently

    QR_R(H):=Q(H_R)

is a genuine finite-rank quadratic family on the original legal smooth
space. Finite rank and linearity are not assumed from a name.

## 3. Explicit error estimate in the needed norm

Fix H for the convergence argument; constants below may depend on H.
Choose R0 so phi is supported in[-R0,R0]. For R>=2R0, F_R=phi. On that
fixed support E_R>=1/2, and all derivatives through any fixed order of
1/E_R are uniformly bounded for these R. Thus

    ||T_R^(8)||_1 <= C_H

uniformly in all sufficiently large integers R. Repeated integration by
parts has no boundary term because T_R vanishes near the period endpoints.
For k!=0,

    |t_(R,k)| <= C_H R^7 |k|^-8.

The standard absolutely convergent Fourier reconstruction, including its
first three derivatives, therefore gives for m=0,1,2,3,

    ||(T_R-S_(R,K))^(m)||_infinity
       <= C_H R^(7-m) K^(m-7).

One obtains reconstruction, for example, from uniform Fejer convergence
and uniqueness of Fourier coefficients, after noting absolute convergence
of the differentiated series. Only a smooth periodic function is used.

Let u_R=H_R-H. On[-R,R], apply D0 to E_R times the Fourier error. Envelope
derivatives are uniformly bounded for R>=1. With K=K_R>=1 this yields

    ||u_R||_infinity+||u'_R||_infinity <= C_H R^7 K_R^-4.

Here the derivative is the classical interior derivative. The zero-extended
error can have endpoint jumps, which must be paid separately. Set

    A_R=2R||u_R||_infinity,
    B_R=|u_R(-R)|+|u_R(R)|+2R||u'_R||_infinity.

Then A_R+B_R<=C_H R^8 K_R^-4. Direct Fourier estimation and one integration
by parts give

    |uhat_R(t)|<=A_R,
    |uhat_R(t)|<=B_R/|t| for t!=0.

Splitting the logarithmic form norm at |t|=1,

    integral log(2+|t|)|uhat_R(t)|²dt
       <= C(A_R²+B_R²)
       <= C_H R^16 K_R^-8 ->0.

The constants in the two frequency integrals are finite because
integral_1^infinity log(2+t)/t² dt is finite. Also
||u_R||_2<=C_H R^(15/2)K_R^-4. This proves actual function convergence in
X and in L², with endpoint jumps and frequency tails explicitly controlled.
It is pointwise in H; no universal norm bound on all H is asserted.

## 4. Pay the growing prime operator, rather than assume global continuity

Form-norm convergence alone on EXPANDING supports does not automatically
give convergence of the full prime term. Both H and H_R are eventually
supported[-R,R]. The full prime-shift operator there has norm at most

    P_R=2sum_(2<=m<=exp(2R)) Lambda(m)/sqrt(m) <=8R exp(R).

Consequently their prime quadratic values differ in absolute value by at
most

    P_R ||u_R||_2 (||H_R||_2+||H||_2)
       <=C_H R^9 exp(R) K_R^-4 ->0.

For the chosen K_R=3^(R²), the factor exp(R) is genuinely dominated.
There is no appeal to PNT cancellation, RH, or an unjustified support-
independent continuity constant. Merely choosing a slowly increasing
degree and ignoring this factor would not close this proof.

The Archimedean quadratic values converge by the X-norm estimate and
|w(t)|<=C log(2+|t|), using Cauchy–Schwarz in the positive weighted Fourier
L² space. Both moments are exactly zero for every R, so every polar term
is exactly zero. Thus

    Q(H_R) -> Q(H)

for the COMPLETE arithmetic form. With M_R=9^R, the source finite prime
cutoff covers the entire support because exp(2R)<9^R. Therefore QR_R is
also an exact source-CvS finite quadratic at L=2R, this explicit cutoff,
and its explicit coefficient vector. No truncated spectral surrogate is
substituted for Q.

For an actual source packet g, H is its exact logarithmic lift and Q(H)
is its actual zero quadratic by the existing moment-zero explicit formula.
This gives the genuine pointwise-convergence producer in the actual
analytic carrier. Its formal Lean source/domain adapter remains to be
ported and checked. It is not a Coq term on the larger O0 continuous-only
carrier without a separate semantic transport.

## 5. What the construction does and does not close

It explicitly constructs finite actual QR_R and proves pointwise
convergence, support, exact moments, norms and growing prime-tail control.
It does NOT prove QR_R>=0, any required vanishing lower error, or global
Q>=0. Existing small-window and fixed-family certificates do not have
the quantifiers needed to provide that assertion for these expanding
windows and dimensions. No claim is made that all other sources have
been exhaustively inspected for such a producer.

The finite-to-limit theorem itself is already proved and is reused. The
remaining signed lower-bound obligation must be attacked on these actual
finite forms or on the positive-complement Schur geometry. Convergence
has not hidden or assumed that sign.
