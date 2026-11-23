# Oscillatory actual packets disprove unnormalized compression nonincrease

Let `eta` be the original normalized real nonnegative C-infinity bump, with
support [-1,1] and eta(x)>0 for |x|<1. Let

    f_T(x)=eta(x) cos(Tx),        A=d²/dx²-1/4,
    G_T=A f_T,                   G'_T=A(f_T(2·)).

Both are real, compact smooth functions on the log line and both have the
two exponential moments equal to zero. The actual Weil test packets g_T and
g'_T are the inverse log lifts: `g(x)=x^(-1/2)G(log x)` for x>0 and zero
otherwise. They are smooth and compactly supported on the positive axis.

The source log support of G_T is exactly [-1,1]. Indeed, if A f_T vanished
on an interval immediately inside an endpoint, f_T would solve
f''=f/4 there with zero value and derivative at the endpoint, hence would
vanish on that interval by ODE uniqueness. This contradicts eta>0 and the
fact that cos(Tx) is not identically zero on any interval. The scaled
packet has support in [-1/2,1/2]. Thus the source has width 2, while the
corrected compressed packet has width at most 1<11/8.

Let Q denote the actual zero-quadratic form in
`RHKreinZetaBridgeV3.zero_quadratic_eq_scertM`, not a surrogate matrix.
Define the angular Fourier transform and the positive constant

    Φ(v)=∫ eta(x) exp(-i v x) dx,
    C=(1/(4π)) ∫ |Φ(v)|² dv = (1/2) ∫ |eta(x)|² dx > 0.

The following limits hold:

    Q(g_T)/(T⁴ log T)  → C,
    Q(g'_T)/(T⁴ log T) → 8 C,            T → +∞.

Consequently Q(g'_T)>Q(g_T)>0 for every sufficiently large T. This is an
actual smooth, moment-zero, wide-to-certified-narrow packet counterexample
to the proposed uniform unnormalized comparison Q(g)>=Q(g'). Both sides
are eventually positive: the result does not contradict RH or the 11/8
window theorem. It does not exclude a normalized or differently corrected
integral transport.

## Proof

The source identity permits the common fixed cutoff M=7 because both widths
are at most 2 and log 8>2. Indeed e<11/4 and (11/4)²=121/16<8. The actual
symbol is

    S_7(t)=Psi(t)-log π-∑_(0≤n<7) ppw(n) cos(t log(n+1)),
    ppw(n)=2 Λ(n+1)/sqrt(n+1),

which retains all prime powers required by that source theorem; the support
condition is what makes the remaining terms vanish. The previously checked
quarter-line series and sum/integral comparison in `defect_tail_20261101`
give `S_7(t)=log|t|+O(1)` as |t|→∞. S_7 is even and continuous, and
`|S_7(t)|≤C₇+log(2+|t|)` for some constant C₇ on the entire real line.

With the angular convention above, the source moment factor has multiplier
`-(t²+1/4)`, so its squared norm is W(t)=(t²+1/4)². Writing

    Φ_T(t)=[Φ(t-T)+Φ(t+T)]/2,

the existing full-form identity yields

    Q(g_T)=1/(2π) ∫ S_7(t) W(t) |Φ_T(t)|² dt,
    Q(g'_T)=1/(4π) ∫ S_7(2u) W(2u) |Φ_T(u)|² du.

The factor 1/2 in the second formula is the compression Jacobian after
combining the squared Fourier scaling and t=2u substitution. It is essential.

For the two squared lobes, shift u=±T+v. For T≥2, the normalized weight is
dominated by a constant times
`(1+|v|)^4(1+log(2+|v|))`. Because Φ is Schwartz, its product with |Φ(v)|²
is integrable. Pointwise, the source weight tends to 1, whereas the
compressed weight tends to 2⁴=16 before the 1/2 Jacobian. Dominated
convergence gives the two diagonal contributions.

After shifting u=T+v, the cross term contains
`Φ(v) conjugate(Φ(v+2T))`; it tends to zero pointwise. The same polynomial
logarithmic weight times `|Φ(v)| sup|Φ|` is integrable, so dominated
convergence makes the cross term vanish. The negative-frequency lobe is
handled separately, not discarded. This proves both displayed limits.
Plancherel supplies the expression and strict positivity of C.

The proof holds with a fixed M throughout. It assumes neither RH nor a
uniform prime-error estimate. It proves a failure of this particular
transport inequality, not failure of the desired positivity.

## Verification boundary

The asymptotic proof above is ordinary analysis; the complete theorem is not
yet a Lean kernel theorem. `OscillatoryKreinPacketsV1.lean` separately
formalizes the smoothness, compact support, both moments for source and
scaled factors, and support inclusion, using the existing Krein atom. Its
actual axiom output and command are in the accepted local Lean receipt.
The Fourier scaling, dominated convergence, exact support endpoints and
asymptotic full-form inequalities remain to be formalized in Lean.

Independent mathematical review checked the two lobes, the cross term,
global domination near zero, the 2π convention and the cutoff. Agreement
between reviewers is not treated as kernel verification.
