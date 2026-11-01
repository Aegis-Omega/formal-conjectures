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

## The same obstruction occurs inside every positive window

Fix any integer M≥1 and any L>0. Choose ε>0 with
`2ε < min(L, log(M+1))`, and replace eta by `eta(x/ε)` in the preceding
construction. Its source and corrected scaled packets now have widths at
most 2ε and ε. Both satisfy the actual moment conditions and fit strictly
inside the window L; the source cutoff M is valid for both.

The same proof applies to the fixed finite symbol S_M. If C_ε is the
positive Fourier mass of eta(x/ε), then

    (Q(g'_T)-Q(g_T))/(T⁴ log T) → 7 C_ε > 0.

Define the actual critical-line mass `N(g)=(1/(2π))∫Nr_g`. The same
two-lobe dominated-convergence proof without the logarithmic symbol yields

    N(g_T)/T⁴ → C_ε > 0,
    [ (1/(2π))∫(-Δ_(2,M)) Nr_(g_T) ] / N(g_T) → -∞.

Indeed the numerator is asymptotic to `-7 C_ε T⁴ log T`. A fixed real m
contributes only m*N(g_T), and any measurable bounded slack σ satisfies
`|(1/(2π))∫σ Nr_(g_T)|≤||σ||∞ N(g_T)`. Neither can offset the logarithmic
negative divergence. This also rules out the corresponding universal
certificate conclusion with any fixed m and bounded slack, on these actual
packets. The argument uses the generic `certificate_raw` if L exceeds
log(M+1); it does not assume the extra window condition in the specialized
`certificate_slack` theorem.

In particular, for sufficiently large T the actual density of g_T obeys

    (1/(2π)) ∫ Δ_(2,M)(u) Nr_(g_T)(u) du > 0,
    Δ_(2,M)(u) = S_M(2u)/2
      * ((4u²+1/4)/(u²+1/4))² - S_M(u).

This is the complete density-weighted defect from the previous checkpoint,
not a pointwise comparison. The corresponding integral with -Δ is strictly
negative on an admissible packet. Therefore no total correction with a
well-defined pairing that vanishes for every packet in that window can establish universal
nonnegativity of that integral. In particular, the existing
`RHKreinZetaBridgeV4.certificate_raw` cannot discharge this particular
unnormalized transport claim with any fixed finite m, irrespective of the
values of its finite certificate parameters. This conclusion does not rule out normalization,
nonzero paid defects, different decompositions, or other RH approaches.
For an infinite correction family, convergence of the total pairing and
interchange with any sum would themselves need justification.

## Necessary condition for constant normalization

The same two-lobe argument applies to every fixed compression s>1. With
`G'_(s,T)=A(f_T(s·))`, Fourier scaling gives a Jacobian 1/s and the weight
`W(su)`, hence

    Q(g'_(s,T))/(T⁴ log T) → s³ C_ε.

For a fixed complex scalar c, the source quadratic form is homogeneous:
`Q(c g)=|c|² Q(g)`. Therefore any proposed uniform inequality
`Q(g) ≥ Q(c g'_s)` on all moment-zero packets in a positive window must
satisfy

    |c|² ≤ s^(-3).

If `|c|²>s^(-3)`, the same actual oscillatory packets falsify the claimed
inequality for all sufficiently large T. The boundary value and smaller
normalizations are not decided by this high-frequency argument. In
particular this necessary condition is not a proof that a normalized
transport exists.

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
