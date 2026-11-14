# Source composition and the positive moment complement

This is an ordinary mathematical composition, not a completed Lean proof of RH.
The previous checkpoints under `/workspace/aegis-nov1` remain unchanged. The
source pin is Aegis-Omega/formal-conjectures
`f8cb6544e9451910fbf1ed5fa71e76a5fa1b747f`.

## 1. Exact form and source normalization

Use angular Fourier transform Hhat(t)=integral H(x) exp(-itx)dx and
E(H)=(1/(2pi)) integral |Hhat|²=integral |H|². The complete form on the two
exponential-moment-zero class is

    Q(H)=(1/(2pi)) integral w(t)|Hhat(t)|²dt
         -2 sum_(m>=2) Lambda(m)/sqrt(m) Re C_H(log m),
    w(t)=Re digamma(1/4+it/2)-log pi.

For support in an interval of length L, only m<=exp(L) contribute. No prime
power or Archimedean tail is discarded. Let X be the form domain with norm
squared integral log(2+|t|)|Hhat(t)|²dt. The multiplier w is bounded in absolute
value by a constant times log(2+|t|); the form is continuous in X on every
fixed compact support interval. The finite prime part is already continuous
in L² by correlation Cauchy–Schwarz and translation isometry.

`CvSArchDigammaV1.archSymbol_eq_hplus` identifies exactly this multiplier;
`CvSArchSourceV1.archTerm` has widths 2j+1/2, so its term
1/(j+1)-2(2j+1/2)/((2j+1/2)²+t²) is the same digamma term.
`CvSFeshbachWindowV1.zero_quadratic_eq_energy` identifies the smooth legal
packet zero side with this spectral integral divided by 2pi, when the
prime cutoff covers its support. Raw source spectral integrals and energies
are BOTH 2pi times the normalized quantities used here. Ratios agree; a
matrix transport still has to carry this factor explicitly.

The exact fetched bodies and blob checks are in `SourceCrosscheck/*.source.json`
and the independent HighMoment source manifests. Reading them is not a fresh
transitive kernel replay.

## 2. Reuse the existing window instead of reproving its sign

The fetched `CvSWindowL43V1.window_L43` (blob
`ad354cb73a86952dc7bed0a04dbce285b5feb103`) concludes zero-side nonnegativity
for EVERY smooth legal packet with 2r<=4/3. Its explicit arguments are the
packet, its two moments, center, half-width, support inclusion, and width
inequality. Its body supplies the trace/row/complement premises by existing
theorems. This is a source-body result; its transitive axiom/replay status
has not been freshly established in this runtime.

Here is the precise ordinary extension needed for actual CvS atoms. Let H in
X be supported in [0,6/5] and have both exponential moments zero. Choose a
nonnegative compactly supported smooth mollifier rho of integral one, and set
rho_epsilon(x)=epsilon^-1 rho(x/epsilon), supported in [-epsilon,epsilon].
Let H_epsilon=H*rho_epsilon, with 0<epsilon<1/15. Compact support implies
H in L¹. Thus H_epsilon is smooth and supported in
[-epsilon,6/5+epsilon], of length strictly less than 4/3.

Fubini is applicable to each exponentially weighted convolution: all factors
have compact support and are integrable. Consequently

    integral exp(sigma x) H_epsilon(x)dx
     =(integral exp(sigma x)H(x)dx)
      (integral exp(sigma x)rho_epsilon(x)dx)=0, sigma=+/-1/2.

The actual inverse lift g_epsilon(y)=y^-1/2 H_epsilon(log y) for y>0, zero
otherwise, is a genuine compact-positive smooth packet with exactly the
source moments. Apply the existing window theorem and exact explicit formula
to obtain Q(H_epsilon)>=0.

In Fourier space Hhat_epsilon=Hhat*rhohat(epsilon t), where the star here
means ordinary multiplication, not convolution. Since |rhohat|<=1 and
rhohat(epsilon t)->1, dominated convergence with dominating function
4 log(2+|t|)|Hhat(t)|² proves X convergence. The Archimedean integral converges
by its logarithmic multiplier bound. Each prime correlation converges because

    |C_F(a)-C_H(a)|<=||F-H||₂ (||F||₂+||H||₂),

uniformly in a, and there are only finitely many primes in one common compact
support cutoff. Hence Q(H)>=0. There is no pointwise-limit/integral interchange
without domination, and the support margin is explicitly positive.

This extension supplies the ordinary local sign on rough actual CvS atoms.
It does NOT supply the sign on arbitrary large support.

## 3. Exact actual-atom decomposition, not a dimension coincidence

The actual 139 atoms are U_a=D0[sin²(pi x/L)exp(2pi iax/L)] on [0,L], zero
outside, a=-69,...,69, D0=D²-1/4. Their zero-extended potentials are C¹;
the atoms themselves can jump at endpoints. The correct carrier is X,
not the original smooth packet type. Each atom has Fourier decay O(1/|t|)
and belongs to X.

The complete ordinary proof of the following source-specific result is in
`/workspace/aegis-nov2-independent/HighMoment/HIGH_MOMENT_COMPLEMENT_V1.md`:

    H=v+V, v in span{U_a},
    integral x^k exp(-x/2)V=0 (0<=k<=70),
    integral x^k exp(+x/2)V=0 (0<=k<=69),

uniquely, for every H in X([0,L]) with the original two moments. The extra
139 moment matrix on the ACTUAL atoms is invertible. Integration by parts
reduces a nullvector to orthogonality of sin² times a real trig polynomial of
degree 69 to a 139-dimensional real-root exponential-polynomial Chebyshev
space. A nonzero trig polynomial has at most 138 sign changes in one period;
a member of a suitable nested Chebyshev subspace can match those changes,
giving a strictly positive integral and a contradiction. Complex coefficients
split into real and imaginary parts. This projection is oblique; it is not
silently identified with the source's orthogonal residual or R_basis map.

More generally, with modes -N,...,N and p=N+2,q=N+1, the same argument gives
the 2N+1 correction and the remaining 2N+3 weighted moment conditions.

## 4. A genuine unconditional producer on arbitrary fixed supports

If H is supported in [-R,R] and kills the weighted moments through p-1 and
q-1, put n=p+q. Hermite interpolation of exp(zx), at the two real nodes
-1/2 and +1/2 with multiplicities p and q, evaluated at z=-it, integrates
to zero against H. The complex Hermite–Genocchi simplex remainder gives

    |remainder| <= exp(R/2) R^n (t²+1/4)^(n/2)/n!.

The real part of every convex combination of the interpolation nodes and -it
lies in [-1/2,1/2]. The simplex volume is 1/n!, so no exp(R|t|) is introduced.
Cauchy–Schwarz in ordinary L², followed by integration over [-T,T], gives

    low_frequency_energy <= epsilon_n E,
    epsilon_n=(2RT/pi)exp(R)[R²(T²+1/4)]^n/(n!)².

Let A_R=2 sum_(2<=m<=exp(2R)) Lambda(m)/sqrt(m). The digamma series shows
w(t)>=w(0), that w is increasing in |t|, and w(T)->infinity. The full prime
operator has norm at most A_R. Thus

    Q(H)>=[w(T)-A_R-(w(T)-w(0))epsilon_n]E.

For any R and delta>0 choose T with w(T)>A_R+2delta, then n sufficiently
large so epsilon_n<delta/(w(T)-w(0)). This proves a positive complement on
EVERY fixed support, with explicit finite moment conditions and a factorial
error estimate. The choice depends on R; it is not a universal-width bound.
Taking increasing n=2N+3 makes it compatible with the actual CvS correction
spaces in section 3. This is a producer, not an assumption of positivity.

At R=3/5,n=141,T=85, exact rational estimates give

    epsilon_n<13/20000, w(85)>103/40,
    w(0)>-6, A_R<9/4,
    Q(V)>=255541/800000 E >=31/100 E.

The final comparison is strict when V is nonzero. The zero residual has Q=E=0.

Only m=2,3 are active. These are inequalities for ALL such residuals, not a
finite-dimensional numerical minimum. The paper proves the digamma infinite
tail bound and the elementary gamma/log constants. The small core-Lean module
`HighMomentExactConstants.lean` checks the cleared integer comparisons, all
1024 rounded digamma summands and their total, using `decide`, not native
execution. It does not yet formalize their interpretation as analytic bounds.

## 5. What the existing local sign closes

For L=6/5, section 2 already gives Q(v+zV)>=0 for every complex z. Since the
moment-complement estimate gives Q(V)>0 for V!=0, minimize this quadratic
polynomial in z. One obtains

    |B_Q(v,V)|²/Q(V)<=Q(v)

and hence the supremum over all such V is also <=Q(v). This is the exact
local signed Schur inequality. It follows by composition with the existing
L43 sign; it is not an unresolved new local mathematical sign claim. Its
formal domain adapter is still PORT_PENDING. The stronger crude sufficient
bound Q(v)>=(100/31)||projection(A v)||² is NOT asserted or needed.

The same reasoning cannot be used on arbitrary supports before their sign
has been proved. There the high-moment producer controls the complement but
does not establish the low/cross signed Schur budget. Positive diagonal
blocks alone are insufficient: [[1,2],[2,1]] has positive diagonal blocks
and a negative eigenvalue. Neither the present positive complement nor the
already proved finite-window theorem supplies global RH positivity.

## 6. Recovered literature and scope

Connes and Consani, arXiv:2006.13771v1, full extracted text recovered through
the connected alphaXiv tool, proves in Theorem 3.6 a compact-perturbation
description of its archimedean trace-remainder operator on each bounded
interval; the surrounding argument obtains positivity after finitely many
linear conditions. Appendix B (148)-(153) records the same explicit-formula
prime weights and digamma normalization. This is relevant existing knowledge,
not an independent all-prime/global Schur producer. Its support restrictions
and extra conditions are not removed here. No novelty claim is made for the
general existence of a finite-codimension positive complement.

The discovered source-specific mechanism is the actual CvS moment correction,
the explicit Hermite bound, and the correctly reused local sign/domain
composition. The new analytic components have ordinary independent review;
their Lean formalization and global use are separate outstanding obligations.

## 7. Incorporate the newly recovered lambda laboratory

A final live-source check found PR92 had advanced by four commits to
`d7e6bc7602ccfe4bf5fb094ab595b36eb532d8d5`. Its 17 changed file bodies,
complete untruncated tree, compare response and Git identities are saved in
`LiveHead`. The earlier selected mathematical source bodies are unchanged.
The previous scoped absence of the S1 laboratory is superseded: its actual
source and outputs have now been recovered, not reconstructed.

The laboratory agrees with this form on the two-moment-zero subspace. On its
unrestricted space it additionally includes the full polar rank-two term.
Its small Ritz values are numerical diagnostics, with quadrature and finite
basis errors; the source audit and selected replay are in `LambdaLabAudit`.
Neither the reported double-exponential behavior nor the observation that
the minimum is even is used as a theorem here.

It motivates a genuinely exact synthesis: the asymmetric 141-moment space
does not commute with reflection. Add the actual odd atom with modulation
70 to the existing 139 directions and instead impose 71 moments at EACH of
the two exponential weights. The 140-dimensional correction then has 70
even and 70 odd directions. A half-interval Chebyshev argument proves its
moment matrix invertible; uniqueness makes the resulting projection commute
with reflection. The full form and the mixed budgets split into the two
parity channels. This is not a claim that either channel has global sign.

The full proof, including the centering phases and root-count construction,
is `BALANCED_PARITY_ADDENDUM_V1.md` in the independent HighMoment directory.
For the balanced complement at width 6/5, the same constants with order 142
give the universal bound

    Q(V)>=(8/25)||V||²,

strict for nonzero V. The sharper numerical lower coefficient is
129657/400000. `HighMomentSymmetric142.lean` checks the two new cleared
integer inequalities; it does not claim an analytic Lean port.

The separate `EXPLICIT_ALL_RADIUS_COMPLEMENT_ADDENDUM_V1.md` supplies an
explicit integer dimension selector on EVERY integer support radius R>=1.
With a=8R3^R, T=3^(a+8), A0=R(T+1), B0=2RT3^R and
J=max(2,3A0,B0(a+9)), the 2J weighted moments with multiplicities J,J
give Q(V)>=2||V||². The balanced actual correction has 2J-2 dimensions,
J-1 of each parity. The selector is enormous and is not proposed as a
practical computation. It proves only complement-certificate termination.

This removes the analytic existence of a positive complement from the
remaining all-radius budget. It does not prove the signed low/cross budget.
The exact open arithmetic statement for this route is: for every integer
R>=1 and every v in the specified actual low space, with its complete
prime-power/Archimedean form,

    Q(v) >= sup_(V !=0 in the balanced high-moment kernel)
                 |B_Q(v,V)|² / Q(V).

Both parity blocks must be covered. The denominator is unconditionally
positive by the producer above; boundedness of the cross functional follows
from the physical operator with its paid endpoint logarithms. The missing
inequality itself is not proved, not renamed as a hypothesis with a claimed
producer, and not inferred from finite positive Ritz values. It retains the
global RH-strength content; no final RH theorem has been checked.
