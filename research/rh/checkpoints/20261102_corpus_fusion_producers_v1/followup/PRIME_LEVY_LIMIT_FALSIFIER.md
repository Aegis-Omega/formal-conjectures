# What happens to the actual finite prime Levy laws

Status: ordinary proof reconstructed by the primary agent. No Lean theorem,
independent-agent verification, or novelty claim. The only imported number-
theoretic theorem is the unconditional prime number theorem in its precise
Chebyshev form psi(x)=sum_(n<=x)Lambda(n)=x+o(x). No RH-size error estimate
is used. All prime powers are included through Lambda.

The recovered `weil_levy_gap_probe.py` already observes divergence of the
untempered prime jump mass. This argument determines the actual normalized
characteristic-function limit, rather than assuming that divergence alone
proves every possible limiting claim false.

## 1. Fixed objects

Let P tend to infinity through real values P>=2, and define

    S_P(t)=sum_(2<=n<=P) Lambda(n)n^(-1/2+it),
    eta_P(t)=w(t)-w(0)+2 S_P(0)-2 Re S_P(t),
    w(t)=Re digamma(1/4+it/2)-log pi.

These are the exact functions in the finite-cutoff source probe before
quadrature. The finite symbol is w(t)-2Re S_P(t), and eta_P subtracts its
value at0. By the existing Levy–Khintchine decomposition, for every fixed
theta>0,

    phi_P(t)=exp(-theta eta_P(t))

is the characteristic function of a symmetric probability law mu_P. The
Archimedean Levy measure is legitimate: near0 its density is O(1/|x|), and
at infinity it decays like exp(-|x|/2), so its min(1,x²)-weighted mass is
finite. The arithmetic part has finitely many positive jumps. This uses
positivity of the normalized finite exponent, not positivity of the
original Weil quadratic form.

## 2. The weighted prime asymptotic, with controlled errors

**Lemma.** For every fixed B<infinity,

    S_P(t)=P^(1/2+it)/(1/2+it)+o_B(sqrt(P))

uniformly for real |t|<=B.

Write psi(x)=x+E(x), E(x)=o(x). Finite Abel summation, with lower boundary
psi(1)=0 and s=-1/2+it, gives

    S_P(t)=P^s psi(P)-s integral_1^P psi(x)x^(s-1)dx.

The x main term equals P^(s+1)/(s+1) plus a bounded term; its denominator
has real part1/2 and cannot vanish. For every epsilon>0 choose X with
|E(x)|<=epsilon x for x>=X. The error of the boundary term is at most
epsilon sqrt(P) for large P. Uniformly for |t|<=B, the error integral
over[1,X] is bounded by a constant depending only on B,X. Its remaining
part is at most

    sqrt(1/4+B²) epsilon integral_X^P x^(-1/2)dx
       <=2sqrt(1/4+B²)epsilon sqrt(P).

Divide by sqrt(P), then let P->infinity and epsilon->0. This proves the
lemma. No sum/integral interchange beyond finite Abel summation is used,
and no uniform-in-growing-B PNT estimate has been assumed.

It follows, for each fixed real t,

    eta_P(t)/(4sqrt(P))
      =1-Re[exp(it log P)/(1+2it)]+o(1).

The fixed Archimedean difference divided by sqrt(P) vanishes. The exact
factors2 and4 follow from S_P(0)=2sqrt(P)+o(sqrt(P)).

## 3. No fixed-time probability limit: mass leaves every compact set

For fixed t!=0,

    1-Re[exp(it log P)/(1+2it)]
       >=1-1/sqrt(1+4t²)>0.

Thus eta_P(t)->infinity for every fixed nonzero t. Therefore

    phi_P(0)=1 for every P,
    phi_P(t)->0 for every fixed t!=0.

The pointwise limit is discontinuous at0 and is not the characteristic
function of a probability measure. In particular the laws cannot converge
weakly to a probability at this normalization.

More strongly, they escape EVERY fixed compact interval. For A>0, Fourier
inversion of a Gaussian and Fubini give

    integral exp(-x²/(2A²)) dmu_P(x)
      =(A/sqrt(2pi)) integral exp(-A²t²/2)phi_P(t)dt ->0.

Fubini is justified by the integrable Gaussian transform and probability
mass1. Dominated convergence applies because |phi_P(t)|<=1, and the
exceptional point t=0 has Lebesgue measure zero. Since
1_[−A,A](x)<=exp(1/2)exp(-x²/(2A²)),

    mu_P([-A,A])->0.

The family is not tight. This is stronger than merely noting infinite
jump mass, and is a falsifier for a proposed ordinary fixed-time
probability-limit argument on the actual prime measure.

The hypotheses theta>0 and t!=0 are essential. At theta=0 all laws are
delta0. At t=0 every characteristic function remains1. No uniform bound
away from t=0 or false continuity of the limit is asserted.

## 4. A positive rescaled limit exists, but is a different object

For fixed theta>=0 consider instead

    Phi_P(t)=exp[-theta eta_P(t/log P)/(4sqrt(P))].

The uniform bounded-t lemma applies to t/log P. Since

    exp(i(t/log P)log P)=exp(it),
    1+2it/log P ->1,

we obtain eta_P(t/log P)/(4sqrt(P))->1-cos t. The Archimedean increment
also vanishes after division by sqrt(P); continuity of w at0 suffices.
Consequently

    Phi_P(t)->exp[-theta(1-cos t)].

The limit is continuous at0 and is the characteristic function of the
symmetric compound-Poisson law with total intensity theta and jumps+1,-1
of equal probabilities. Levy's continuity theorem therefore gives weak
convergence for THIS simultaneously time- and space-rescaled family.

The scaling changes time to theta/(4sqrt(P)) and space to x/log P. It
does not represent the original finite Weil symbol on its original test
functions. The limit has discarded the arithmetic fine structure needed
for the signed Weil budget. Its positivity is not a new RH producer.

## 5. Why this does not contradict compact-support stabilization

On a FIXED compact-support carrier the full quadratic form stabilizes once
the prime cutoff covers the correlation support. In the jump decomposition,
however, the positive jump energy and the adverse scalar offset EACH grow
like4sqrt(P); their contribution from inactive primes cancels exactly in
the signed form. The normalized probability laws retain the jump part but
omit the growing scalar mass factor. Their loss of tightness is therefore
compatible with exact stabilization of the signed compact-support form.

Restoring the scalar factor gives a finite positive measure for each P,
with total mass exp(-theta[w(0)-2S_P(0)]), which grows without bound. It
does not restore a finite probability limit or discharge the signed
Poincare/Schur inequality on the legal two-moment class.

This rules out one specific finite-positive-process globalization. It
does not rule out every tempered, compensated, distributional or projected
construction. Any such alternative must identify the SAME actual Weil
form and pay its scalar/mixed terms before it can enter the RH chain.
