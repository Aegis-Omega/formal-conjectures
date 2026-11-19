# Historical Python mathematical source review

This review concerns the 150 Python blobs in `python_manifest.json`, extracted from the supplied historical intake manifest. No historical program was imported or executed. Python AST parsing was used only to inspect source structure; malformed historical versions were treated as text. `body_structure.txt` preserves the function/class and module-docstring view. This is a bounded source review, not a claim that an RH proof cannot exist elsewhere.

The strongest unconditional all-support conclusion recoverable from the mathematical bodies is an effective high-frequency lower bound for the **actual finite-support Weil symbol**. Its proof is below. It does not supply the low-frequency quadratic sign needed by Weil's criterion. The interval Galerkin and Feshbach bodies supply finite computations and conditional extension mechanisms, not an unconditional all-window sign theorem. `rh_proven` remains false.

## 1. A sound effective growth producer, with full proof

The actual symbol is written in `2cb4cbbae83fba11c1d14c19b15ac0d46d8a3feb.py`, lines 35–41, for the range before prime 3 enters; the general finite-prime version is in the Feshbach and Epstein bodies. For a test function supported in an interval of length L, put

    W_L = sum_{prime powers q < exp(L)} Lambda(q)/sqrt(q),
    s_L(t) = Re digamma(1/4 + it/2) - log(pi)
             - 2 sum_{q < exp(L)} Lambda(q)/sqrt(q) cos(t log q),
    B_L = log(pi) - digamma(1/4) + 2 W_L > 0.

Here digamma(1/4)=-gamma-pi/2-3 log 2, so B_L has an explicit elementary/standard-constant enclosure; certified rational bounds for it can be computed independently of any zero or eigenvalue.

The sums are finite. Including an extra boundary prime power in W_L only weakens the lower bound and avoids any floating boundary decision. For every L>0, every real target M, and every dimension, one can effectively produce R with

    s_L(t) >= M whenever |t| >= R,
    s_L(t) >= -B_L for every real t.

Proof. For a>0, the convergent digamma expansion gives, for real y,

    Re digamma(a+iy) - digamma(a)
      = sum_{n=0}^infty y^2 / ((n+a)((n+a)^2+y^2)).

All summands are nonnegative. If |y| >= J-1+a, the first J summands are each at least 1/(2(n+a)). Taking a=1/4 and y=t/2 yields

    s_L(t) >= -B_L + (1/2) sum_{n=0}^{J-1} 1/(n+1/4)

whenever |t| >= 2(J-3/4), for J>=1. Choose J until the rational harmonic partial sum exceeds 2(M+B_L), using a certified rational upper bound for B_L if necessary. This search terminates because the harmonic sum diverges. Taking R=2(J-3/4) proves the first statement. Dropping the nonnegative digamma difference proves the second. This proof uses neither RH nor numerical eigenvalues.

Composition into the actual form. With Fourier convention `g_hat(t)=integral g(x) exp(-itx) dx`, and both exponential moments zero, the pole term in the explicit formula vanishes and the usual Fourier form is

    Q_W(g) = (1/(2 pi)) integral s_L(t) |g_hat(t)|^2 dt.

The identity applies to smooth compactly supported g; the finite prime support follows from the support of its autocorrelation. Consequently

    Q_W(g) >= M/(2 pi) integral_{|t|>=R} |g_hat(t)|^2 dt
              - B_L/(2 pi) integral_{|t|<R} |g_hat(t)|^2 dt.

In particular, Q_W(g) >= -B_L ||g||_2^2, unconditionally, for arbitrary support L. The conclusion is a lower bound with a negative allowance, not Q_W(g)>=0. The source bodies do not provide the necessary control of the low-frequency term by the high-frequency term for all moment-zero tests. Increasing R does not remove that term. This is the exact point at which this effective growth producer fails to close the sign argument.

## 2. The strongest finite sign mechanism: interval LDL and restrictions

Bodies: `eccddd8474e3d855e686878b28e74d1e4895329c.py`, especially lines 152–182, 241–331, 487–739; earlier version `6fb173d77e292f5e45b84c67c25f6d2ddfa0aac7.py`. The CLI versions at indices 140–147 call these evaluators or exact rational verifiers; they do not synthesize sign estimates.

The geometric auxiliary series have explicit geometric remainder radii. The matrix is assembled from pole, archimedean and finite-prime terms. At a fixed `(c,N,precision)`, interval LDL computes pivots. If every pivot interval is strictly positive, the enclosed exact symmetric matrix is positive definite: inductively each pivot and multiplier contains its exact counterpart, no divisor contains zero, and A=L D L^T gives

    x^T A x = sum_i D_i (L^T x)_i^2 > 0 for x != 0.

If all pivots have strict signs of either kind, the same congruence determines the inertia. The ordinary evaluator's `valid=True` permits negative pivots, so `valid` alone is not positivity. The restricted evaluator explicitly requires positive pivots.

The restricted body takes caller-supplied exact S, G and epsilon>=0 and evaluates

    S^T (K_N + epsilon G) S.

If positive, and if G represents the correct Gram form and S represents a moment-corrected basis, it proves

    q(Sx) >= -epsilon ||Sx||^2

on that finite subspace. It does not construct S or G from the actual test space, nor choose epsilon_N tending to zero. No claim about all N follows from the presence of loops accepting N. Moreover the shipped specification explicitly bounds N<=256 and c<=100000; its domain is not even a cofinal family of all supports/dimensions.

Termination is bounded for each admitted input: finite prime sieve, finite matrix loops, explicitly capped geometric-series loops (which can reject), and finite pivot loops (which can be undetermined). There is no theorem that raising precision eventually produces positive pivots for every `(c,N)`, and exact zero pivots cannot be resolved by merely shrinking interval error.

Needed limiting argument, stated precisely: for every support L there must be actual moment-zero g_N converging to every g in a topology in which q is continuous, actual Gram identification, bounded ||g_N||, and certified q(g_N)>=-epsilon_N||g_N||^2 with epsilon_N→0. Then taking the limit gives q(g)>=0. This elementary limiting implication is sound, but its universal numerical premise is not produced by these bodies. Thus density/continuity alone cannot complete the composition.

Dependencies followed in the existing full-source corpus:

* `2885b23d14f857fbcb7aa358ef0183a095482ba9.py` (`exact_ldlt`): verifies an explicitly supplied rational equality A=L D L^T and D_i>=0. Its finite loops terminate. Its proof is the displayed sum of squares. It provides no formula identifying A with q and no family of factorizations.
* `389662a6e3e493221f34beb6dc57f496f22a9788.py` (`arch_tail_certificate`): computes dyadic finite-band scalar trace/entry budgets and logarithmic tails. Its variables N and c remain fixed. Even a proof of `0 <= Q_infty-Q_T <= B_T I` here controls the **archimedean integration cutoff for a fixed finite band**, not the omitted basis complement or all support lengths.
* `89c2becefd2c561eb41aea9d7aab689bd7b348c5.py` and `969d7674a12a882a964910da706def0179e09387.py`: decomposed finite contribution interval addition, followed by the same local approximation implication discussed in section 5. No universal sign producer is hidden behind the CLI aliases.

## 3. Feshbach tails and the exact missing inequality

Bodies: `ae9a9311052ca2e8c1ddb43041b4c7e6a1a51781.py` and `08dafdbb2de1139a449dd09fe647fb10e201c2a7.py`. They construct a finite complex moment-zero basis Z and evaluate finite rows of A. Expanding

    1/(n-m) = sum_{j<K} m^j/n^(j+1) + m^K/(n^K(n-m))

for |m|<=N<NP<|n| gives explicit tail sums; Cauchy–Schwarz over the finitely many expansion terms produces the `Tail + Eco I` upper form. Assuming the displayed scalar bounds, this proves an upper bound on ||A v||^2 for v in the fixed finite span. Subtracting the squared norm of its orthogonal projection gives the intended cross-block bound

    ||P_perp A v||^2 <= v^* C_B v.

It is not a lower bound for q on the entire complement.

Here is the complete block composition such bounds can support. Write A on V plus V-perp as [[A11,B*],[B,C]]. If C>=c I for some c>0, then completing the square gives

    <A(v+w),v+w>
      = <(A11-B* C^{-1} B)v,v>
        + ||C^(1/2)(w+C^{-1} Bv)||^2.

Since C^{-1}<=c^{-1}I and B*B<=C_B, it is enough to prove

    A11 - C_B/c >= 0.

The finite cross-block upper bound does not produce C>=cI. The floating LP `f25ff0713ec2466243e922c23b76d6c3deaa3f75.py` proposes a symbol minorant/slack on a grid; `b0f104b879437090d9cf04ae9a5ddb61f1210ea3.py` does likewise at a fixed L=6/5. Neither proves its between-grid inequalities or an all-L selection/termination theorem. The exact-integer row-budget body `fe804b746ce0d3e98c2273edeb646bd2078b40f6.py` verifies a fixed N=139 residual certificate at L=6/5, with NP=150 and a chosen rational projection. Its exact arithmetic can validate that proposed finite certificate but does not produce the preceding inequalities for arbitrary L.

The general Feshbach bodies also use a 200-term `KS` sum as part of their asserted scalar bound. The written comment identifies it as a bound but the displayed construction does not add the positive remaining geometric tail. A direct conservative repair is to add

    exp(-(2*200+1/2)L) / (2(2*200+1/2)(1-exp(-2L)))

to that sum. This repair makes this one scalar series bound explicit; it does not discharge the complement sign inequality or globalization. The report does not treat the unchecked bound as a completed sign certificate.

## 4. Embedded Perron/growth proof: exact hidden assumption

Body `193d27b0c0ed6d059c6a1e60d2f3fa5b3bcee36b.py`, lines 25–48, writes

    lambda_P(gamma)
      = 2 Re[P^(1/2+i gamma)/(1/2+i gamma)]
        - 2 m(gamma) log P + O_gamma(1).

Its derivation says each zero is rho=1/2+i g' and every other zero gives a bounded oscillation. For an unrestricted zero rho=beta+i g', however, the actual integrated zero contribution has denominator

    beta-1/2+i(gamma+g')

and P-exponent

    beta-1/2+i(gamma+g').

When beta>1/2, its magnitude grows as P^(beta-1/2). Symmetries of zeta's zeros permit such a right-side zero whenever an off-line zero exists. The source's replacement of every beta by 1/2 is therefore precisely the assumption the proposed growth route needs to avoid. No uniform convergence estimate justifying the sum of bounded oscillations is supplied either. These are mathematical failures of the embedded proof, independently of how its finite slope assertions behave.

The same body claims its Gaussian main-term share is exactly `4 pi sigma^2 exp(sigma^2/4)`, independently of P. Its own integral convention gives the exact finite-P expression

    I(P,sigma) = sigma^2 integral_R
                  2 Re[P^(1/2+it)/(1/2+it)] exp(-sigma^2 t^2) dt
               = 2 pi sigma^2 exp(sigma^2/4)
                  erfc((sigma^2-log P)/(2 sigma)).

Proof: use `(1/2+it)^(-1)=integral_0^infty exp(-u/2-itu)du`, exchange the absolutely integrable Gaussian integral, evaluate its Fourier transform, and complete the square in u. The result tends to the source's constant as P→infinity. This exact Gaussian calculation is not a bound on the unrestricted zero contributions above, so the corrected identity cannot repair the hidden critical-line assumption.

## 5. Other actual mathematical bodies examined

`35087597b9f1be6ec5de922383960ae8b5725a3f.py` and its `qwhp`/`qw` bodies `ca36a73b8a8fa8078a1b7d7a0e3736d1b05b94fa.py`, `74fbe9c90b5f8416fef7b22306123f3c127b632b.py`: exact rational clamped polynomial trial functions, with v=psi/4-psi''. Integration by parts gives

    integral e^(sx) v(x) dx = (1/4-s^2) integral e^(sx) psi(x) dx = 0

at s=±1/2 because psi=psi'=0 at both endpoints. This is a genuine all-degree moment-zero construction. A rigorously evaluated trial quotient proves `inf q/||.||^2 <= q(v)/||v||^2`, an **upper** bound. An arbitrarily good positive upper bound cannot supply the lower bound required for positivity. The independent exact witness checker `157d23ba1d95f46939c16354d6f91b88f016e057.py` directly evaluates one such polynomial and has the same direction of conclusion.

`07d94cc01e75a164234eb06e8b62b46e03ab9fa9.py`: exact rational observable contraction. If A_plus=A_minus T and D=A_minus(I-TT^T)A_minus^T, then

    x^T D x = ||A_minus^T x||^2 - ||T^T A_minus^T x||^2.

Thus D>=0 iff T^T contracts on Ran(A_minus^T). The program decides D>=0 by all principal minors; termination follows because a fixed finite matrix has finitely many subsets and exact Gaussian elimination terminates. It verifies supplied A_minus,T. It supplies neither the actual Weil factorization nor a contraction estimate for the actual arithmetic matrices. Without those inputs it is an equivalence, not a sign producer.

`e393319732ce34dfe2adeb6f0ea9c32b6751da49.py`: the Fourier transform of sinc(a t-k)sinc(a t-l) is supported in [-2 pi a,2 pi a], because each sinc transform is supported in [-pi a,pi a] and multiplication convolves them. Hence prime cosine frequencies outside this interval vanish exactly in this section. This reduces the prime sum to finitely many terms; it makes no sign assertion about the remaining terms. The finite sinc Gram matrix is diagonal with scale 1/(2 tau scale), but its DC constraint is not the pair of exponential moment conditions by itself.

`352b76dffb9d9e2f98466bc988be0e97e8dcde59.py` and companion batch generation/resplitting bodies: exact rational Taylor-model algebra for the fixed L=21/20 certificate, using coefficients read from `RHKreinL105DataV1.lean`. The sound primitives are enclosure addition/multiplication, finite Taylor remainder bounds and interval cell subdivision. The certificate coefficients and L are fixed. No rule creates a certificate for arbitrarily large L, and cell subdivision improves verification of a proposed inequality rather than proving existence of that inequality.

`2cb4cbbae83fba11c1d14c19b15ac0d46d8a3feb.py` and its malformed historical version: explicit alternative clamped sine bases with g=(1/4-D^2)g1. The endpoint cancellation and exact Gram identities are valid; the symbol explicitly rejects L>=log 3. Its finite midpoint quadrature/eigensolve produces trial data, not a rigorous all-dimension lower bound.

`b3d1399ba5bea02f02d6c7f4336f4f205c1a5373.py` and five earlier Epstein bodies: finite coefficient recurrences for -F'/F and one fixed witness's arithmetic displacement between the principal D=-20 Epstein series and its class-sum control. The exact recurrence follows by multiplying `(-F'/F)F=-F'` and comparing Dirichlet coefficients. Even prime-power support of the Euler control is a structural identity rather than positivity of its Weil quadratic form. The final Arb extension encloses a finite sum of logarithmic/trigonometric values at support L=3.5; it is not a zeta all-support estimate.

`ff976121c82144a5a84c947d5ac3c9d0a0046f43.py` is a finite section diagnostic, not a proof. Its interlacing observation is correct: restricting the Rayleigh quotient's domain can only increase its infimum. That observation cannot turn upper Ritz values into lower bounds on the full space. No diagnostic experiments were replayed here.

`f9f6a549f97e600cf6f125f1a9f18813cf8c457f.py`, lines 188–251: the exact implication is `|Q_W-Q_R|<=delta` and `Q_R-delta>=0` imply `Q_W>=0`. The body only receives Q_R, delta and evidence commitments, and checks arithmetic. It does not prove either approximation premise or supply them for every test function. The later finite-certificate dependency verifies interval addition for a supplied decomposition, with the same finite scope.

The remaining source families are build/import/replay/receipt/census/catalog/CLI/test programs, plus already supplied obstruction/witness diagnostics. Their theorem references, aliases and generated Lean templates identify dependencies but do not themselves derive an arithmetic sign theorem. In particular the catalog's aliases point to fixed-window results, moment-killer range results, obstructions and conditional all-window reductions; its literature rows explicitly leave all-width simple/even eigenvector and approximation premises unproved. Those labels and statuses were not used as mathematical evidence.

## Conclusion of this bounded attempt

The high-frequency growth theorem in section 1 is unconditional, covers arbitrary L, and has an explicit terminating threshold construction. The missing composition is a nonnegative total lower bound after the low-frequency and mixed contribution is included. The finite algorithms would certify concrete instances if supplied adequate inputs and strict margins; no inspected mathematical body supplies those inputs with an unconditional all-L/all-dimension success theorem. This conclusion describes the exact examined candidates and their logical scope; it is not an inference that no other producer exists.
