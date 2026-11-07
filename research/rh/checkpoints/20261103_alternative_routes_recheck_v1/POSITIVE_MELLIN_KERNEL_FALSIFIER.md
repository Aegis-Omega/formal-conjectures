# Strengthening the Li test to a strictly positive smooth Mellin kernel

Ordinary mathematical proof. No RH equivalence is added, and no claim is
made that the function below is the actual completed zeta. This follows
through on the polynomial counterexample by testing a stronger attempted
producer: positivity and very fast decay of the Mellin kernel, together
with finite order, the functional equation, and the critical strip.

## Exact construction

For a>0 and complex z define

    B_a(z)=integral_R exp(-a*cosh t)*exp(z*t) dt.

For each a this is entire and even in z, and real under conjugation.
Indeed cosh t grows exponentially in |t|, so every derivative in z is
dominated on each compact z-set by an integrable function. Reflection
t->-t gives evenness. Put z=s-1/2 and

    F(s)=[cosh(4*z)+cosh(1)]*B_1(z).

This has the EXACT positive-kernel representation

    F(s)=integral_R Phi(t)*exp((s-1/2)*t) dt,
    Phi(t)=(1/2)exp(-cosh(t-4))+(1/2)exp(-cosh(t+4))
           +cosh(1)*exp(-cosh t).

The substitution in each shifted integral proves the identity, with
absolute convergence. Phi is strictly positive, even, smooth, and has
superexponential decay at both ends, including every derivative. In
particular F(1-s)=F(s), F(conj s)=conj(F(s)), and F(s)>0 on the real
axis. Every even center Taylor coefficient is strictly positive, because
it is the corresponding positive moment of Phi divided by its factorial.
The odd center coefficients vanish.

For R>=1, cosh t>=exp(|t|)/2 and u=exp(|t|) give

    sup_(|z|<=R) |B_1(z)|
       <=2 integral_1^infinity u^(R-1)*exp(-u/2) du
       <=C*exp(R*log(4*R)).

For the last step split exp(-u/2) into two exp(-u/4) factors, bound
u^R exp(-u/4)<=exp(R log(4R)) by the same elementary majorant used in
the existing XiGrowth source, and integrate u^-1 exp(-u/4). The cosh
factor adds at most exp(4R)+cosh1. Thus F has order at most one. On the
positive real axis B_1(R)>=B_1(0)>0, since its even integral contains
cosh(Rt)>=1; the cosh factor grows like exp(4R), so F has order exactly
one. This construction retains the relevant coarse growth property of
the theta/Mellin argument rather than replacing it by order two.

## All zeros lie in the strict strip, but some are off its center

We first prove from the integral that every zero of B_1(z) is purely
imaginary. Differentiation in a is justified by the same rapid tail.
Integrating the t-derivatives of exp(-a cosh t+zt) and of
sinh(t)exp(-a cosh t+zt), whose boundary terms vanish, gives

    a^2*(d^2/da^2)B_a(z)+a*(d/da)B_a(z)-(a^2+z^2)*B_a(z)=0.

Let y(x)=B_(exp x)(z), x>=0. Then

    -y''(x)+exp(2x)*y(x)=-z^2*y(x).

For fixed z, both y and y' decay at least as a polynomial in exp x
times exp(-exp(x)/2). To obtain a bound directly from the defining
integral, split exp(-a cosh t) into exp(-a cosh t/2) factors, use one
factor <=exp(-a/2), and use a>=1 in the other; the remaining integrals
of (1+cosh t)exp(-cosh t/2+|z||t|) are finite. Therefore all the energy
integrals below converge and the boundary term at infinity vanishes.

The solution is not identically zero. In fact

    sqrt(a)*exp(a)*B_a(z) -> sqrt(2*pi), a->infinity.

After t=u/sqrt(a), pointwise convergence follows by expanding cosh at
zero. For a>=1, the integrand has modulus at most
exp(-u^2/2+|z||u|), an integrable Gaussian majorant. Dominated convergence
proves the displayed limit, independently of any zero hypothesis.

If B_1(z)=0, then y(0)=0. Integration by parts and the decay just proved
yield

    integral_0^infinity (|y'|^2+exp(2x)|y|^2) dx
       =-z^2 * integral_0^infinity |y|^2 dx.

The left side is strictly positive and the norm on the right is nonzero.
Consequently -z^2 is strictly positive real, which forces Re z=0 and
z!=0. This proves the required location of ALL B_1 zeros without RH.
No spectral identification with zeta is being assumed.

The remaining factor has its zeros exactly at

    z=+/-1/4 + i*(2k+1)*pi/4, k in Z,

by solving cosh(4z)=-cosh1. They are simple, and B_1 is nonzero at them
by the preceding result. Thus all F zeros have real part 1/4,1/2, or3/4,
and in particular rho=3/4+i*pi/4 is an actual simple off-center zero.
All lie in 0<Re s<1. F(0) and F(1) are strictly positive. Finite order
also supplies the usual weighted inverse-square zero summability by
the classical entire-function zero-counting theorem; this last general
theorem is not needed for the direct contradiction below.

## Why all its Li coefficients cannot be nonnegative

Define G(w)=d/dw log(F(1/(1-w))) near w=0, meaning the logarithmic
derivative (not a choice of logarithm). Since F(1)>0 it is analytic there
and its Taylor coefficients are real. At rho=3/4+i*pi/4 it has a
nonremovable pole at w0=1-1/rho. The Mobius derivative is nonzero and
the zero is simple. Moreover

    |w0|^2=|rho-1|^2/|rho|^2<1,

because Re rho>1/2. Hence its Taylor radius r satisfies 0<r<1.

If every Taylor coefficient were nonnegative, r would have to be a
singular point on the positive real axis. Here is the positivity argument
in full, so no unverified invocation of Pringsheim is hidden. If G were
analytic near r, for each k its derivatives as x increases to r would
converge to G^(k)(r). Monotone convergence of the nonnegative series gives

    G^(k)(r)/k!=sum_(n>=k) binom(n,k)*a_n*r^(n-k).

For some epsilon>0 its Taylor series at r converges at r+epsilon.
Tonelli and the binomial theorem then give

    sum_k G^(k)(r)*epsilon^k/k!
      =sum_n a_n*(r+epsilon)^n <infinity,

contradicting radius r. In our case G IS analytic at every positive
r<1: its argument 1/(1-r) is real >1 and F there is strictly positive.
Thus at least one Li/Taylor coefficient is negative.

This uses an actual pole and a fully justified limit argument, not a
generic false claim that pairwise minors force PSD. It produces no new
RH-equivalent criterion. It is a counterexample to the tested universal
producer, using an explicit positive Mellin kernel and exact off-axis
zeros. The index of a negative coefficient is not certified here; the
separate polynomial witness has an exact certified index.

## Boundary of the conclusion

The example is not the Jacobi theta kernel or the zeta Euler product.
It therefore cannot refute an argument that uses their more specific
identities and proves its hypotheses. It does refute any proposed
argument which forgets all that structure and retains only positivity,
smoothness, rapid decay, finite order, symmetry, and strip containment.
These conditions survive this adversarial test family simultaneously.
This tells us which information a stronger Li/Hadamard producer must
retain; it does not prove that every other route reduces to Schur.

All analytic statements here are ordinary proofs, not a Lean port.
No final RH theorem or unconditional Li sign for actual zeta is claimed.
