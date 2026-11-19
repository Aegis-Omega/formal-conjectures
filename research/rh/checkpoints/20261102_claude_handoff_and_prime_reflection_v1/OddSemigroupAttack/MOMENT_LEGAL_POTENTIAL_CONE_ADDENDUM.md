# The moment-killer does not remove the reflected-prime obstruction

This continues the already published ordinary proof; it does not alter its
source or regenerate its archive. The new claim concerns the actual legal
two-moment class, by transporting a positive cone through the existing
moment-killer. It is a falsification of a proposed Perron mechanism, not
a claim that mixed entries of a PSD form must be negative.

Fix a>log(2)/2 and centers x0,y0 as in the previous proof, with
x0+y0=log 2, x0!=y0, both in (0,a). Let phi be a nonnegative even
C_c^infinity(-1,1) function with ||phi||_2=1. Put

    p_delta(x)=delta^(-1/2)phi((x-x0)/delta),
    q_delta(x)=delta^(-1/2)phi((x-y0)/delta),
    P_delta(x)=p_delta(x)-p_delta(-x),
    S_delta(x)=q_delta(x)-q_delta(-x),
    H_delta=(1/4-D^2)P_delta,
    J_delta=(1/4-D^2)S_delta.

These are genuine compact smooth odd functions. BOTH exponential moments
of H_delta and J_delta vanish exactly, by the existing moment-killer
identity and integration by parts with no boundary terms. The positive
half POTENTIALS p_delta,q_delta are nonnegative and disjoint. The positive
half profiles of H_delta,J_delta need not be nonnegative; this distinction
is explicit and essential.

Let A=||phi''||_2^2>0 and B=||phi'||_2^2. The squared norm of the single
local image (1/4-D^2)p_delta is exactly

    E_delta=delta^(-4)A+(1/2)delta^(-2)B+1/16.

Indeed the cross term is -(1/2)delta^(-2)<phi,phi''>, and
<phi,phi''>=-||phi'||^2. A>0 because a compactly supported affine function
is zero. The reflected prime n=2 contributes EXACTLY

    sqrt(2)*log(2)*E_delta

to Q(H_delta,J_delta). All other prime terms vanish for small delta:
the supports remain near the same four centers, and their largest
difference stays below log 3. The polar contribution is exactly zero.

## Full Archimedean term after the moment-killer

On the separated support rectangles, integration by parts twice in each
variable moves the two moment-killers onto the Archimedean kernel. For
t>0 write

    k(t)=exp(t/2)/(2*sinh t)=sum_(n>=0) exp(-(2n+1/2)t).

The transformed kernel is

    k2(t)=(1/4-D_t^2)^2 k(t)
         =sum_(n>=1) 4*n^2*(2n+1)^2 exp(-(2n+1/2)t)
         =4*exp(-t/2)*z*(9+55*z+31*z^2+z^3)/(1-z)^5,
           z=exp(-2t).

Termwise differentiation is valid uniformly on t>=m for every m>0,
because the fourth-degree polynomial in n times exp(-2nm) is summable.
The n=0 term vanishes, rather than being discarded as an error. The
rational expression follows from the convergent sums of n^2 z^n,
n^3 z^n and n^4 z^n. Thus k2 is bounded on the separated rectangles.

Each odd potential has L^1 norm <=2*sqrt(2delta), so their mixed
Archimedean pairing after these integrations by parts is O(delta), with
a constant depending on the fixed centers and phi, not on delta. All
diagonal distribution terms vanish since the supports are separated.
Therefore

    Q(H_delta,J_delta)
       =sqrt(2)*log(2)*E_delta+O(delta),
    Q(H_delta,J_delta)/E_delta
       =sqrt(2)*log(2)+O(delta^5) >0

for sufficiently small delta. These are actual legal moment-zero packets
after the usual inverse logarithmic lift; no pole or infinite tail is
missing. This transports the original reflected-prime witness onto the
legal domain without assuming RH or changing the sign convention.

There is also an explicit error bound. Put h=y0-x0>0, M=integral phi>0,
and fix delta0>0 small enough for all support exclusions above and
m=min(h,log 2)-2delta0>0. Define

    c0=2*M^2/A * [k2(h)-k2(log 2)] >0,
    C=c0*[B/(2*A)+delta0^2/(16*A)] +8*M^2/A*k2''(m).

For every 0<delta<=delta0,

    |Qarch(H_delta,J_delta)/E_delta +c0*delta^5| <= C*delta^7.

To check the estimate, expand k2(c+delta*(u-v)) to first order. Its linear
term integrates to zero because phi is even; the quadratic remainder has
absolute integral <=2*delta^2*M^2*k2''(m). The positivity and monotone
decrease of k2'' follow from its positive exponential series. There are
two odd copies and two distances h,log 2, giving an unnormalized error
<=8*delta^3*M^2*k2''(m). Divide by
E_delta=delta^(-4)A*[1+B*delta^2/(2*A)+delta^4/(16*A)] and bound the change
in the leading denominator by its nonnegative additive part. This gives
the stated C exactly. Thus the complete normalized mixed value is

    sqrt(2)*log(2)-c0*delta^5+error, |error|<=C*delta^7.

The order-one reflected prime and the order-five Archimedean correction
are separated with a quantified error, not inferred from a numerical
plateau or from a finite-dimensional positive minimum.

## Consequence for the positive-potential cone

Consider the potential form

    qpot(p,q)=Q((1/4-D^2)Up,(1/4-D^2)Uq),

where U is the odd half-line isometry from the previous manuscript.
For the unit-norm nonnegative disjoint potentials above,

    qpot(p_delta,q_delta)
       =log(2)/sqrt(2)*E_delta+O(delta) -> +infinity.

For every bounded self-adjoint operator T on the potential L^2 space,
|<T p_delta,q_delta>|<=||T||. Thus adding ANY bounded perturbation, not
just a compact perturbation, cannot repair the necessary nonpositive
disjoint-cross-term condition for positivity preservation on this cone.

The potential form is lower bounded for each fixed a: on its smooth
compactly supported core its Fourier multiplier is

    [w(t)-2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n)*cos(t log n)]*(t^2+1/4)^2.

Its negative part is bounded, since w(t) grows like log|t| and the prime
sum is finite. Its shifted form norm is comparable to the weighted
Fourier norm with weight 1+t^4*log(2+|t|). Completing the core gives its
closed densely defined Friedrichs form; the odd subspace is invariant.
Thus the standard necessary semigroup condition used earlier applies to
the associated operator whenever that cone-preserving property is
claimed. No assumed self-adjointness or RH positivity is used to define
it. The argument does not assert that this higher-order form domain is
closed under taking absolute values; indeed that would be another
necessary condition for a positivity-preserving semigroup.

An actual unconditional sign proof is not ruled out. What is ruled out
is this specific attempted cone argument after a bounded correction.
Noncompact arithmetic structure, a different cone, and direct Schur
estimates remain distinct possibilities requiring their own proofs.

## Concrete computational check

verify_moment_legal_reflection.py uses the exact clamped polynomial
phi(u)=(1-u^2)^4 on [-1,1], zero outside. Its local image is obtained by
exact rational differentiation. The correlation, norm and prime pairings
are exact polynomial operations; the full Archimedean pairing is evaluated
with 800-bit Arb integration. This piecewise-smooth profile is in the
form domain and both moments vanish exactly by clamping. Smooth
nonnegative clamped-potential approximations preserve those moments and
the separated supports, and converge in the form norm. The general
smooth proof above does not depend on the numerical witness.

This is an ordinary proof plus a source-bound interval computation. No
Lean analytic port or RH proof is claimed.
