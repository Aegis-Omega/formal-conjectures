# A prime reflection prevents a Perron argument on the odd half-line cone

Status: complete ordinary analytic counterexample to a proposed auxiliary
semigroup property. Not a counterexample to RH or to positivity of Q.
No Lean kernel replay is claimed. The full source form and normalization
are those recorded in ../PROOF_COMPOSITION.md and its source manifests.

## Candidate and its exact failure

A tempting continuation of the simple-even spectral observations is to
prove positivity preservation of the local odd operator and use a Perron
argument there. This candidate fails for the actual zeta form already at
half-width a=1/2. Its positive-prime-weight reflection cannot be removed.

Let Qfull be the complete Weil form including the polar term. On real
functions with angular Fourier transform its polarization is

    Qfull(F,G) = Qarch(F,G)
        + M_+(F)M_-(G)+M_-(F)M_+(G)
        - sum_(n>=2) Lambda(n)/sqrt(n)
            [C_FG(log n)+C_GF(log n)],

where C_FG(t)=integral F(x)G(x+t)dx. On the two-moment-zero class this
reduces to the previously used Q; here the polar term is retained.
For disjoint supports of F and G, the diagonal subtraction vanishes and

    Qarch(F,G)=-integral integral F(x)G(y) k(|x-y|) dx dy,
    k(t)=exp(t/2)/(2*sinh t), t>0.

This follows directly by polarizing the full real-space Archimedean
identity. Supports below stay a positive distance apart, so Fubini is
justified by an integrable bounded kernel times |F(x)G(y)|.

Put d=log 2, x0=d/3, y0=2d/3, and 0<delta<=1/1000. Choose any nonnegative
even smooth phi supported in [-1,1], with integral phi^2=1. Define

    f(x)=delta^(-1/2)phi((x-x0)/delta),
    g(x)=delta^(-1/2)phi((x-y0)/delta),
    F(x)=f(x)-f(-x), G(x)=g(x)-g(-x).

Both F and G are odd smooth functions supported inside (-1/2,1/2).
Their supports are disjoint. Their positive-half profiles f and g are
nonnegative and disjoint. All statements hold for EVERY such normalized
phi, not just a numerical test family.

The elementary estimates 2/3<log 2<7/10 show that the smallest distance
between the supports of F and G is d/3-2delta>1/5. The largest is d+2delta<1.
The same inequalities imply y0+delta<1/2 and x0-delta>0. These estimates
can, for example, be obtained from
log 2=2*sum_(j>=0) (1/3)^(2j+1)/(2j+1): the first term is a strict
lower bound, and bounding 1/(2j+1)<=1/3 for j>=1 gives log 2<25/36<7/10.

## The arithmetic term is EXACTLY positive and of order one

At t=d the only intersecting support pair is F near -x0 and G near y0.
Since d-x0=y0 and phi is even, C_FG(d)=-integral phi^2=-1.
Likewise C_GF(d)=-1. For all n>=3, log n>=log 3>1 exceeds the support
differences, so both correlations vanish. Here log 3>1 follows from e<3,
for example by summing the exponential series and bounding its tail.
Consequently the COMPLETE prime contribution is exactly

    - (log 2)/sqrt(2) * (-1-1) = sqrt(2)*log 2.

No prime powers or reflection terms have been dropped.

For 1/5<=t<=1, sinh t>=t and exp(t/2)<=exp(1/2)<2 imply k(t)<5.
The last inequality follows from e<3<4. By Cauchy--Schwarz,
||f||_1,||g||_1 <=sqrt(2delta), and therefore
||F||_1||G||_1<=8delta. Thus

    |Qarch(F,G)| <=40delta.

Because |x|<=1/2, |M_+(F)|,|M_-(F)|<=2||F||_1, and the same is true
for G. The absolute value of the entire polar term is at most 64delta.
It follows that

    Qfull(F,G) >= sqrt(2)*log 2 -104delta
                > 2/3 -104/1000 >0.

The odd half-line isometry is Uf=(f(x)-f(-x))/sqrt(2). Hence its transported
form qodd(f,g)=Qfull(F,G)/2 has a positive off-diagonal entry for disjoint
nonnegative test functions f,g.

## Why this refutes the semigroup mechanism

Let Aodd denote the lower-bounded self-adjoint operator associated with
the local odd form, whose existence follows from the existing local
form theory. If exp(-t*Aodd) preserved the usual nonnegative cone on
L^2(0,1/2), then for disjoint nonnegative form-domain f,g,

    <exp(-t*Aodd)f,g> >=0, <f,g>=0.

The spectral theorem for a lower-bounded self-adjoint operator gives
qodd(f,g)=lim_(t->0+) <(I-exp(-t*Aodd))f,g>/t <=0, a contradiction.
For form-domain vectors the limit follows after shifting Aodd by a scalar
to be nonnegative and applying dominated convergence to its spectral
calculus; the scalar cross term is zero because <f,g>=0. Smooth f,g above
belong to this form domain. Thus no unconditional positivity-preserving
semigroup proof for this odd cone can be used.

This is compatible with the EXISTING positivity theorem on this window.
A positive quadratic form need not generate a positivity-preserving
semigroup. Semigroup positivity and positive semidefiniteness are different
properties, and this argument does not deny the latter.

On the odd two-moment-zero subspace an additional obstruction is immediate:
for an odd function with positive-half profile f>=0,

    M_+(F)=2 integral_0^a sinh(x/2)f(x) dx.

It vanishes only if f=0 almost everywhere. Thus the ordinary half-line
nonnegative cone has trivial intersection with the legal odd moment-zero
class. One cannot apply its Perron theory after imposing those moments
without proving a different cone construction and all its properties.

## Exact Toeplitz/Hankel split and the all-radius obstruction

For arbitrary real half-line profiles f,g supported in (0,a), extend them
oddly to F,G. For d>0 put

    I_fg(d)=integral_0^(a-d) f(x)g(x+d) dx,
    J_fg(d)=integral_(max(0,d-a))^(min(a,d)) f(x)g(d-x) dx,

where an empty interval contributes zero. Splitting the correlation at
x=-d and x=0 gives the exact identity

    C_FG(d)=I_fg(d)+I_gf(d)-J_fg(d).

The reflection substitution x->d-x shows J_fg=J_gf. Consequently, on the
isometric odd half-line carrier,

    qprime(f,g)=-sum_(n>=2) Lambda(n)/sqrt(n)
                 [I_fg(log n)+I_gf(log n)-J_fg(log n)].

The positive J term is a genuine reflected prime operator, not an
Archimedean error. Replacing it by a smooth small off-diagonal remainder
loses its order-one pairing on shrinking bumps.

For EVERY fixed a>log(2)/2 the same obstruction occurs. Choose

    0<eta<min(log(2)/4, a-log(2)/2),
    x0=log(2)/2-eta, y0=log(2)/2+eta.

Choose delta small enough that the four bump supports are interior and
separated and x0+y0+2delta<log 3. Then the n=2 prime pairing is still
exactly sqrt(2)*log 2 in the unscaled form. All other prime pairings
vanish. The continuous off-diagonal Archimedean kernel is bounded on
these four separated rectangles, and the polar kernel is bounded as
well, so their pairings are O(delta). It follows that

    lim_(delta->0) qodd(f_delta,g_delta)=log(2)/sqrt(2)>0.

Thus positivity preservation fails for every such a, not merely at one
computed radius. No claim about the endpoint a=log(2)/2 is made here.

Moreover, no self-adjoint COMPACT perturbation of this odd operator
repairs positivity preservation on the ordinary half-line cone. The
normalized shrinking profiles f_delta and g_delta tend weakly to zero
in L^2: for any h in L^2, the Cauchy--Schwarz bound uses the L^2 norm of
h on a shrinking support, which tends to zero by absolute continuity
of its integral. For compact K, ||K f_delta||_2->0, and hence
<K f_delta,g_delta>->0. The strictly positive limiting mixed value
therefore survives. The bounded self-adjoint perturbation still defines
a lower-bounded closed form, to which the same semigroup necessary
condition applies. In particular finite-rank and bounded smooth-kernel
corrections cannot supply this particular missing cone mechanism.

This is not an obstruction to a noncompact arithmetic correction, a
different cone, a direct semidefinite form proof, or the existing
Schur-complement route. It isolates the actual reflected-prime term
that such an argument would have to handle.

## Independent computational diagnostic and its scope

`verify_reflection_witness.py` uses instead the explicit H^1 bump
phi(u)=sqrt(15/16)*(1-u^2) on [-1,1], zero elsewhere. It checks its exact
norm and correlation polynomial and evaluates the FULL bilinear value by
800-bit Arb quadrature, separately pricing the polar and Archimedean terms.
This is a concrete independent check of the algebraic signs and factors;
the smooth universal bound above does not depend on quadrature or this
piecewise-polynomial test. The polynomial profile can also be approximated
by nonnegative even smooth profiles in H^1 and normalized in L^2, preserving
the separated supports and the strict positive margin.

No hypothesis equivalent to RH enters this counterexample. It falsifies
one concrete extension mechanism rather than producing a new RH criterion.
The remaining task is still an actual sign producer for the full legal
class. A different invariant cone is not ruled out by this calculation.
