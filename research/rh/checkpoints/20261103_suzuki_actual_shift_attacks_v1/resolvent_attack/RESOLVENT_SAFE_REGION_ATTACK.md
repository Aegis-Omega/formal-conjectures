# Finite positive shifts do not identify the safe-region zeta limit

Date: 2026-11-03. `rh_proven = false`.

This is an ordinary operator-theoretic argument, not a Lean/kernel check and not
a numerical experiment. I first read `audit/SUZUKI_SOURCE_COMPOSITION.md`, then
the primary v3 text, specifically Theorem 1.5, Corollary 1.6, Sections 2.4, 4.5,
6.1–6.5, and 7.8–7.9. No old scripts, downloads, or GitHub writes were used.

The concrete result is an admissible choice of the **actual Suzuki shifted
operators** for which the canonical normalized Herglotz functions converge to
the free constant `i` on the entire upper half-plane. They consequently fail to
agree with the candidate zeta function even on `Im z > 1/2`. I also isolate the
uncontrolled ground-eigenspace term when the positive shift is chosen close to
the lowest eigenvalue. This does not exclude every possible carefully selected
shift sequence; it disproves identification based solely on finite positivity,
normal-family compactness, and the Euler product.

## 1. Exact finite-a objects and normalization

Fix `a>0`. Let `A=A_a` be Suzuki's self-adjoint realization of the full Weil form
on `L2(-a,a)`, let `ell=lambda_a=inf spec A`, and let

    T = A - lambda I = A - ell I + epsilon I,
    lambda = ell - epsilon,       epsilon>0,
    R = T^(-1).

No sign is assumed for `ell`. Section 6.3 gives the exact adjoint eigenvectors

    v_z = R e_z,                 e_z(x)=exp(-i z x).

In particular, choose

    u_+ = R exp(x),              u_- = R exp(-x).

These are precisely the deficiency vectors for eigenvalues `+i` and `-i`.
Because `A` is real and commutes with reflection `Jf(x)=f(-x)` (Section 4.5),
`u_-=J u_+`. Their T norms are equal, as Theorem 1.5 requires:

    ||u_+||_T^2 = <R exp(x), exp(x)>_2
                = <R exp(-x), exp(-x)>_2 = ||u_-||_T^2.

Thus no arbitrary relative scale or phase has entered. Multiplying both vectors
by the same nonzero real scalar has no effect on the quotient below.

Use Suzuki's Fourier sign

    Ff(z) = integral_(-a)^a f(x) exp(i z x) dx,

and put

    P(z) = (z-i) F u_+(z),
    Q(z) = (z+i) F u_-(z).

Then the actual characteristic functions in (1.11) are

    W_0 = P+Q,                  W_pi = P-Q.

Define the canonical normalized functions

    theta_a(z) = P(z)/Q(z),
    m_a(z) = i (1+theta_a(z))/(1-theta_a(z)) = -i W_0(z)/W_pi(z).       (A)

These definitions fix the freedom that an arbitrary exponential gauge on W
would leave. They use both actual self-adjoint boundary conditions.

Here is a direct justification that (A) is a normalized Herglotz function using
the already established Theorem 1.5. For every unit complex `eta`, `P+eta Q`
has no zeros in the upper half-plane. At `z=i`, `P(i)=0`, while

    Q(i)=2i <R exp(-x),exp(-x)>_2 != 0.

Hence `theta_a(i)=0`. A simultaneous zero of `P,Q` would violate the same
theorem. A pole of `P/Q`, or a point with `|P/Q|>=1`, would, by continuity from
`i`, give a point with `|P/Q|=1`; the appropriate unit `eta` would then make
`P+eta Q=0`. Consequently `theta_a` is analytic with `|theta_a|<1`, and `m_a`
is analytic with positive imaginary part and `m_a(i)=i`. These functions form
a normal family by the Cayley transform and Montel's theorem. This argument
does not assume the unshifted global de Branges identification in Section 7.

## 2. The exact safe-region candidate supplied by the zeta model

Let

    s=1/2-i z,       X(z)=xi(s),       E(z)=xi(s)+xi'(s),
    q=xi(3/2),       r=xi'(3/2).

The prime on `xi` means differentiation in `s`. In particular
`dX/dz=-i xi'(s)`; losing this factor changes the Herglotz normalization.

The Euler product proves `xi(s)!=0` on `Re s>1`, equivalently

    Omega_safe = {z: Im z>1/2}.

On this region the logarithmic derivative is the unconditional analytic
function

    L(s)=xi'(s)/xi(s)
        = 1/s + 1/(s-1) - (log pi)/2
          + psi(s/2)/2 - sum_(n>=2) Lambda(n)n^(-s).                 (B)

The Dirichlet series converges absolutely and uniformly on smaller closed
half-planes. The candidate normalized Herglotz object in Suzuki's model is

    m_xi(z) = i (q/r) L(1/2-i z).                                  (C)

This is obtained by using **both** `theta=0` and `theta=pi` in the exact boundary
form algebra of Section 7.8, rather than guessing from W alone. Indeed its
displayed constants are `C_0=q`, `C_pi=i r`, so the model boundary expressions
are

    W_0^model =  2i q xi'(s)/(pi E(z)),
    W_pi^model = -2i r xi(s)/(pi E(z)),

up to the same nonzero common scale. Taking `-i W_0^model/W_pi^model` yields
(C), and `m_xi(i)=i`. This derivation is algebra from the model expressions;
the source's identification of that global model with the Weil Hilbert space
in Section 7 is made under RH and is **not** used as an unconditional theorem.

Unconditionally `q,r>0`: for real `s>1`, the standard symmetrized Hadamard
logarithmic derivative has positive terms
`Re(1/(s-rho))`, since all nontrivial zeros satisfy `0<Re rho<1`.
Thus `xi'(s)/xi(s)>0` there. The same formula gives `Re L(s)>0` for `Re s>1`.
In particular `1+L(s)` is nonzero on the safe region, and the target in
Corollary 1.6 is analytic there:

    F_xi(z)=1/(1+L(1/2-i z)).                                      (D)

The candidate is not constant even on the safe region. The Euler product and
the elementary digamma asymptotic imply, for real `sigma -> +infinity`,

    L(sigma) = (1/2) log(sigma/(2pi)) + O(1/sigma) -> +infinity.

Thus `m_xi(i y)` is nonconstant and unbounded as `y->infinity`, while
`F_xi(i y)->0`. These facts are unconditional.

## 3. Actual admissible shifts giving a different safe-region limit

For each fixed `a`, choose `L>max(0,-ell)` and set

    lambda=-L,       epsilon=L+ell>0,       R_L=(A+L)^(-1).

This is exactly the requested `A-ell+epsilon` family, with an admissible positive
`epsilon`; it is not a substitute operator. By the spectral theorem,

    L (A+L)^(-1) f -> f strongly in L2(-a,a),  for every f, as L->infinity. (E)

For example, for sufficiently large L the multipliers `L/(t+L)` are bounded
by 2 for every `t>=ell`, and tend pointwise to 1. Dominated convergence proves
(E). Applied to `exp(±x)`, this convergence implies locally uniform convergence
of their Fourier transforms and of the actual W's: the evaluation vectors
`exp(-i conjugate(z)x)` have bounded L2 norm on every compact set.

The free transforms can be computed exactly, with no asymptotic assumptions:

    integral exp(x) exp(i z x) dx = 2 sinh(a(1+i z))/(1+i z),
    integral exp(-x)exp(i z x) dx = 2 sinh(a(-1+i z))/(-1+i z).

Since `1+i z=i(z-i)` and `-1+i z=i(z+i)`, the removable factors cancel and give

    L W_pi(z) -> -4i sinh(a) cos(a z),
    L W_0(z)  ->  4 cosh(a) sin(a z),              L->infinity.       (F)

The corresponding **actual normalized quotient** therefore approaches

    m_a^free(z)=coth(a) tan(a z),

which satisfies `m_a^free(i)=i`. As `a->infinity`,

    m_a^free(z) -> i

uniformly on every upper-half-plane compact. To obtain a single actual
admissible sequence, take `a_n=n` and choose `L_n` sufficiently large for (F)
on an increasing compact exhaustion. The following estimate makes this choice
concrete rather than leaving only a qualitative diagonal argument.

### A sufficient shift-size estimate

Let `S=A-ell>=0`, `C=L+ell=epsilon`, `h_±=exp(±x)`, and

    N_a=||h_±||_2=sqrt(sinh(2a)),
    H_a=||S^(1/2)h_±||_2^2.

`H_a` is finite. Here a form-domain argument is needed, rather than the mere
inclusion `D(Q_W^a) subset H^log` stated in Section 3.1. The truncated
exponentials have Fourier transforms `O_a((1+|t|)^(-1))`, so they belong to
`H^s(R)` for every `0<s<1/2`. Smooth interior cutoffs approximate them in H^s
for this range of s; equivalently, the shrinking endpoint layers have H^s
norm tending to zero. Since `1+log^+|t| <= C_s(1+|t|^(2s))`, they also
approximate in the logarithmic Fourier norm. On the smooth core, (2.8) bounds
the form norm by that Fourier norm plus a finite-a L2 term. Hence the cutoffs
are Cauchy in the closed form norm and converge in L2 to the truncated
exponentials, placing these vectors in the closed form domain. Reflection
makes both signs have the same H. No assertion that these vectors are in the
operator domain is needed. The qualitative argument (E) does not depend on
this additional rate estimate.

The spectral inequality

    t^2/(t+C)^2 <= t/(4C),       t>=0,

and `L R_L-I = -S(S+C)^(-1)-ell(S+C)^(-1)` prove

    delta_a := ||(L R_L-I)h_±||_2
       <= sqrt(H_a)/(2 sqrt(C)) + |ell| N_a/C.                    (G)

This estimate keeps the spectral lower bound and inverse dependence visible.
Define the nonvanishing entire gauges

    Z_pi = [L exp(i a z)/(-2i sinh a)] W_pi,
    Z_0  = [L exp(i a z)/( 2i cosh a)] W_0.

The corresponding free values are exactly `1+exp(2i a z)` and
`1-exp(2i a z)`. For `Im z>=eta>0`, `|z|<=R`, Cauchy–Schwarz and

    exp(-a Im z) ||exp(-i conjugate(z)x)||_2
       = sqrt((1-exp(-4a Im z))/(2 Im z)) <= 1/sqrt(2 eta)

give the explicit sufficient bound

    |Z_pi-(1+exp(2i a z))| <= B(a,R,eta) delta_a,
    |Z_0 -(1-exp(2i a z))| <= B(a,R,eta) delta_a,

    B(a,R,eta)=(R+1)/(sinh(a) sqrt(2 eta)).                         (H)

For `a=n`, use `eta=1/n`, `R=sqrt(2)n`, and denote the resulting B by `B_n`.
It suffices to choose

    C_n >= max(1, 2|ell_n|, H_n n^2 B_n^2,
                    2 |ell_n| N_n n B_n),
    L_n=C_n-ell_n,

with an additional harmless strict increase if needed to make `L_n>0`.
Equations (G)–(H) then give errors at most `1/n` on that compact exhaustion.
For any fixed upper-half-plane compact, `exp(2i n z)->0`; hence

    Z_pi,n -> 1,         Z_0,n -> 1,
    m_n = i coth(n) Z_0,n/Z_pi,n -> i.                             (I)

This is a counterexample in the exact source objects to automatic safe-region
identification. It even respects the canonical normalization `m_n(i)=i` for
every n. In terms of Corollary 1.6, the explicitly displayed permitted analytic
gauge for W_pi produces the locally uniform limit 1, whereas the proposed
zeta target is the nonconstant function (D).

The W_pi gauge is literally of the permitted form `exp(phi_a(z))`, with

    phi_a(z)=log(L_a/(2 sinh a)) + i pi/2 + i a z,

which is entire. Thus the normalization used in this counterexample requires
no analytic extension assumption.

## 4. Why choosing epsilon small does not supply the missing estimate

The opposite choice retains a different uncontrolled term. Let `P_a` project
onto the lowest eigenspace of `A_a` and let `d_a>0` be the gap to the next
distinct eigenvalue. Compact resolvent gives the exact expansion

    R_(a,epsilon) = epsilon^(-1) P_a + R_perp,
    ||R_perp|| <= 1/(d_a+epsilon).                                (J)

Consequently each deficiency transform has the explicit component

    F[R_(a,epsilon)h_±](z)
      = epsilon^(-1) F[P_a h_±](z) + F[R_perp h_±](z),

and the remainder is bounded by

    |F[R_perp h_±](z)| <= N_a ||exp(-i conjugate(z)x)||_2/(d_a+epsilon).

Neither the residue `F[P_a h_±](z)` nor its relation to `epsilon,d_a,a` is
controlled by the Euler-product identity (B). The inverse amplifies this
residue; positivity does not remove it.

For illustration with the **actual spectral objects**, if at a particular a
the ground eigenvalue is simple, with a real even eigenfunction psi and
`b=<h_+,psi> != 0`, reflection gives `<h_-,psi>=b`. As `epsilon->0` at that
fixed a, the leading W terms are

    W_pi ~ -2i b Fpsi(z)/epsilon,
    W_0  ~  2z b Fpsi(z)/epsilon,

so `m_(a,epsilon)(z)->z` wherever the leading transform is nonzero. For a simple
odd ground eigenfunction and nonzero overlap the analogous limit is `-1/z`.
These conditional formulas do not assert unknown parity/overlap properties at
large a; they identify precisely what would need to be controlled or canceled.
Theorem 1.4 supplies simple even ground states only at sufficiently small a.

For any two admissible positive gaps the shift dependence is exactly

    R_epsilon - R_delta = (delta-epsilon) R_epsilon R_delta.        (K)

On deficiency matrix elements the norm-only bound is proportional to
`|delta-epsilon|/(epsilon delta)`. Thus no shift-independence conclusion follows
from the finite positivity estimate `T>=epsilon I`. Formula (J) shows the
concrete spectral term responsible for its deterioration.

## 5. Outcome of the safe-region attack

The Euler product does give an unconditional analytic target on `Im z>1/2`.
It does not identify the resolvent matrix elements defining the finite-a
boundary characteristic. The canonical Herglotz functions eliminate arbitrary
normalization and exhibit an admissible actual shift sequence with a different
limit there. For a near-ground shift, (J) is the concrete uncontrolled residue.

An analytic-continuation argument could start only after proving a quantitative
comparison between the selected shifted resolvent matrix elements and (B) on
the safe open region. No such comparison was obtained here. Normal-family
compactness alone is insufficient, as (I) shows. Allowing arbitrary gauges on W
does not fix this: one can arrange a local logarithmic gauge to match any
nonzero safe-region function, but extending and controlling that gauge on the
whole upper half-plane is additional information. No global identity, sign
estimate, or unconditional RH proof follows from this attempt.
