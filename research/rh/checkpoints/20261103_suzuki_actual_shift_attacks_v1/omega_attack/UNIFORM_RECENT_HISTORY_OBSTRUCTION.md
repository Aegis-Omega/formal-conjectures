# Uniform failure of the recent-history inverse bound

2026-11-03. This strengthens the fixed-shift result in
`RECENT_HISTORY_INVERSE_OBSTRUCTION.md`. It concerns the same actual
Suzuki arithmetic functions, not a toy family. It is an ordinary analytic
argument, with no RH assumption or numerical sign decision.

Use the earlier notation

    F_a=Psi_a, a>=1/2,
    c_a=L(1/2+a), d_a=L'(1/2+a), L=xi'/xi,
    B_a(t)=exp(at)F_a(t)
      -integral_(max(0,t-2/a))^t exp(au)[2a-a^2(t-u)]F_a(u)du.

The stronger assertion is

    exists T, forall a>=1/2, forall t>=T, B_a(t)<0.             (U)

In particular, choosing a time-dependent shift a(t)>=1/2 does not repair
this particular recent-history lower-bound proof. It says nothing against
the full inverse transform with its retained positive older contribution.

## Uniform affine remainder

Put `f_a(u)=exp(-au)Psi(u)`. The exact remainder in the previous argument is

    F_a(t)=c_a t+d_a+R_a(t),
    R_a(t)=f_a(t)-2a integral_t^infinity f_a(u)du
                         +a^2 integral_t^infinity(u-t)f_a(u)du. (1)

The unconditional source PNT estimate supplies constants C,k>0 and T0 with

    |f_(1/2)(u)|<=C exp(-k sqrt(u)), u>=T0.                    (2)

For `1/2<=a<=1`, use `|f_a(u)|<=|f_(1/2)(u)|`, `2a<=2`, and `a^2<=1`.
For t>=T0 this gives

    |R_a(t)| <= |f_(1/2)(t)|
          +2 integral_t^infinity |f_(1/2)(u)|du
          +integral_t^infinity (u-t)|f_(1/2)(u)|du =: r_0(t).

The right side tends to zero, independently of a in this interval: the
source bound is pointwise decaying and has an absolutely integrable first
moment. For `a>=1`, put `b=a-1/2>=a/2`. In (1)--(2) one may bound
`exp(-k sqrt(u))<=exp(-k sqrt(t))` when u>=t, and integrate the remaining
exponentials exactly. Consequently

    |R_a(t)| <= C exp(-bt-k sqrt(t))[1+2a/b+a^2/b^2]
               <=9C exp(-k sqrt(t)).

It follows that

    sup_(a>=1/2)|R_a(t)| <= r(t):=r_0(t)+9C exp(-k sqrt(t)) ->0. (3)

No constants in this last bound depend on a.

## Uniform slope and intercept bounds

The symmetrized Hadamard expression proves `L(s)>0` for every real s>=1,
using only the known strict zero-free boundary. L is continuous there.
On the positive real axis, the absolutely convergent Euler-product series
and the digamma asymptotic give

    L(s)=(1/2)log(s/(2pi))+O(1/s) -> infinity,
    L'(s)=1/(2s)+O(1/s^2) ->0.

For the second estimate use the differentiated digamma expansion and
the absolutely convergent derivative of the Dirichlet series on s>=2;
it is not inferred by differentiating an unspecified O remainder.
Compactness on bounded intervals therefore supplies constants m>0 and D<infinity
with

    c_a>=m,              |d_a|<=D,              for all a>=1/2. (4)

At s=1 the canceled zeta pole causes no singularity in xi or L. The endpoint
transform and derivative were justified by dominated convergence in the
fixed-shift argument.

## Uniform negative sign

For t>=4 all the cutoffs satisfy `t>=2/a`. Define

    w_a(v)=exp(-av)(2a-a^2v), 0<=v<=2/a.

This weight is nonnegative. Its two moments are exact:

    integral w_a(v)dv=1+exp(-2),
    integral v w_a(v)dv=4 exp(-2)/a.                            (5)

For the second integral substitute w=av and integrate
`exp(-w)w(2-w)` from zero to two. Insert (1) into the definition of B_a.
The affine terms can be integrated without an asymptotic operation:

    exp(-at)B_a(t)
       =-exp(-2)c_a t+exp(-2)(4c_a/a-d_a)
          +R_a(t)-integral_0^(2/a) w_a(v)R_a(t-v)dv.            (6)

All sampled lags are at most four. Set
`r_star(t)=sup_(s>=t-4) r(s)`, which tends to zero because r(s)->0.
For sufficiently large t, (3)--(6) give the uniform estimate

    | B_a(t)/(c_a t exp(at))+exp(-2) |
       <= exp(-2)(8+D/m)/t
                    +(2+exp(-2))r_star(t)/(m t), a>=1/2.      (7)

The right side tends to zero independently of a. Choose T so it is
less than `exp(-2)/2` for every t>=T. Since `c_a t exp(at)>0`, (7)
proves (U).

## Interpretation and verification scope

This is a global-in-shift obstruction to one proposed proof shortcut.
It preserves rather than contradicts the valid inequality `Psi(t)>=B_a(t)`.
The full older-history term cannot be discarded for this route, even after
an arbitrary adaptive choice of a>=1/2. The exact full signed history budget
has not been proved nonnegative here. This result is not an RH proof or
another RH equivalence. There is no Lean replay of this analytic argument.

Sources are the same pinned Suzuki 2206.03682v4 primary source, Theorem
1.1(1),(3) and Section 11, and the standard Hadamard/logarithmic-derivative
identities used explicitly above. The source PDF identity is recorded in
`SOURCE_MANIFEST.json` in the handoff archive.
