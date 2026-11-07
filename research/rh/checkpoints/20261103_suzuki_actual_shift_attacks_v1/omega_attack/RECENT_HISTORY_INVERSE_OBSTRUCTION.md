# The positive old history is essential in the actual inverse transport

2026-11-03. Ordinary mathematical derivation by the root agent.
No RH assumption and no numerical experiment are used.

Let `Psi` be the actual arithmetic function of Suzuki 2206.03682v4, and
write `F_a=Psi_a`, with `a>=1/2`. The positive forward shift and its
semigroup law are the existing equations in Section 11. They imply the exact
inverse formula, for every finite `t>0`,

    Psi(t) = exp(at) F_a(t)
           + integral_0^t exp(au)[a^2(t-u)-2a] F_a(u) du.       (1)

The function `F_a` is unconditionally nonnegative. The integral coefficient
is negative for recent lags `0<t-u<2/a` and positive for older lags `t-u>2/a`.
Consequently discarding the older positive part gives the genuine lower bound

    Psi(t) >= B_a(t),
    B_a(t) = exp(at) F_a(t)
       - integral_(max(0,t-2/a))^t exp(au)[2a-a^2(t-u)]F_a(u)du. (2)

This bound is valid. The attempted proof that its right side is nonnegative
for large t fails for the actual Suzuki function, for every such a.

## Exact unconditional large-t behavior of the shifted function

The unconditional source estimate in Theorem 1.1 has the form

    |Psi(t)| <= C exp(t/2-c sqrt(t))

for sufficiently large t and some positive constants C,c. Thus, when
`a>=1/2`, the function `f_a(t)=exp(-at)Psi(t)` is absolutely integrable
with every polynomial weight. Put

    A_a = integral_0^infinity f_a(u)du,
    D_a = integral_0^infinity u f_a(u)du.

The source's exact forward-shift formula is

    F_a(t)=f_a(t)+2a integral_0^t f_a(u)du
                      +a^2 integral_0^t(t-u)f_a(u)du.

Replacing these integrals by their infinite integrals is justified by the
above absolute bounds. In particular
`t integral_t^infinity |f_a(u)|du` tends to zero. It follows that

    F_a(t)=a^2 A_a t+(2a A_a-a^2 D_a)+o(1).                    (3)

Let `L(s)=xi'(s)/xi(s)` and `sigma=1/2+a`. The unconditional transform in
the same primary source gives, initially for `a>1/2`,

    A_a=L(sigma)/a^2,
    D_a=2L(sigma)/a^3-L'(sigma)/a^2.

At `a=1/2` these identities follow by dominated convergence and the
zero-free property of xi at s=1. The derivative limit is also dominated by
the integrable weight `u exp(-u/2)|Psi(u)|`. Hence (3) becomes

    F_a(t)=c_a t+d_a+o(1),
    c_a=L(1/2+a)>0,       d_a=L'(1/2+a).                       (4)

Strict positivity of c_a is unconditional: in the symmetrized Hadamard
logarithmic derivative, each zero contributes positive real part at real
`sigma>=1`, since every nontrivial zero has real part strictly less than one.
The conjugate pairing makes this real-part sum convergent. Equivalently,
at the endpoint `c_(1/2)=1+gamma/2-log(2 sqrt(pi))>0`. This uses the
established zero-free boundary, not the critical-line assertion.

## The proposed recent-history lower bound is eventually negative

For `t>=2/a`, substitute `v=t-u` in (2) and divide by `t exp(at)`:

    B_a(t)/(t exp(at)) = F_a(t)/t
      - integral_0^(2/a) exp(-av)(2a-a^2 v) F_a(t-v)/t dv.

By (4), `F_a(t-v)/t -> c_a` uniformly on this fixed finite v interval.
Passing to the limit is therefore justified. The exact elementary integral is

    integral_0^(2/a) exp(-av)(2a-a^2v)dv
       = integral_0^2 exp(-w)(2-w)dw
       = 1+exp(-2).

Thus the actual asymptotic sign is

    lim_(t->infinity) B_a(t)/(t exp(at)) = -exp(-2)c_a < 0.    (5)

In particular, for every fixed `a>=1/2` there is a threshold `T(a)` such
that `B_a(t)<0` for all `t>=T(a)`. No uniform threshold over an unbounded
set of a, or assertion about a time-dependent choice `a(t)`, is made. This is an
actual-function counterexample to using the truncated inverse as a positive
lower bound. It is not a counterexample to the full inverse identity, to
`Psi>=0`, or to RH.

The omitted older contribution in (1) is not a small positive error at the
scale relevant here: it cancels the negative leading term in (5). Indeed the
source estimate also gives `Psi(t)/(t exp(at))->0`, so its scaled limit is
exactly `+exp(-2)c_a`. Any viable inverse-transport proof must preserve or
quantitatively control that cancellation. Positivity of F_a by itself does
not pay for it.

## Source and proof scope

Primary source: Suzuki, arXiv:2206.03682v4, Theorem 1.1 and Section 11;
PDF SHA-256
`eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41`.
This written analytic argument was independently reviewed; see
`resolvent_attack/INDEPENDENT_RECENT_HISTORY_REVIEW.md` in the archive.
There is no analytic Lean proof or RH closure in this file.
