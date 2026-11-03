# Independent review of the actual inverse-transport attempt

2026-11-03. Verdict: the fixed-shift and uniform recent-history
obstructions are mathematically correct as stated. No correction is
needed in RECENT_HISTORY_INVERSE_OBSTRUCTION.md or
UNIFORM_RECENT_HISTORY_OBSTRUCTION.md. This is a bounded written
review, not an analytic Lean replay or a proof of the remaining sign.

## Sign and endpoint checks

For continuous f of exponential order, the forward transform has

    Laplace(T_a f)(s)=((s+a)^2/s^2) Laplace(f)(s+a)

on a sufficiently far-right half-plane. The factors cancel on composition,
so Laplace uniqueness proves T_b T_a=T_(a+b). Applying T_-a therefore
gives precisely the printed inverse, with coefficients -2a and +a^2.
All finite-interval integrals exist for the actual Psi. Differentiating
T_eta at eta=0 gives -t f(t)+2integral_0^t f(u)du, confirming the sign
of the first omega variation independently of a zero-series argument.

The source singularity is Psi(t)=O(t log(1/t)), not a nonintegrable
function singularity. Its derivative is O(log(1/t)); the variation has
zero value and derivative at zero. In the curvature formula the factor
t cancels the 1/t singularity. Thus the integration constants and the
ordinary integral used in OMEGA_VARIATION_ATTACK.md are correct.

The unconditional PNT bound gives, at the borderline a=1/2,
|exp(-t/2)Psi(t)|<=C exp(-c sqrt(t)) for large t. Every polynomial
weight is integrable. This simultaneously justifies the affine-tail
expansion, its first moment, the endpoint a downarrow1/2, and the
derivative identity for that moment. In particular the endpoint step
does not use an unproved power-saving estimate or RH.

Writing L=xi'/xi, differentiation of A_a=L(1/2+a)/a^2 gives

    -A_a'=2L(1/2+a)/a^3-L'(1/2+a)/a^2.

The resulting intercept is +L', with the printed sign. The strict
positive slope L(s)>0 for real s>=1 follows from the source's
symmetrized zero expression: each real-part numerator s-Re(rho) is
positive, and the real-part sum converges by inverse-square zero
summability. This uses only the strict zero-free boundary Re(rho)<1.

## Fixed and uniform limits

For fixed a, F_a(t-v)/t tends uniformly to c_a on0<=v<=2/a.
An o(1) remainder is uniformly small on the entire shifted finite
interval once t is large. The weight is bounded and integrable there,
so the displayed recent-history limit is valid without a hidden
dominated-convergence hypothesis.

The uniform extension also checks. On a in[1/2,1], the proposed
majorant follows from2a<=2 and a^2<=1 and tends to zero by the
absolutely integrable first moment of exp(-u/2)Psi(u). For a>=1,
b=a-1/2 satisfies a/b<=2. Exact exponential-tail integration gives
the factor1+2a/b+(a/b)^2<=9. Thus the remainder is uniformly o(1).

Continuity and positivity of L on[1,infinity), together with L(s)
tending to infinity, give a positive infimum m. Continuity of L'
at1 and its independently justified O(1/s) asymptotic give a finite
uniform intercept bound D. No monotonicity of L is being assumed.

For w_a(v)=exp(-av)(2a-a^2v) on[0,2/a], both moments are correct:

    integral w_a=1+exp(-2), integral v w_a=4exp(-2)/a.

Since2/a<=4, setting epsilon(t)=sup_(a>=1/2,u>=t)|R_a(u)| gives

    |B_a(t)/(c_a t exp(at))+exp(-2)|
       <=exp(-2)(8+D/m)/t
           +(2+exp(-2))epsilon(t-4)/(m t).

This tends to zero uniformly in all a>=1/2. Hence one T makes every
B_a(t) negative for all t>=T, including an arbitrary adaptive a=a(t).

The positive old-history term has the compensating fixed-a scaled
limit +exp(-2)c_a. This can also be checked directly: F_a(u)<=C_a(1+u)
globally, and exp(-av)(a^2v-2a) is integrable on v>=2/a. Extending the
integrand by zero for v>t gives an integrable majorant for
F_a(t-v)/t. Its limiting integral is
c_a integral_2^infinity exp(-w)(w-2)dw=exp(-2)c_a.

## Exact remaining signed budget

Keeping the full history, the backward sign requires the following
specific bound for the actual known-positive F_a:

    integral_0^min(t,2/a) exp(-av)(2a-a^2v)F_a(t-v)dv
      <= F_a(t)
          +integral_(2/a)^t exp(-av)(a^2v-2a)F_a(t-v)dv,        (R)

where the older integral is zero if t<2/a. Both integrals in(R) have
nonnegative kernels on their stated ranges. Dropping the older term
is precisely the attempted sufficient bound that the reviewed actual
asymptotic disproves. No sign proof of the full budget(R) was obtained.

More explicitly, let F_a(t)=c_a t+d_a+R_a(t), and set
K_a(v)=exp(-av)(a^2v-2a). Linearity of the exact inverse gives

    Psi(t)=d_a+(c_a-a d_a)t
       +exp(at)[R_a(t)+integral_0^t K_a(v)R_a(t-v)dv].          (S)

The affine identity here is exact, not asymptotic: T_-a(1)=1-at
and T_-a(t)=t. Thus the explicit missing residual estimate is

    R_a(t)+integral_0^t K_a(v)R_a(t-v)dv
       >=-exp(-at)[d_a+(c_a-a d_a)t].                          (S+)

The proved absolute remainder estimates provide no signed version of
(S+). Exponential amplification retains exactly the original PNT-scale
uncertainty. Furthermore F_a''=exp(-at)Psi'' shows that undoing the
shift restores the original continuous archimedean curvature and
negative prime-power jumps with their original magnitudes. The jump
formula does not itself add a favorable term to(S+) or(R).

These are residual arithmetic inequalities, not an additional proof
of an RH equivalence. They retain the full positive old history and
state what this inverse attempt has not bounded. Other possible
backward inequalities or choices of a proof route are not excluded.

## Separate bounded resolvent review

A separate tool-spawned agent, `/root/analytic_audit/resolvent_limit_check`,
checked the complex-parameter and local-uniform passages in
RESOLVENT_SAFE_REGION_ATTACK.md, excluding
the free formula and constants already checked by the root. No
correction was found. The inverse is at a fixed admissible real shift;
complex z enters through finite-interval exponentials, so those scalar
elements are entire. Strong convergence at fixed interval upgrades to
local-uniform convergence on each fixed compact by the displayed L2
bound. The diagonal argument does not claim convergence on its moving
exhaustion. The near-ground limits remain conditional on the stated
overlap/parity assumptions; operator-norm blowup alone gives no scalar
obstruction when the relevant projected vector vanishes. No uniform
control in interval width was inferred.

The actual delegation used `collaboration.spawn_agent` with
`task_name="resolvent_limit_check"` and `fork_turns="none"`; a subsequent
`collaboration.list_agents` call confirmed that canonical ID as completed
with the quoted review. DELEGATED_RESOLVENT_REVIEW_RECORD.json preserves
an explicitly labelled transcript of that observed tool result. It is
not a signed runner receipt, a separate mathematical foundation or a
human-review claim.

## Scope

No new numerical run was needed for this review. The actual initial
256-bit omega check and root's384-bit replay are separate executions
of the same frozen checker, not distinct interval foundations. Their
finite scope remains separate from these written inverse arguments.
No usage or tool limit prevented the bounded review; the remaining
unproved item is the signed mathematical budget, not execution.
