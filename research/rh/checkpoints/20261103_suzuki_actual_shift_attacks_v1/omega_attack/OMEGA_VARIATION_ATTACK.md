# Exact omega variation of the actual Suzuki family

Date: 2026-11-03. The descending monotonicity
`partial_omega Psi_omega(t)<=0`, which would transfer known positivity
at omega=1/2 directly to omega=0, is false for the actual function.
This is proved analytically below and checked with rigorous finite Arb
enclosures at the boundary and first prime activation. No RH sign
assumption, toy function or new RH-equivalence proof is used.

## Source and exact variation

The source is Suzuki, arXiv:2206.03682v4, equations(1.1),(11.1),(11.2)
and Section11, read in SUZUKI_2206_03682v4.txt. The PDF SHA256 is
eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41.
The existing SUZUKI_SOURCE_COMPOSITION.md was read; its derivative
correction is not redone here. Write F_omega=Psi_omega on t>=0, retaining
the source's even extension only when discussing the whole real line.

On each finite t interval, differentiating(11.1) in omega is justified
by continuity of Psi and bounded exponential weights. The source's
composition law T_eta T_omega=T_(omega+eta), differentiated at eta=0,
gives the exact first variation

    G_omega(t):=partial_omega F_omega(t)
       =2 integral_0^t F_omega(u)du-t F_omega(t).                 (1)

This also follows by direct differentiation of(11.1). Differentiating
twice in t away from prime activations, or distributionally on t>0,
gives

    F_omega''(t)=exp(-omega*t)Psi''(t),
    G_omega''(t)=-t exp(-omega*t)Psi''(t).                       (2)

The source's exact arithmetic definition yields

    Psi''=h(t)-sum_(n>=2) Lambda(n)/sqrt(n) delta_(log n),
    h(t)=2cosh(t/2)-exp(t/2)/(2sinh t).                         (3)

For example the Lerch contribution is
(1/4)sum_(j>=0)[1-exp(-(2j+1/2)t)]/(j+1/4)^2; twice differentiating
on a compact positive t interval gives
-sum_j exp(-(2j+1/2)t)=-exp(t/2)/(2sinh t). The differentiated
series converge uniformly there. The linear digamma/log(pi) term
has second derivative zero. Every actual prime power and its exact
von Mangoldt weight is retained in(3).

Near zero, h(t)=-1/(2t)+7/4+O(t). Thus Psi=O(t log(1/t)), its first
derivative is O(log(1/t)), and(1) has G_omega(0)=G_omega'(0)=0.
Multiplication by t makes the singularity in(2) integrable. Integrating
(2) twice therefore gives the convergent exact arithmetic variation

    G_omega(t)=
      -integral_0^t (t-u)u exp(-omega*u)h(u)du
      +sum_(n<=exp t) Lambda(n)log(n)n^(-1/2-omega)(t-log n).    (4)

The prime sum is finite for every t. This identity needs no Euler
product outside its domain, zero-series limit, or RH assumption.

## An unconditional actual-function counterexample to descending monotonicity

Set x=exp(t). Direct algebra in(3) gives

    h(t)=(x^3-x-1)/(sqrt(x)(x^2-1)).                            (5)

There is a unique rho>1 satisfying rho^3-rho-1=0: the polynomial is
strictly increasing on x>=1, is negative at1 and positive at2. Hence
rho<2 and h(t)<0 on0<t<log(rho)<log2. No prime has activated in this
interval. The integral in(4) consequently proves

    partial_omega Psi_omega(t)>0
    for every real omega and every0<t<=log(rho).                 (6)

The endpoint also has strict positivity because its integrand is
strictly positive on0<u<t. In particular(6) holds throughout the
requested omega interval[0,1/2]. This is a full analytic counterexample
to the proposed nonpositive derivative, using the actual arithmetic
function rather than an arbitrary input to T_omega.

For a second consistency check, expansion of(4) gives

    G_omega(t)=t^2/4-(7+2omega)t^3/24+O(t^4),                   (7)

uniformly on compact omega intervals, in particular[0,1/2]. The leading
positive coefficient agrees with(6). This asymptotic is not needed for
the exact sign proof.

## Actual prime activations

At a=log n, G_omega is continuous. Its one-sided t derivatives satisfy

    G_omega'(a+)-G_omega'(a-)
       =a Lambda(n)n^(-1/2-omega).                             (8)

Thus prime powers cause upward slope jumps, not the nonpositive
correction that a descending omega comparison would need. There is
no jump at an integer that is not a prime power. Between activations,
(2) and(5) show G_omega''<0 once t>log(rho). This describes the actual
signed curvature and jump structure; it does not assert a global
sign for G_omega.

At omega=1/2, (4) becomes

    G_(1/2)(t)=integral_0^t u(t-u)
                    [1/(2sinh u)-1-exp(-u)]du
              +sum_(n<=exp t) Lambda(n)log(n)/n (t-log n).      (9)

To evaluate it without quadrature or an uncontrolled infinite tail,
put L_s(t)=sum_(j>=0)exp(-2jt)/(j+1/2)^s. Elementary integration of
the three terms in(9) gives

    G_(1/2)(t)=
       -t^3/6-t(1+exp(-t))+2(1-exp(-t))
       +pi^2 t/8-7 zeta(3)/4
       +(exp(-t)/4)[t L_2(t)+L_3(t)]
       +sum_(n<=exp t) Lambda(n)log(n)/n (t-log n).             (10)

For the archimedean integral, expand1/(2sinh u)=sum_(j>=0)
exp(-(2j+1)u). Tonelli applies to u(t-u)>=0. The elementary integral
of each summand is t(1+exp(-bt))/b^2-2(1-exp(-bt))/b^3. Summing
b=2j+1 uses sum_(odd b)b^-2=pi^2/8 and sum_(odd b)b^-3=7zeta(3)/8,
which yields exactly(10). This independently derives its normalization.

With N terms, the positive omitted Lerch tail has the explicit bound

    0<=L_s(t)-sum_(j<N)q^j/(j+1/2)^s
       <=q^N/[(N+1/2)^s(1-q)], q=exp(-2t).                    (11)

## Executed rigorous numerical checks

The newly authored omega_variation_enclosure_v1.py implements(10)--(11)
with256-bit python-flint Arb balls and N=512. It checks the source PDF
hash, validates each point's prime window and uses explicit exception
gates, not removable Python assertions. No archived program was executed.
Its actual source SHA256 is
6bdc4560592ce87002dee0205334ab04c57556371c3b79c9fd3bf75dc96e7029.

All five resulting lower bounds are strictly positive:

| exact t, omega=1/2 | G_(1/2)(t), shortened display |
| --- | --- |
|1/10|0.00217406133726491656175|
|1/2|0.02491098287703608703879|
|log2-1/1000|0.02337608864123358251189|
|log2|0.02332034750460255576761|
|log2+1/1000|0.02350425525232485627334|

Full outward balls and tail bounds are in OMEGA_VARIATION_RECEIPT.json.
The largest displayed radius among these rows is less than3.6e-51.

Differentiating(10) in t at the first activation gives left slope

    -t^2/2-1+(t+1)exp(-t)+pi^2/8
       -(exp(-t)/4)L_2(t)-(t exp(-t)/2)L_1(t), t=log2.

The right slope adds(log2)^2/2. The same interval implementation proves

    left =-0.0560297384466920776580... <0,
    right= 0.1841967685124086346755... >0,
    jump = 0.2402265069591007123336... .

Thus at omega=1/2 the positive omega derivative has a strict local minimum
as a function of t at the first prime activation. The sign behavior is
resolved on both sides; no plain floating-point sign was promoted.

Actual successful command, exit0:

    PYTHONPATH=/workspace/aegis-nov2-runtime/arb-python python3 /workspace/aegis-nov3-suzuki/omega_attack/omega_variation_enclosure_v1.py --output /workspace/aegis-nov3-suzuki/omega_attack/OMEGA_VARIATION_RECEIPT.json

The first attempt with the default Python import path failed with
ModuleNotFoundError for flint. The already available approved local
python-flint installation above resolved that execution issue. It was
not a mathematical failure. The successful stdout is OMEGA_VARIATION_RUN.log.
No installation, network access or permission increase was used.

## Diagnostics and remaining mathematical limit

A separate newly handwritten floating-point sweep tested omega=0,0.1,0.25,
0.5 and0.02<=t<=10 in steps0.002, retaining actual prime powers. It observed
no negative first omega derivative. That sweep has no certified error
or global force; it is only a diagnostic. It does not prove global
nonnegative omega variation, and such increasing monotonicity would
still give the opposite order to a direct descent from omega=1/2.

The exact formula(1) supplies no scalar maximum principle for backward
omega transport: it couples the value at t to the whole interval[0,t].
This audit has not disproved every possible differential inequality.
An inequality strong enough for backward positivity would need its own
signed bound for the actual integral/prime expression(4), not the already
known positivity at omega>=1/2. No such bound, no analytic Lean replay,
and no proof of Psi_0's global sign is claimed here.
