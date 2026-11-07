# Exact polynomial witness: analytic meaning and replay scope

This is an ordinary analytic proof of the formula evaluated by
`check_exact_witness.py`, not a Lean theorem or an unconditional proof of RH.
The pinned Claude source and its original output are preserved unchanged.
The independent calculation uses the same Arb library, but a different
algebraic/integration implementation. It is not an independent proof kernel.

## Objects and quantifiers

Fix a positive rational a <= 3/2 and a nonzero real polynomial

    v(y) = psi(y)/4 - psi''(y)/a^2,
    psi(+/-1) = psi'(+/-1) = 0.

Let H(x)=v(x/a) for |x|<a and zero otherwise; endpoint values are immaterial.
The potential Psi(x)=psi(x/a), extended by zero, is C^1 and piecewise smooth.
Thus H=(1/4-D^2)Psi as distributions: the clamped conditions remove both
possible delta distributions at the endpoints. Integration by parts gives

    M_sigma(H)=integral exp(sigma*x)H(x) dx
             =(1/4-sigma^2) integral exp(sigma*x)Psi(x) dx = 0

for sigma=+/-1/2. This is an exact identity, not the numerical observation
that two interval moment enclosures contain zero. H is nonzero and has
positive exact rational norm E=integral |H|^2.

Use the angular Fourier convention Hhat(t)=integral H(x)exp(-itx) dx.
The actual source two-moment form is

    Q(H)=(1/(2*pi)) integral w(t)|Hhat(t)|^2 dt
         -2 sum_(m>=2) Lambda(m)/sqrt(m) C_H(log m),
    w(t)=Re digamma(1/4+it/2)-log pi,
    C_H(z)=integral H(x)H(x+z) dx.

All functions here are real. The extension to complex test functions in the
RH criterion is not supplied by this one real witness. Its purpose is an
upper bound for a variational infimum, not positivity of an entire class.

H is compactly supported and of bounded variation, so Hhat(t)=O(1/|t|).
Consequently it belongs to the logarithmic form domain
X with norm squared integral log(2+|t|)|Hhat(t)|^2 dt. The full Archimedean
integral is absolutely convergent; the multiplier is bounded in absolute
value by C+log(2+|t|). The real-space identity used below is the same full
Archimedean identity documented in PROOF_COMPOSITION.md and the source
digamma/explicit-formula modules. No fixed-frequency cutoff is introduced.

## Exact correlation, arithmetic cutoff, and integral

For 0<=tau<=2, define

    r(tau)=integral_(-1)^(1-tau) v(y)v(y+tau) dy.

Taylor's formula for a polynomial is finite and exact. Substituting
v(y+tau)=sum tau^k v^(k)(y)/k! and integrating each polynomial gives exactly
the `correlation` polynomial in the checker. Hence

    C_H(a*tau)=a*r(tau), r(0)=E/a, r(2)=0.

For z>=2a the correlation is zero. Therefore all prime-power terms with
log m>=2a are zero, including a possible endpoint term. For the four
replayed radii the strict inequalities N<exp(2a)<N+1 are certified by Arb;
N=4,7,12,20 respectively. Integer trial division enumerates every prime
power <=N, with Lambda(p^k)=log p. No asymptotic prime estimate is needed.

Put h(tau)=(r(tau)-r(0))/tau, an exact polynomial, and C0=log(4*pi)+gamma.
The full Archimedean identity reads

    Q_arch(H)=-C0*E-I,
    I=integral_0^infinity [exp(z/2)C_H(z)-E]/sinh z dz.

The integrand is bounded near zero because C_H(z)-E=O(z). At infinity,
C_H(z)=0 and 1/sinh z is integrable. Split at 2a, using
integral_(2a)^infinity 1/sinh z dz=-log tanh a. Then

    I=a*J+2E*nu+E*log tanh a,
    J=integral_0^2 h(tau) exp(a*tau/2)/sinc(i*a*tau) dtau,
    nu=integral_0^(2a) exp(z/4)sinc(i*z/4)/(4*sinc(i*z)) dz,
    sinc(z)=sin(z)/z, sinc(0)=1.

The substitution uses sinh z=z*sinc(i*z), and
(exp(z/2)-1)/(2*sinh z)=exp(z/4)sinc(i*z/4)/(4*sinc(i*z)).
It follows that the exact expression evaluated is

    Q(H)=-[C0+log tanh a]E-a*J-2E*nu
         -2a sum_(2<=m<=N) Lambda(m)/sqrt(m) r(log m/a).

This includes the infinite Archimedean tail analytically, all arithmetic
terms, and the polar contribution (exactly zero by the two moments).
There is no omitted quadrature tail or unpriced support extension.

Both integrands after regularization are meromorphic functions of the
complex integration variable; their apparent zero singularities have been
removed. The other denominator zeros are isolated off the real segments.
Arb's analytic integration callback is valid on every region where it
returns a finite enclosure; division over a region containing a pole
returns a nonfinite ball and forces subdivision/failure. The explicit
finite-result checks prevent a nonfinite integral being called certified.
The callbacks contain no log or square-root branch choice. Real logarithms
and square roots in the external constants have positive arguments.
This relies on the documented soundness of python-flint/Arb, not on a
Lean verification of that implementation.

## SAME-support smooth approximation

The upper bound also applies to the infimum over the original smooth legal
test class, without increasing a. Choose smooth cutoffs chi_delta inside
(-a,a), equal to one except in endpoint layers of width O(delta), with
|chi_delta^(j)|<=C_j delta^(-j). Define

    H_delta=(1/4-D^2)(chi_delta*Psi).

Each H_delta is smooth, supported strictly inside [-a,a], and has both
moments zero by the same exact integration by parts. At the endpoints,
Psi=O(dist^2) and Psi'=O(dist). Thus u_delta=H_delta-H is supported in
layers of total length O(delta), has uniformly bounded amplitude, and has
uniformly bounded total variation, including its endpoint jumps. Hence

    |uhat_delta(t)| <= min(C*delta, C/|t|).

Integration over |t|<=1/delta and its complement proves

    ||u_delta||_X^2 = O(delta*(1+log(1/delta))) -> 0.

The logarithmic multiplier bound gives convergence of the complete
Archimedean form. There is one fixed finite prime-power set for the common
support [-a,a]; correlation convergence follows from

    |C_F(z)-C_H(z)| <= ||F-H||_2 (||F||_2+||H||_2).

Therefore Q(H_delta)->Q(H) and ||H_delta||_2^2->E>0. In particular the
infimum of Q(F)/||F||_2^2 over nonzero smooth functions with the two moments
and support [-a,a] is <=Q(H)/E. The inverse logarithmic lift makes these
actual compact-positive smooth Weil packets. This does not prove that
infimum is nonnegative, and a positive trial value is not a lower bound.

## Outward bound and the printing defect

The original `R.upper().str(6, radius=False)` prints a nearest decimal;
it need not round upward. For example it prints 1/3 as 0.333333. At a=3/4
the printed 7.67846e-10 is strictly below the enclosed trial quotient
7.678460751097...e-10. The same problem occurs for the original a=3/2
printed bound. This does not refute an upper bound for the infimum: the
infimum could be smaller. It does mean those literal decimals do not
follow from the displayed witnesses as directed upper bounds.

The new checker extracts the exact dyadic upper endpoint and explicitly
rounds UP to a rational with denominator 10^80. It verifies the resulting
strict inequality using ball arithmetic. Raw input, checker and receipt
hashes bind the computation. The original source and output are untouched.

The actual receipt records 800-bit precision, 2^-700 integration tolerances,
all prime-power indices and an exact rational upper bound. It does not
claim a lower bound, simple eigenvalue, spectral completeness, global
positivity, a Lean analytic soundness theorem, or RH closure.
