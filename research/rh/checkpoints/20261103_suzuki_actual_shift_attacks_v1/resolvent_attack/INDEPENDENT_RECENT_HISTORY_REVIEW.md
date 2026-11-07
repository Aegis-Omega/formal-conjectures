# Independent review of the recent-history inverse obstruction

Reviewed 2026-11-03 against Suzuki 2206.03682v4, Theorem 1.1(1),(3),
Section 11 (11.1), and its displayed shift-composition law. The original
argument was not modified. No numerical computation or Lean replay was used.

**Assessment: (1)–(5) are valid, including the endpoint a=1/2.** The result
disproves eventual nonnegativity of this particular truncated lower bound for
each fixed admissible shift. It does not disprove positivity of Psi itself.

- **Inverse and lower bound (1)–(2):** Taking omega=a and eta=-a in the
  source's finite-t composition law gives (1) with exactly the displayed
  kernel. The known unconditional nonnegativity of F_a for a>=1/2 makes
  the omitted part with lag greater than 2/a nonnegative. The kernel is
  zero at the cutoff, so including or excluding that endpoint is immaterial.
  For t<2/a no older part exists and B_a=Psi exactly.
- **Integrability and (3):** The source PNT estimate bounds
  `exp(-a t)|Psi(t)|` by `C exp(-c sqrt(t))` for every a>=1/2 at large t.
  Hence all polynomial moments used exist absolutely, including at a=1/2.
  Continuity of Psi handles zero. The claimed vanishing tail follows from
  `t integral_t^infinity |f_a(u)|du <= integral_t^infinity u|f_a(u)|du`.
  The pointwise f_a(t) also tends to zero. These facts justify the o(1)
  remainder in (3), rather than merely an o(t) remainder.
- **Transform, signs, and (4):** Substituting z=i a in source (1.2) gives
  `A_a=L(1/2+a)/a^2` for a>1/2. Differentiation with respect to a gives
  `D_a=-A_a'=2L/a^3-L'/a^2`, so the constant term in (3) is indeed `+L'`.
  As a decreases to 1/2, the same absolutely integrable polynomial-weighted
  majorants justify both limits. Xi is analytic and nonzero at s=1 after
  cancellation of the zeta pole. Thus there is no endpoint singularity or
  illicit use of an Euler-product derivative on its boundary. The source's
  symmetrized Hadamard formula gives c_a>0 for sigma>=1 using the known
  zero-free boundary Re(s)=1. The displayed endpoint constant has the correct
  value and sign; no critical-line assumption is needed.
- **Limit (5):** For fixed a, the lag interval [0,2/a] is fixed. The affine
  asymptotic (4) implies the asserted uniform convergence of
  F_a(t-v)/t there. Its kernel integral is exactly `1+exp(-2)`, yielding
  `-exp(-2)c_a<0`. The source PNT bound also proves the stated zero limit
  for `Psi(t)/(t exp(a t))`, so the omitted older part must cancel the
  negative leading term with precisely the positive coefficient claimed.

The relevant quantifier is

    for every fixed a>=1/2, there exists T(a) such that
    B_a(t)<0 for every t>=T(a).

No uniform threshold over unbounded a is proved, and the argument does not
by itself rule out a separately analyzed time-dependent choice a=a(t).
This is a scope qualification, not a correction to (1)–(5). The conclusion
about the stated fixed-shift recent-history proof is sound. RH remains open.
