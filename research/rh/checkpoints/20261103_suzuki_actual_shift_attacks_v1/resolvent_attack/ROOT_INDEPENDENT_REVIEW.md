# Independent review of the two Suzuki attacks

2026-11-03. Reviewer: root execution agent, separately from the authors of the
two arguments. This is an ordinary mathematical review, not a Lean replay.

## Resolvent construction

I checked the formulas against Sections 6.2--6.3 and Theorem 1.5 of
Suzuki, arXiv:2606.09096v3, and checked the normalization against the two
boundary expressions in Section 7.8. The latter section's global model is
conditional in the source; only its algebra is used to name the candidate.

The two deficiency vectors are indeed `(A_a-lambda)^(-1)exp(+-x)`.
Reflection preserves their form norms. The source theorem for every boundary
phase makes `P/Q` a Schur function: along a path from `i` a pole or a value of
modulus at least one would force a unit-modulus value, and hence a forbidden
nonreal zero for one boundary phase. Therefore `-i W_0/W_pi` is Herglotz and
equals `i` at `i`. The normalization is not inferred from a free gauge on one W.

I recomputed the free transforms. They give

    L W_pi -> -4 i sinh(a) cos(a z),
    L W_0  ->  4 cosh(a) sin(a z).

Multiplication by the respective gauges in the argument gives exactly
`1+exp(2iaz)` and `1-exp(2iaz)`. Consequently the quotient is
`coth(a)tan(az)` and tends to `i` locally uniformly in the upper half-plane.
All signs and the derivative factor `d xi(1/2-iz)/dz=-i xi'(1/2-iz)` agree.

For the explicit diagonal choice, put `S=A_a-ell >= 0` and `C=L+ell`.
The scalar inequality `t^2/(t+C)^2 <= t/(4C)` follows from
`(t-C)^2>=0`. Its spectral integral gives the stated square-root form bound.
The other term is bounded by `|ell| ||h||/C`. With the displayed choice of
`C_n`, each contribution to the gauged transform error is at most `1/(2n)`.
The compact exhaustion contains every fixed upper-half-plane compact
eventually. The free denominator tends uniformly to one there, so division
is justified eventually. The finite form energy of the truncated exponentials
also follows from their membership in `H^s(R)` for any `0<s<1/2`, which dominates
the logarithmic Fourier weight; smooth interior cutoffs approximate in the
logarithmic form norm. No unsupported operator-domain membership is needed.

The small-gap expansion is the spectral projection decomposition. In the
conditional simple-even case it gives quotient limit `z`; in the simple-odd
case it gives `-1/z`. The document correctly refrains from asserting unknown
large-a parity or overlap conditions.

Conclusion: the actual large-shift counterexample and its quantitative
diagonal argument are valid given the cited finite-a spectral theorem. They
reject automatic safe-region identification for arbitrary admissible shifts.
They do not disprove the existence of a carefully selected shift sequence.

## Omega derivative

I checked the exact semigroup formula directly in Section 11 of
Suzuki, arXiv:2206.03682v4. Differentiation at zero of the extra shift gives
`partial_omega F_omega=2 integral_0^t F_omega(u)du-t F_omega(t)`.
Twice differentiating the original transform cancels its first-derivative
terms and leaves `F_omega''=exp(-omega t)Psi''` away from prime activations.
The distributional prime signs therefore give upward slope jumps in the
omega derivative, exactly as reported.

For `x=exp(t)`, the source arithmetic curvature simplifies to

    h(t)=(x^3-x-1)/(sqrt(x)(x^2-1)).

It is negative before the positive root greater than one. The factor `u`
in the variation integral removes the curvature singularity at zero; the
other factor `t-u` makes the resulting integral strictly positive there for
every real omega. This is an actual-function analytic counterexample to
descending omega monotonicity. It does not depend on the numerical samples.

I independently integrated the odd-exponential expansion in the half-shift
formula: each term contributes `t/b^2-2/b^3+exp(-bt)(t/b^2+2/b^3)`.
The sums of odd reciprocal squares and cubes and the remaining Lerch terms
match formula (10). The geometric upper bound in (11) covers every omitted
term. The checker adds a symmetric Arb ball containing the positive tail,
which is conservative. At the exact activation, a small ball around the
identically zero prime term remains conservative.

I actually replayed the authored checker at 384 bits, separately from the
author's 256-bit execution. Command:

    PYTHONPATH=/workspace/aegis-nov2-runtime/arb-python python3 /workspace/aegis-nov3-suzuki/omega_attack/omega_variation_enclosure_v1.py --precision 384 --output /workspace/aegis-nov3-suzuki/omega_attack/OMEGA_VARIATION_ROOT_REPLAY_384.json

Exit status was zero. All five positive derivative bounds and both
one-sided slope signs were reproduced. This is a second execution of the
same numerical checker with higher precision, not a second implementation
and not a Lean proof. The written analytic derivation was reviewed separately.

## RH scope

Neither attack supplies the unshifted global sign. No final RH theorem,
kernel closure, or global mathematical impossibility follows. The existing
globalization theorems and all their quantified conclusions remain intact.
