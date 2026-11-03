# Independent omega-variation review

Reviewed 2026-11-03 against the actual Suzuki 2206.03682v4 text, Section 11,
(11.1) and its displayed composition law, and the arithmetic definition (1.1).
I read the attack, checker source and saved receipt. I did not modify or run
the checker. The saved PDF and checker hashes match the receipt.

**Assessment: the analytic counterexample to descending omega monotonicity is
correct.** No RH or unproved global sign assumption enters it. The numerical
checker implements the stated finite scope with a conservative series tail.

- **(1)–(2):** Differentiating the source's composition law at `eta=0` gives
  `G_omega=2 integral F_omega-t F_omega`. Direct differentiation of (11.1)
  also gives `F_omega''=exp(-omega t) Psi''` on `t>0`, including the prime
  delta terms distributionally. Therefore its omega derivative is exactly
  the second identity (2). All omega differentiation on bounded t intervals
  is justified by continuity of Psi and bounded exponential weights.
- **(3):** The twice-differentiated Lerch coefficient is exactly `-1` for each
  exponential `exp(-(2j+1/2)t)`. Its sum is
  `-exp(t/2)/(2 sinh t)`. The polar second derivative is `2 cosh(t/2)` and
  each prime-power hinge contributes `-Lambda(n)/sqrt(n) delta_(log n)`.
  Thus the sign and normalization are correct.
- **Endpoint and (4):** `h(t)=-1/(2t)+7/4+O(t)` is correct. Although h itself
  is not integrable at zero, `t exp(-omega t)h(t)` is bounded there. From
  `Psi=O(t log(1/t))`, `Psi'=O(log(1/t))`, equation (1) implies both
  `G(0)=0` and `G'(0)=0` (`G'=F-t F'`). Integrating (2) twice thus yields
  (4) with no missing constant, linear term, or delta contribution at zero.
  The distributional assertion about Psi'' is on `t>0`, so it does not
  wrongly assign a locally integrable whole-line meaning to h at zero.
- **(5) and the sign:** Substituting `x=exp(t)` gives exactly
  `(x^3-x-1)/(sqrt(x)(x^2-1))`. The denominator is positive for x>1 and the
  numerator increases strictly there. Before its unique root, h is negative
  and no prime has activated. Consequently the weighted integral in (4) is
  strictly positive, including at the stated endpoint. This proves the
  counterexample for every real omega, not merely at sampled values.
- **(10):** At omega=1/2 the smooth integrand is
  `u(t-u)[1/(2 sinh u)-1-exp(-u)]`. Its apparent zero-endpoint singularity
  is canceled by u. Tonelli applies to the positive odd-exponential series.
  For b>0 its elementary integral is
  `t(1+exp(-bt))/b^2-2(1-exp(-bt))/b^3`. Summing odd b yields the coefficients
  `pi^2 t/8`, `-7 zeta(3)/4`, and
  `exp(-t)[t L_2+L_3]/4` exactly. The remaining two smooth terms and the
  prime contribution in (10) are correct.
- **Tail and checker:** For s=1,2,3 and t>0, bounding every omitted
  denominator below by `(N+1/2)^s` gives (11). `lerch_half` sums j=0 through
  N-1, then uses the current power q^N and a symmetric zero-centered Arb
  ball containing the entire positive omitted tail. This is conservative.
  All test points are rigorously restricted to `0<t<log 3`, so n=2 is the
  only possible nonzero prime-power term. At exact `t=log 2` the true hinge
  is zero; the small interval dependency error still encloses zero. The
  explicit exception gates require positive lower bounds. The saved tail
  size at t=1/10 is consistent with the largest displayed output radius.
  The separately differentiated left-slope formula is also correct, since
  `L_s'=-2 L_(s-1)+L_s`; its added jump is exactly `(log 2)^2/2`.

The limitations in the attack are appropriate. The finite Arb receipt does
not prove a global derivative sign, and no observed floating-point sweep
changes that scope. Positive omega derivative near zero gives the opposite
ordering to the proposed descent from omega=1/2. It does not establish the
sign of Psi_0 or exclude every possible differential comparison argument.
There is no Lean replay or unconditional RH proof in this result.
