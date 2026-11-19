# Actual log-3 interaction for independently shaped source packets

Date: 2026-11-03. Source root: `/workspace/aegis-replay-20261103`.

This is an ordinary mathematical composition of the source definitions and
existing estimates. The independent-shape statements below have not been
formalized or checked by Lean. No archived code was executed and no source
module was changed. The conclusion concerns one explicit nonlocal two-window
family, not arbitrary source reconstruction or global RH.

## Source normalization and exact domain

Put \(r=1/256\), \(D=2\log 3\), and choose arbitrary complex profiles

\[
h,\eta\in C_c^\infty(\mathbb R;\mathbb C),\qquad
\operatorname{supp}h,\operatorname{supp}\eta\subseteq[-r,r],
\]

with both source moments zero:

\[
\int e^{-t/2}h(t)\,dt=\int e^{t/2}h(t)\,dt=0,
\qquad
\int e^{-t/2}\eta(t)\,dt=\int e^{t/2}\eta(t)\,dt=0.
\]

For any common origin \(a\in\mathbb R\), define actual source packets, extended
by zero for \(x\le0\), by

\[
p(x)=x^{-1/2}h(\log x-a),\qquad
q(x)=x^{-1/2}\eta(\log x-a-D)\quad(x>0).
\]

These are elements of `WeilCompactSmoothGV1`: their support stays in a compact
subinterval of the positive half-line, so the zero extension is smooth. Their
logarithmic lifts are \(h(t-a)\) and \(\eta(t-a-D)\), respectively. The source
moments are \(\int p(x)/x\,dx\) and \(\int p(x)\,dx\); under \(x=e^t\) they become
nonzero exponential constants times the displayed profile moments. Thus both
packets satisfy `WeilMomentConditionsV1` and have fine centers \(a,a+D\).

Use the source energies and the first-argument-linear inner product

\[
E_p=\operatorname{energy}(p)=\int|h|^2,\quad
E_q=\operatorname{energy}(q)=\int|\eta|^2,\quad
S=E_p+E_q,\quad H=\int h(t)\overline{\eta(t)}\,dt.
\]

The energy identification is exactly
`logLift_energy_eq_packet_energy`, not an alternative norm convention.
The profiles may have different shapes, energies and complex phases.

Source references: `AegisRH/PR606/WeilCriterionCompactSmoothV1.lean:50,54,64,87`,
`AegisRH/PR606/WeilThreeBlockCrossPrimeV28.lean:56,62`, and
`AegisRH/PR606/WeilLogCoordinateIsometryV21.lean:118`.

## Exact signed prime formula for the independent shapes

Write \(X_{p,q}(u)=\int\operatorname{logLift}p(v+u)
\overline{\operatorname{logLift}q(v)}\,dv\). The source identity is

\[
X_{p,q}(u)=e^{u/2}\operatorname{mixed}(p,q)(e^u).
\]

Its support is contained in \([-D-2r,-D+2r]\). Consequently every positive
integer sample \(\operatorname{mixed}(p,q)(m)\) vanishes. A reciprocal sample
can survive only if \(|\log m-D|\le2r\). At the present radius the existing
`nat_eq_pow_three_of_log_window` argument, with \(k=2\), forces \(m=9\);
its sufficient condition is \(2r\le1/(2\cdot9)\), which holds. This support
argument does not require the two profiles to be equal.

The surviving correlation is

\[
X_{p,q}(-D)=\int h(t)\overline{\eta(t)}\,dt=H,
\qquad \operatorname{mixed}(p,q)(1/9)=3H.
\]

Because the source reciprocal coefficient is \(1/m\), and
\(\Lambda(9)=\log3\), the entire genuine von Mangoldt sum is exactly

\[
\boxed{\operatorname{WeilPrimeSum}(\operatorname{mixed}(p,q))
=\frac{\log3}{3}H.}
\]

In particular this is an inner product, not an energy unless \(\eta=h\).
The conjugation and orientation above follow directly from the source mixed
definition. Since \(\operatorname{mixed}(p,q)(1)=0\), no center constant remains:

\[
B(p,q)=\frac{\log3}{3}H+\mathcal A_D(h,\eta).
\]

Here \(\mathcal A_D\) is the actual Archimedean term, with its sign retained.
The exact separated-kernel theorem gives

\[
\mathcal A_D(h,\eta)
=\iint h(x)\overline{\eta(y)}K(D+y-x)\,dx\,dy,
\qquad K(s)=\frac{e^{-s/2}}{1-e^{-2s}}\quad(s>0).
\]

The argument \(D+y-x\) and the positive sign are fixed by
`separated_arch_eq_log_kernel`, which uses \(K(u)X_{p,q}(-u)\).

Source references: `AEGISOverlay/RHPrimeThreeWindowV1.lean:60,205` and
`AegisRH/PR606/WeilSeparatedArchBridgeV31.lean:187`.
The existing `RHLogThreeSignedPrimeProducerV1` theorem at line 66 treats the
same-mother case; the independent-shape identity here is the extension just
proved from its support argument and the actual definitions.

## Signed full-Weil estimate and an actual mixed-budget producer

The existing `distinct_fine_far_arch_norm_le` theorem applies because both
packets are fine, \(p\) has the two moments, and \(D\ge\log2\). It states
\(\|\mathcal A_D\|\le S/200\). This is **one two-hundredth of the energy sum**;
for two equal energies \(E\) it is \(E/100\).

Thus the first signed estimate, before any profile relaxation, is

\[
\boxed{\operatorname{Re}B(p,q)
\le\frac{\log3}{3}\operatorname{Re}H+\frac{S}{200}.}
\tag{1}
\]

The genuine signed prime interaction is retained in (1). Only the existing
Archimedean remainder estimate was used. More sharply, the source theorem
`distinct_fine_arch_decay_any_positive_gap` replaces \(1/200\) by

\[
R(D)=\frac1{128}
\frac{e^{-5(D-1/128)/2}}{1-e^{-2(D-1/128)}}.
\]

For the rational relaxation, reuse the existing
`distinct_logCross_norm_le_mean_energy` theorem at source line764 and
evaluate its correlation at \(-D\). It already supplies
\(|H|\le S/2\), hence \(2\operatorname{Re}H\le S\). No new Cauchy--Schwarz
or Archimedean estimate is being introduced. Since \(0<\log3\le2\), (1) implies

\[
\operatorname{Re}B(p,q)
\le\left(\frac{\log3}{6}+\frac1{200}\right)S
\le\frac{203}{600}S.
\tag{2}
\]

Let \(\alpha=5671/3200\). The existing fine diagonal theorem supplies

\[
\alpha E_p\le-\operatorname{Re}B(p,p),\qquad
\alpha E_q\le-\operatorname{Re}B(q,q).
\]

Hermitian symmetry and ordinary finite summation then give the actual signed
full-Weil bound

\[
\boxed{\operatorname{Re}B(p+q,p+q)
\le-\left(\alpha-\frac{203}{300}\right)S
=-\frac{10517}{9600}S.}
\tag{3}
\]

This is the original same-mother two-packet margin, expressed in the energy
sum, now established for independently shaped legal profiles at this exact
gap. No polarization or absolute Schur replacement is involved.

To feed the existing consumer explicitly, take \(n=1\) and
\(gs:\operatorname{Fin}(2)\to\operatorname{WeilCompactSmoothGV1}\) with
\(gs(0)=p,gs(1)=q\). Use the two fine diagonal inequalities as `hd`. By the
definition of the genuine defect and `B_hermitian`,

\[
\operatorname{actualMixedDefect}(1,gs)
=2\operatorname{Re}B(p,q)
\le\frac{203}{300}S\le\alpha S.
\]

The final comparison is strict when \(S>0\), since
\(\alpha-203/300=10517/9600>0\). For the zero pair the weak inequality still
provides the required `hbudget`. Therefore
`actual_sign_of_one_fine_mixed_budget gs hd hbudget` consumes an **actually
produced** mixed budget for this nonlocal two-window family and yields its
nonpositive arithmetic sign. Its source packet is exactly \(p+q\), whose
moments vanish. This supplies the consumer only on this stated family; it
does not supply one such certificate for every arbitrary source packet.

Source references: `AEGISOverlay/RHActualMixedDefectV1.lean:764,809,1112`,
`research/rh/aegis_pr721_fb983fd/lean/RHFineDiagonalUpgradeV3.lean.src:203`,
`AegisRH/PR606/WeilMixedAlgebraV2.lean:211`, and
`AEGISOverlay/RHActualUniversalFineGramV1.lean:913`.
The diagonal `.lean.src` file was read as text only.

## An adverse actual cross-sign with orthogonal independent shapes

Choose a nonzero, nonnegative, even real
\(\psi\in C_c^\infty((-r,r))\), and define

\[
\phi=\psi''-\tfrac14\psi,\qquad
c=\frac{\|\phi\|_2}{\|\phi'\|_2}>0,\qquad
h=\phi,\quad\eta=c\phi'.
\]

Such a \(\psi\) can be the usual smooth bump
\(\exp[-1/(1-(2t/r)^2)]\) on \(|t|<r/2\), extended by zero. Integration by parts
shows \(\int e^{\pm t/2}\phi=0\) and
\(\int e^{\pm t/2}\phi'=0\). The function \(\phi\) is nonzero (for example,
\(\int\phi=-\tfrac14\int\psi<0\)), and \(\phi'\) is nonzero because a compactly
supported nonzero function cannot be constant. The two profiles are even and
odd, hence linearly independent. Their source energies are equal and positive.
Also

\[
H=c\int\phi(t)\phi'(t)\,dt=0.
\]

At \(D=2\log3\), the **entire genuine prime sum is therefore exactly zero**,
including the sole possible sample at 9. This annihilation does not force
the full Weil cross term to vanish or to be favorable.

For a separated gap \(d>2r\), put
\(A_\psi(\lambda)=\int e^{\lambda t}\psi(t)\,dt>0\) and
\(\lambda_j=2j+1/2\). The exact positive kernel expansion

\[
K(s)=\sum_{j\ge0}e^{-\lambda_js}
\]

converges uniformly on the interaction domain \(s\ge d-2r>0\); compact
support also gives absolute convergence after integration. Integration by
parts, together with evenness of \(\psi\), gives

\[
A_\phi(\lambda)=(\lambda^2-\tfrac14)A_\psi(\lambda),\qquad
A_{c\phi'}(-\lambda)=c\lambda A_\phi(-\lambda).
\]

Hence the actual real Archimedean term is

\[
\boxed{\mathcal A_d(\phi,c\phi')
=c\sum_{j\ge1}\lambda_j e^{-\lambda_jd}
(\lambda_j^2-\tfrac14)^2A_\psi(\lambda_j)^2>0.}
\tag{4}
\]

The \(j=0\) term vanishes exactly by the moments. There is no sign estimate
or norm surrogate in (4). At \(D=2\log3\), its first surviving term has
\(\lambda_1=5/2\), so

\[
\boxed{\operatorname{Re}B(p,q)
=\mathcal A_D(\phi,c\phi')
\ge\frac{10c}{27}A_\psi(5/2)^2>0.}
\tag{5}
\]

Indeed \((5/2)((5/2)^2-1/4)^2e^{-(5/2)D}=90/243=10/27\).
Thus a universal favorable assertion \(\operatorname{Re}B(p,q)\le0\) fails
even for orthogonal, equal-energy, independently shaped legal fine packets
at the exact log-3 resonance with the resonant prime term annihilated.
This is compatible with (3): the positive cross term is paid by the negative
diagonals.

The same positive Arch formula holds at any separated integer-log-free
gap. For an exact example outside the common \(L=4/3\) center range, take
\(d=(\log4+\log5)/2\). Its distance from both neighboring integer logarithms
is \(\tfrac12\log(5/4)>1/128\), so the prime sum is zero and (4) gives
\(\operatorname{Re}B>0\). The convenient gap \(d=3/2\) also lies strictly
between \(\log4+1/128\) and \(\log5-1/128\).

There is a useful restricted favorable orientation: putting \(c\phi'\) in
the **left** profile and \(\phi\) in the right profile reverses the sign of
every surviving term in (4). Its actual prime sum is still zero at the
same exact resonance or prime-free gaps, and its real full-Weil cross term
is strictly negative. Thus the sign depends on the actual ordered profiles;
orthogonality or an even/odd sector label alone does not fix it.

## What the existing resonance controls leave open

`RHLogThreeSignedPrimeProducerV1:66,105` proves a same-mother prime budget
and a coercive two-packet sum at \(2\log3\). It does not assert a nonpositive
cross term. `RHPrimeThreeWindowV1:205` treats \(k\log3\) with an explicit
isolation-width hypothesis. At fixed \(r=1/256\), that theorem's sufficient
condition \(3^k\le64\) certifies only \(k=1,2,3\), not all lattice gaps.
The finite-horizon producer uses
\(r(K)=\min(1/256,1/(4\cdot3^K))\) to retain exact arithmetic for \(k\le K\).

`RHActualMixedDefectV1:680` has a signed common-window estimate for
independent fine centers within \(35/128\). The Trigram extension reaches
\(507/640\), and `RHL43ActualWeightedGramV1:167` reaches \(509/384\).
These are bounds paid by actual diagonals, not universal favorable signs.
Separated log-free windows have zero actual prime term and a charged Arch
remainder; resonant windows retain their signed correlations. The exact
independent-shape result (1)–(3) fills the particular two-window gap
\(2\log3\), while (5) rejects a blanket favorable sector sign there.
Neither result controls the sum of all mixed interactions for arbitrary
centers, shapes or numbers of atoms.

## Source hashes

SHA-256 of the exact files read for the central derivation, recorded on
2026-11-03. Paths are relative to the source root above.

```text
cce91eba3bbdb9c7762f2daea7283eac1f3afda1654adcec0ecf47dc27ece989  AEGISOverlay/RHLogThreeSignedPrimeProducerV1.lean
47809981563dbfc8e93985837257664d9b5ad9fd1c1efb7270cd3ab70a4823bb  AEGISOverlay/RHPrimeThreeWindowV1.lean
34557b25d8580c9c47691af90eec3b265084cb03e33155ac5d959b7107476fd9  AEGISOverlay/RHActualMixedDefectV1.lean
1db180efd9073288fb0ffb71193a1f29a30c04bc9b8340b9245b65d826175d34  AEGISOverlay/RHActualUniversalFineGramV1.lean
75593212f793e8435cddcac77b8a39e5b94f268f6df8a3bacbd9cd98c2b81afb  AegisRH/PR606/WeilCriterionCompactSmoothV1.lean
68bc4b84171a0f4cbc5e5d6f4a6fda7d47cdeb2201d2205fefdfdbc27d8616c7  AegisRH/PR606/WeilThreeBlockCrossPrimeV28.lean
8c303e7fe9c14e1082cb1b3e972da6d282305100b49982f22b0fa98f5be7aa21  AegisRH/PR606/WeilSeparatedArchBridgeV31.lean
017f644e89d763646b38af50d5df91c2386d70cb18fc557206ce54d489e7bfa2  AegisRH/PR606/WeilLogCoordinateIsometryV21.lean
fa510757adddeecfc7940fc646b43ab03064bf38ee34488d3933d5215195ca68  AegisRH/PR606/WeilMixedAlgebraV2.lean
7fe66f1327f183f8b9ec9b283004909e56f197bfae942edd7a392ee2bf373154  research/rh/aegis_pr721_fb983fd/lean/RHFineDiagonalUpgradeV3.lean.src
```
