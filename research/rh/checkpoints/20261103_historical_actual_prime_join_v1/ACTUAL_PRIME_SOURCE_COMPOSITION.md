# Actual finite prime operator from the recovered Coq source

This composition recovers an actual arithmetic constituent of the Weil form,
including its complex carrier, its physical support cutoff, and its scale.
It does not claim positivity of that constituent or of the assembled Weil
form. The derivation below is a complete ordinary mathematical proof, not a
new Coq/Lean kernel receipt. No archive program was executed.

## Source binding

The history manifest is
`/workspace/aegis-nov3-history-intake/HISTORY_INTAKE_MANIFEST.json`; its bodies
are in `source/<blob>.<extension>`. The following proof bodies, rather than
status declarations, enter the composition:

* `02dba9c7dbff4e1b904231499e6b6ba0c4bac0d0.v`,
  `CanonicalPrimeSourceSum`: canonical `q=i+2`; actual von Mangoldt zero
  off prime powers; certified binding of Lambda(q), sqrt(q), log(q); the
  constructive derivative of their finite sum at a shared positive L.
* `056bf0f92378f097b2fdbe86f7f36506651a8e5c.v`,
  `PrimalityStdlibBridge`: the local primality predicate implies standard
  integer primality, Euclid's lemma, and uniqueness of prime-power bases.
  This removes the possibility that the canonical Lambda source is only a
  family with arbitrary labels called primes.
* Existing recovered `PrimePowerWeightBridge`, blob
  `5c816320f3ec1c8a312a56cc18ebdba0e6f78893.v` in
  `/workspace/aegis-nov2/CoqRecovery/CorpusBlobs`: exact definitions
  `omega=1-log(q)/L`, amplitude `-Lambda(q)/(pi sqrt(q))`, frequency
  `2 pi omega`; its scalar derivative normalization is proved.
* `a5e22827b80e52064d0e00993fe1b2a7c0319eea.v` and
  `6f73c0cf5427d0331eef5e3f2fa24a98c2204184.v`,
  `ConcreteFiniteGuinandWeilSemanticsV1`: the actual complex scalar prime
  term is Lambda(q)(F(q)+q^-1 F(q^-1)); the leading q=1 term is zero and
  the remaining prefix is exactly q=i+2.
* `e66051154a36132b4f2c828f8babe69764860cca.v`,
  `CornO0MorphismBridge`: full ring/order transport IR -> O0 and equality
  with the independent completion presentation.
* `63bb11daa11e6889b4381855dd2febea733814c4.v`,
  `CornO0TransportTrig`: both carrier round trips and commutation for the
  transport-defined O0 sine/cosine.
* `/workspace/aegis-nov2/FiniteSource523/WeilFiniteSourceCalculusV1.lean`:
  `weil_single_frequency_source_calculus_v1`,
  `weil_finite_source_measure_extension_v1`, and
  `weil_finite_source_full_entry_identification_v1`. Their signed finite
  identities are used unchanged.
* Handwritten source `47011893bd11e6c73fc8a425d422095c738163e4.md`,
  `WEIL_CROSS_TERM_KERNEL_V1`, sections 1–2, fixes the dy autocorrelation,
  logarithmic h normalization, actual prime sum and sign of the arithmetic
  RHS. Its formulas can also be derived directly as below.

## 1. Scalar prime formula on the actual complex autocorrelation

Let h be a compactly supported complex function and

    g(x)=x^(-1/2) h(log x)  (x>0),
    F_g(x)= integral_(y>0) g(xy) conjugate(g(y)) dy,
    R_h(u)= integral_R h(t+u) conjugate(h(t)) dt.

For all the finite functions used below, the integrals exist absolutely.
Substitute y=exp(t), dy=exp(t)dt, to obtain

    F_g(exp u)=exp(-u/2) R_h(u).

Changing variable t -> t-u also gives

    R_h(-u)=conjugate(R_h(u)).

Consequently the exact canonical scalar prime term is

    Lambda(q)[F_g(q)+q^-1 F_g(q^-1)]
      = Lambda(q)/sqrt(q) [R_h(log q)+R_h(-log q)]
      = 2 Lambda(q)/sqrt(q) Re R_h(log q).                 (1)

No pointwise real projection of F_g was taken. In general F_g is complex;
only this complete reciprocal pair is real. This matches the source's
`ComplexAutocorrelationCarrierV1` policy with an actual analytic identity.

In the zero-positive Weil convention, the prime part is the negative of
(1). Write it as P_L(h). This sign is fixed throughout this note.

## 2. Full finite entry identity, including diagonal

Fix L>0, a finite integer band K={-N,...,N}, complex coefficients c_m, and

    e_m(x)=exp(2 pi i m x/L),
    h(x)=1_[0,L](x) sum_(m in K) c_m e_m(x).

Endpoint values do not affect any integral. For 0<=ell<=L define

    I_mn(ell)=integral_0^(L-ell) e_m(x+ell) conjugate(e_n(x)) dx.

Finite expansion is legitimate, and

    R_h(ell)=sum_m sum_n c_m conjugate(c_n) I_mn(ell).     (2)

For m=n,

    I_mm=(L-ell) exp(2 pi i m ell/L).

For m!=n, elementary integration and integer periodicity give

    I_mn = L/[2 pi i (m-n)]
           [exp(2 pi i n ell/L)-exp(2 pi i m ell/L)].      (3)

In particular I_mn=I_nm, including the diagonal. Set omega=1-ell/L.
The real parts are therefore

    Re I_mm = L omega cos(2 pi omega m),
    Re I_mn = L/[2 pi(m-n)]
              [sin(2 pi omega m)-sin(2 pi omega n)]       (m!=n). (4)

For an actual integer q>=2 with ell=log q<=L put

    alpha_q=-Lambda(q)/sqrt(q),
    psi_q(x)=alpha_q/pi sin(2 pi omega_q x),
    omega_q=1-log(q)/L.

This is exactly the recovered Coq prime source, not an arbitrary source
coefficient. If D_q(m,n) is psi's divided difference off the diagonal and
psi'_q(m) on the diagonal, (4) proves, entry by entry,

    -2 Lambda(q)/sqrt(q) Re I_mn(log q) = L D_q(m,n).      (5)

The diagonal is L[-2 Lambda(q) omega_q/sqrt(q)]
cos(2 pi omega_q m), exactly the Coq scalar derivative normalization.
The off-diagonal is L times the PR523 divided difference. Thus the
physical interval contributes an essential factor L.

## 3. The real PR523 finite theorem covers complex coefficients correctly

Write c_m=a_m+i b_m with a_m,b_m real. Since I_mn=I_nm, its imaginary
part contributes zero to the real part of (2): the imaginary coefficient
part is antisymmetric in m,n while I is symmetric. Explicitly, pairing
(m,n) with (n,m) gives

    Re R_h(ell)
      =sum_m sum_n (a_m a_n+b_m b_n) Re I_mn(ell).         (6)

This proves for each actual q in the physical cutoff

    -2 Lambda(q)/sqrt(q) Re R_h(log q)
      =L [WeilSingleFrequencyQuadraticV1 N a alpha_q omega_q
          +WeilSingleFrequencyQuadraticV1 N b alpha_q omega_q].  (7)

It is equality on the original complex finite family. It is not an
assumption that all admissible tests are real, and it is not an assumption
that the autocorrelation itself is pointwise real.

Let M=floor(exp L). The prime sum is finite because R_h(u)=0 for |u|>=L
(the boundary equality is zero too). Summing (7) for q=2,...,M and applying
the existing PR523 source-superposition identity gives

    P_L(h)=L sum_(2<=q<=M) alpha_q
                 [WeilChordKernelV1 N a omega_q
                  +WeilChordKernelV1 N b omega_q].        (8)

Thus the canonical arithmetic source, the scalar Guinand–Weil prime
constituent, the entire finite source-entry contraction and its chord form
are identified mathematically, with every actual prime power retained.
Off-prime-power integers vanish by the recovered canonical Lambda theorem.
The q=1 term vanishes by the recovered leading-zero theorem.

The Coq all-integer prefix alone does not encode log(q)<=L. For q>exp L,
the actual overlap is empty, whereas integrating the polynomial from 0 to
L-log(q) is a reversed, generally nonzero interval. Therefore (8) requires
exactly the physical cutoff, or zero extension of each source outside it.
A naked arbitrary `count` cannot be substituted into (8).

## 4. Exact moment-legal potential coefficients

The preceding finite family can be restricted to the actual clamped-potential
construction without guessing legality. Let a finite complex sequence beta_m
satisfy

    sum_m beta_m=0,        sum_m m beta_m=0.

Put phi(x)=sum_m beta_m e_m(x) on [0,L] and zero outside. Both phi and
phi' vanish at 0 and L. Therefore the distribution D0 phi=phi''-phi/4
is the ordinary interior function, with no delta or delta-prime boundary
terms. Its coefficients are exactly

    c_m= -[(2 pi m/L)^2+1/4] beta_m.                    (10)

For s=+-1/2, integration by parts twice gives

    integral_R exp(sx) D0 phi(x) dx
      = (s^2-1/4) integral_0^L exp(sx) phi(x) dx=0.    (11)

Thus both actual exponential moments vanish, for complex beta as well.
This directly fits the modulated sin-squared potential atoms:

    phi_n(x)=sin^2(pi x/L) exp(2 pi i n x/L),
    beta_n=1/2, beta_(n-1)=beta_(n+1)=-1/4.

Their sum and first discrete moment are both zero. Finite superpositions
of the actual atoms retain these identities. Applying (8) with (10)
therefore identifies the complete actual prime quadratic on this legal
finite potential family, including arbitrary complex atom coefficients.
Changing D0 to -D0 changes every c by a common minus sign and leaves the
quadratic unchanged; a source normalization factor must still be retained.

These h have piecewise smooth zero extensions and generally have jumps at
0 and L; they are in the logarithmically weighted Fourier form domain,
since their Fourier transform is O((1+|t|)^-1). They are not being falsely
called compact smooth tests. To reach the canonical smooth class use the
existing moment-preserving mollification/form-convergence theorem, with
its hypotheses and full-form identification. The arithmetic identity (8)
itself needs no such limiting argument.

## 5. What the historical carrier map actually transports

Let J= corn_ir_to_o0_carrier_v1. For finite IR entries A_mn and coefficients
v_m, let q_IR=sum_mn v_m A_mn v_n, and let q_O0 be the same expression
with J applied to every input and O0 ring operations. The recovered zero,
addition and multiplication theorems prove by two finite inductions that

    J(q_IR)=q_O0.                                        (9)

No positivity is used in this identity. If q_IR>=0 is separately proved,
`corn_ir_to_o0_preserves_le_v1` and preservation of zero give q_O0>=0.
The completion/reference equivalence proves the same result for the
independent completion image. This works for signed A as well; it does not
manufacture a sign.

The two round trips in CornO0TransportTrig also prove the needed finite
sine/cosine commutation when O0 trig is defined by transport. They do not
identify an independently defined native O0 integral or a Mathlib integral.
Thus finite constructive arithmetic and trigonometry are already connected
more strongly than a bare type mismatch suggests. The analytic integral
identity (8) remains an ordinary mathematical bridge, not a cross-prover
proof-term import.

## 6. Exact endpoint of the attempted positivity composition

Equation (8) completes an actual source identification. It does not match
the hypotheses of `finite_cauchy_stieltjes_rank_two_psd` or the weighted
Archimedean theorem: alpha_q=-Lambda(q)/sqrt(q)<=0, and the real chord
kernel has not been identified as a nonnegative Gram square at those
arithmetic frequencies. The existing PR523 theorem intentionally allows
signed alpha and concludes equality, not a sign. The finite Cauchy
Archimedean theorem is preserved on its stated fixed-T domain, as is its
weighted extension when the actual integration weight has the required
sign. Neither supplies the signed prime/low-Archimedean budget in (8).

`o0_normalized_quotient_stability_sound_v1`, historical blob
`4ef504813599e951888835311c5d752a266a0050.v`, cannot repair this exact
remaining implication: its input `o0_error_hypotheses_v1` already contains
nonnegativity of both the exact and approximate numerators. It transports
an error bound between positive quantities; it does not prove positivity
of the actual Weil numerator.

The old Globalization.v307 proof is retained unchanged. No new term of
its `GlobalizationReadyV1` is asserted here: (8) and (9) identify finite
arithmetic values but supply neither the full actual sign nor the old
all-continuous-compact-test convergence field. In particular, the finite
trigonometric h above need not have both Mellin moments zero or be smooth
under zero extension. Section 4 supplies exact legality for the actual finite potential
family; canonical smooth membership requires the separate domain transport
just stated. Membership is not inferred from an unconstrained finite
coefficient list.

This is a delimited failure of this proposed composition at the full
signed inequality. It is not a conclusion that no other historical source
contains a proof, and it does not negate any valid existing local-window,
finite-source, carrier-transport or globalization theorem.
