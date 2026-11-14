# Actual signed sectors: source composition and its exact domain

2026-11-03. Ordinary mathematical source review and composition. No
analytic Lean replay, new weight optimization, or global RH proof is
claimed. The previous eleven-window polarization/weight proof is reused
as an input, not repeated. Suzuki is outside this continuation.

## Exact sources and existing producers

The active source checkout is detached at
`1f70364296eee931d0cae5ecc16a0c9810c0c4cc`. Actual Git blobs read:

| AEGISOverlay source | Git blob |
| --- | --- |
|RHBaguaActualWeilV1.lean|4b030efaa21cb5ed825c42d1e263886b6ad356c5|
|RHTimeSliceWeilV1.lean|0281d47ab0e0a790ac5dda4819ee312ed7dec6aa|
|RHLogThreeSignedPrimeProducerV1.lean|c4f11498abc94fd7e5b9ada587140a1bc862c822|
|RHActualMixedDefectV1.lean|f3d1ccf81ba8c9fbefc41886ddf163db10656148|
|RHActualUniversalFineGramV1.lean|a09243144d5116b75f3274dcf990697f261f51fd|

The relevant proof bodies were read along with RHActualNarrowGramSignV1,
RHBaguaWalshV1, RHBaguaRotatingTwoPairMellinV1, RHFourLogThreeActualPrimeV1,
RHScaleRowCompositionV1, RHOptimizedSchurGlobalJoinV1 and the existing
RHMixedBudgetRefinementV1. The producer search precedes the composition.

The actual scope of the existing sign producers is:

* `bagua_actual_full_weighted_margin` and
  `bagua_complementary_phase_coupling_margin` apply the complete actual
  Trigram estimate to sums in one common log half-width2/5 window.
  Both sector signs and every complex relative phase are genuinely
  controlled on that domain; their proof does not require zero cross blocks.
* `timeSliceFamily_full_weighted_margin` allows arbitrary finite
  cardinality, but retains one mother, fine half-width1/256, and the
  explicit center-span bound507/1280. Its proof embeds all slices into
  that same Trigram window.
* The sparse rotating/four-log-three producer keeps one mother,
  exact gaps4|i-j|log3, ordered separation and a horizon-dependent
  width. Arbitrary coefficient vectors, including converted Walsh sector
  coefficients, are allowed on that stated family. The common mother
  and geometry cannot be removed by changing coordinates.
* `timeSliceFamily_signed_prime_arch29` retains its actual signed-prime
  estimate and row allowance as hypotheses. It is not a producer of
  those bounds for arbitrary centers.

The universal fine constructor is already unconditional: it constructs
every legal packet as a finite sum of moment-zero fine packets with
5671/3200 diagonal bounds and the exact full Gram identity. Its centers
are unrestricted and its cardinality is arbitrary. Its theorem gives
no common Trigram window, one mother, or arithmetic lattice.

## The actual orthogonal-decomposition issue

Let H be the source unnormalized8x8 Walsh matrix, H^2=8I. Let C send
coefficient index i to7-i, and P_+=(I+C)/2, P_-=(I-C)/2. These are
orthogonal projectors for the standard coefficient inner product.

There are two distinct operations in the source. Original-index
complementation becomes diagonal character parity under H. In contrast,
`baguaEvenPacket/ baguaOddPacket` apply P_+/P_- to WALSH mode labels.
For original synthesized coefficients w=Hz, their actual packet
expressions are

    U=sum_i [(1+chi(i))/2] w_i g_i,
    V=sum_i [(1-chi(i))/2] w_i g_i,
    chi(i)=(-1)^(three-bit Hamming parity of i).                (1)

This follows by the source character identity H_(a,7-i)=chi(a)H_(a,i),
or its transposed version. It is an exact actual-packet identity.
For z=e_0, w_i=1 and the two groups are

    U=g_0+g_3+g_5+g_6, V=g_1+g_2+g_4+g_7.                   (2)

The packet-synthesis map need not be isometric or injective. Thus
coefficient orthogonality neither proves L2 orthogonality of U,V nor
that B(U,V)=0. The existing source correctly retains both cross blocks.

An actual source-legal counterexample to this automatic identification
is already elementary: set all eight packets equal to one nonzero
legal g in the common Trigram window, and z=e_0. Then mode0=8g,
mode7=0, and the source's U=V=4g. Therefore B(U,V)=16B(g,g), with
strictly negative real part by the existing Trigram margin. The
supposedly complementary images can even coincide.

A stronger example below has physically L2-orthogonal packets and
strictly POSITIVE actual B coupling. Hence imposing ordinary L2
orthogonality alone does not repair the missing B-commutation step.

## A valid nonlocal Bagua composition reusing the prior shape result

Define V_11(a) to consist of sums

    f=sum_(j=0)^10 T_(j log(33/16)) h_j,

where each h_j is an arbitrary legal mother in the one common
half-width1/256 source window centered at a. This is a complex vector
space with independent shapes; it is not a finite-dimensional basis.
The previous WEIGHTED_SHAPE_COMPOSITION.md establishes

    -Re B(f,f)>=mu sum_j E(h_j), mu=394709/1136000.              (3)

The translated fine windows are disjoint. The exact half-density
translation preserves L2 energy, so the sum on the right is E(f).
This also holds when each h_j is an arbitrary finite sum of legal
within-window packets, with its actual sum energy.

For eight arbitrary source packets g_i in V_11(a), every Walsh mode,
both complementary packet images and every relative-phase sum remain
in V_11(a). Applying(3), then the existing finite B expansion, gives
for every complex phase c

    2 Re B(U,cV)+mu E(U+cV)
       <=-Re B(U,U)-Re B(cV,cV).                              (4)

All real signed mixed terms are retained. There is no assumed physical
sector orthogonality. This composes the existing complete Bagua algebra
with a known nonlocal infinite-dimensional positive space, extending
the common-Trigram coupling domain in this precise restricted way.
It is a reuse of the prior source result, not another polarization,
Schur proof or optimization.

There is also an exact way to supply the existing per-packet budget
on this family. For nonzero f in V_11(a), (3) gives Re B(f,f)<0.
Use the already existing universal fine constructor for f and then
`RHMixedBudgetRefinementV1.certificate_of_strict_sign`. That theorem
refines the actual fine atoms into scaled copies and produces the
literal MixedBudgetCertificate(5671/3200,f). For f=0 use its existing
`certificate_of_zero`. Thus no hcross or mixed-budget premise remains
for f in this stated family.

The terminal consumer needs this certificate for EVERY legal packet.
The source reconstruction does not put an arbitrary packet in V_11(a).
Neither (4) nor the exact scoped certificate can fill that universal
argument without an additional domain/coverage theorem.

## A direct actual arithmetic sector estimate at two-log-three

ACTUAL_LOG3_INDEPENDENT_SHAPES.md records a second, direct composition.
For two independently shaped fine legal mothers with aligned log
profiles h and eta, and translation gap d=2log3, the complete prime
contribution is exactly

    Prime(p,q)=(log3/3) integral h(x)conj(eta(x))dx.             (5)

Only the actual n=9 sample survives. This retains the signed complex
inner product; it is not replaced by the energy of a shared mother.
The existing distinct-shape Arch bound is at most(E(p)+E(q))/200.
Together with the existing actual fine diagonal it yields

    -Re B(p+q,p+q)
       >=(5671/3200-1/100)(E(p)+E(q))
                       -(2log3/3)Re integral h conj(eta),      (6)

and in particular the conservative bound

    -Re B(p+q,p+q)>=10517/9600 (E(p)+E(q)).                    (7)

The actual mixed defect of gs=[p,q] is2Re B(p,q), bounded by
203/300(E(p)+E(q))<=(5671/3200)(E(p)+E(q)). Both original diagonal
inputs hold individually. Thus this pair directly supplies a genuine
one-fine-mixed-budget witness on its nonlocal two-window domain,
including the zero-energy case. It uses no new polarization or weights.

The current named log-three theorem and its time-slice adapter are
same-mother specializations. No independent-shape prime9 producer was
located in the searched active sources. The restored generic
WeilThreeBlockNormBridgeV21 is a correspondence/consumer theorem with
the cross estimates still supplied as inputs. Accordingly this is
described as an ordinary source composition/shape extension, not as a
claim of a novel analytic mechanism or a replayed new Lean theorem.

## Actual missing signed sector estimate

To see why L2 orthogonality cannot delete the missing coupling, choose
a nonzero even nonnegative smooth psi supported in(-r,r), r<=1/256.
Let phi=psi''-psi/4, and take actual log lifts

    h_p(x)=phi(x), h_q(x)=c phi'(x-d), d=2log3, c>0.

Both have exactly zero exponential moments; their physical supports
are disjoint, hence they are L2-orthogonal. Their exact prime9
coefficient is zero since integral phi phi'=0. Nevertheless the
source-normalized separated Arch expansion gives

    Re B(p,q)=c sum_(j>=1) lambda_j exp(-lambda_j d)
                     (lambda_j^2-1/4)^2 Apsi(lambda_j)^2>0,
    lambda_j=2j+1/2, Apsi(lambda)=integral exp(lambda x)psi(x)dx,

with the first term already(10c/27)Apsi(5/2)^2>0. Full derivation,
convergence and normalization are in the companion note. Flipping q
reverses the real sign. This is an actual Weil example, not a generic
matrix countermodel or a counterexample to RH.

Place p at original Bagua index0, q at index1 and put zero packets at
the other indices. For z=e_0, formula(2) gives U=p,V=q exactly. Thus
even an actual physical L2-orthogonal source Bagua pair need not have
vanishing or universally favorable real B coupling. Its union does
not satisfy the common Trigram hypothesis. The direct estimate(6)
pays this particular coupling, but gives no bound at arbitrary gaps
or for all cross interactions of a reconstructed packet.

The live signed target is concrete: after grouping actual fine atoms
into controlled local clusters, bound the sum of real B cross terms
between those clusters, together with their retained within-cluster
budgets. Equivalently in the displayed Bagua split, pay2Re B(U,V)
against the actual sector diagonal budgets. The exact original
RHScaleRowCompositionV1 total-defect consumer already accepts this
signed input. Current Bagua/Walsh identities, sparse prime producers
and Arch estimates do not supply it for the unrestricted geometry
of the universal fine constructor.

## Verification boundary

This work read existing proof bodies and derived the displayed ordinary
analytic compositions. It did not execute archived programs, alter old
checkpoints, prove another RH equivalence or create a new weight lemma.
No new analytic Lean compilation or transitive axiom audit is claimed.
No usage/tool limit prevented this bounded review. The remaining
unrestricted signed bound is a mathematical obligation.
