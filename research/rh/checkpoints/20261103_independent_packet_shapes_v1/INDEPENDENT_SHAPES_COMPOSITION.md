# Compose the existing eleven-lattice proof for independent packet shapes

This is an ordinary mathematical composition of existing source theorems,
not a new RH equivalence. It removes the common-mother restriction from a
specified eleven-window family. It does not remove the window geometry.
No novelty beyond this integration is claimed; earlier unreviewed sources
may already contain the same consequence. No fresh Lean replay is claimed.

## Source results actually reused

The source identities and exact snapshots are in SOURCE_MANIFEST.json.
In `AEGIS.RHActualElevenLatticeV1` the following are already proved:

* `all_actual_eleven_mixed_bounds`: for every moment-zero smooth packet w
  supported in the common logarithmic window of full width 1/128,
  `norm(B(T_i w,T_j w)) <= c_ij E(w)` for every i != j in Fin 11;
* `all_actual_eleven_diagonal_bounds`: `-Re B(T_i w,T_i w) >= A E(w)`;
* `eleven_row_bound`: `sum_(j!=i)c_ij <= R` for every i.

Here `T_i=translatePacket(.,i log(33/16))`, `E(w)=integral |w(x)|^2 dx`,
`A=5671/3200`, `R=1621/1850`, and

    c_ij = 57/100       if |i-j|=9,
           837/3700    if |i-j|=10,
           1/100      otherwise (off diagonal).

These costs concern the genuine arithmetic form B, with its existing
prime-power and Archimedean proofs. They are not substituted matrices.
The source's local support and two moment conditions are retained below.

The existing `AEGIS.RHActualUniversalFineGramV1` theorem
`actual_fine_gram_coercive_of_signed_real_row_certificate` consumes
arbitrary genuine packets p_i, the diagonal bound A E(p_i), and a symmetric
cost satisfying `Re B(p_i,p_j)<=c_ij(E(p_i)+E(p_j))`, with rows at most
57430/65536. It yields the margin 641/32768. Its matrix summation argument
is already complete; it need not be reconstructed as a new obligation.

Existing common-window arbitrary-shape theorems in
`RHActualMixedDefectV1`, `RHActualNarrowGramSignV1`, and
`RHL43ActualWeightedGramV1` were checked before deriving this adapter.
They handle sums in one common certified interval. The application here
has eleven widely separated intervals, so that particular common-window
hypothesis cannot supply it directly. Existing distinct-packet far-Arch
bounds are retained as alternative, potentially sharper inputs.

## Exact ordinary theorem on the actual packet class

Fix real a. Independently choose eleven actual packets h_0,...,h_10, each
complex, compact smooth on the positive multiplicative axis, with both
repository moments zero and logarithmic support in

    [a-1/256,a+1/256].

For every eleven complex coefficients z_i, put

    F = sum_(i=0)^10 z_i T_i h_i.

Then the existing actual arithmetic form satisfies

    -Re B(F,F) >= (2339/118400) sum_i |z_i|^2 E(h_i) >= 0.       (1)

The explicit-formula theorem applies because every translated/scaled
piece, hence F, has both zero moments. It identifies the left side with
the canonical zero quadratic on this F. The implication here uses that
existing transport, not an assumed positive representation of the zeros.

The h_i need not be equal, scalar multiples, translates of one seed, or
members of a finite-dimensional basis. Thus (1) concerns an infinite-
dimensional family. It is nevertheless not the entire legal test class.

## Proof: first supply the missing distinct-shape mixed terms

Let V_a denote the linear space of legal mother packets in the common
small window. Sums and complex multiples remain in V_a: support cannot
grow outside that interval, and both moments are linear. All energies
below are finite, since the packets are compact smooth.

For fixed i != j define the sesquilinear form

    S(u,v)=B(T_i u,T_j v),  q(w)=S(w,w).

S is linear in its first argument and conjugate linear in its second.
It need NOT be Hermitian. The existing same-mother theorem gives
`|q(w)|<=c_ij E(w)` for EVERY w in V_a, including the four sums below.

The non-Hermitian four-phase identity is

    4 S(u,v) = q(u+v)-q(u-v)+i q(u+i v)-i q(u-i v).              (2)

To check orientation, write a=S(u,u), b=S(u,v), c=S(v,u), d=S(v,v).
For any scalar alpha,
`q(u+alpha v)=a+conj(alpha)b+alpha c+|alpha|^2 d`.
Substitution of 1,-1,i,-i gives exactly (2), with no relation assumed
between b and conjugate(c).

The triangle inequality, the source bound on each q, and the ordinary
L2 parallelogram identities imply

    |S(u,v)| <= (c_ij/4) [E(u+v)+E(u-v)+E(u+i v)+E(u-i v)]
             = c_ij [E(u)+E(v)].                              (3)

This is the required actual different-shape bound. No Cauchy--Schwarz
inequality in the unknown Weil form has been used. The only positive
norm used in the parallelogram law is the independently defined L2 norm.
No limits, infinite sums over zeros, or new exchanges of integrals occur.

Apply (3) with u=z_i h_i and v=z_j h_j. Set
`p_i=T_i(z_i h_i)`, and `e_i=E(p_i)=|z_i|^2 E(h_i)`. Translation is an
isometry for the repository packet energy. The old diagonal theorem
applied individually to each z_i h_i gives `-Re B(p_i,p_i)>=A e_i`.
Equation (3) gives `Re B(p_i,p_j)<=c_ij(e_i+e_j)`.

The cost matrix is symmetric. The already proved finite Gram expansion
and signed-row summation therefore give

    -Re B(F,F) >= A sum_i e_i - sum_(i!=j)c_ij(e_i+e_j)
                 >= (A-2R) sum_i e_i.

Indeed exchanging the two finite indices changes neither c_ij nor its
domain, so the ordered off-diagonal sum is
`2 sum_i e_i sum_(j!=i)c_ij <= 2R sum_i e_i`.
All e_i are nonnegative. Finally, exactly,

    5671/3200 - 2*(1621/1850) = 2339/118400 > 0.

This proves (1), including zero packets and arbitrary complex phases.
Alternatively the existing signed-row consumer applies directly,
since `57430/65536 - R = 2911/30310400 > 0`, and yields its slightly
weaker already proved margin 641/32768. No new analytic row hypothesis
is left in this specified eleven-window application.

## Adversarial checks and exact scope

1. It is essential that the old estimate is for every mother w, not one
   fixed packet. Otherwise the four sums in (2) would not be certified.
   The recovered source has exactly that quantifier order.
2. Ordinary Hermitian polarization cannot be applied to S: translation
   indices i and j differ. Equation (2) is valid without Hermitianity.
3. A sharp numerical-radius-to-operator-norm estimate can lose a factor
   two. We retained that loss: the final margin is A-2R, not A-R.
4. A 2x2 nilpotent form `S(u,v)=2*u_1*conj(v_2)` satisfies
   `|S(w,w)|<=E(w)` but takes value 2 on (e_1,e_2). Thus dropping that
   loss would be unjustified. This checks the new adapter, not RH.
5. The source row estimate excludes the diagonal, even though the cost
   definition assigns a value at zero. No diagonal cost is included.
6. No fixed positive global coercivity is claimed. Translation and
   scaling preserve the two moments, so the full pole term vanishes
   on F exactly; it was not discarded for nonlegal inputs.
7. The equality and positivity above are ordinary mathematics derived
   from the recovered source theorems. The symbolic checker verifies
   only (2), the four-energy sum, and the rational constants. It does
   not verify the analytic source lemmas or constitute a kernel replay.

## Attempt to compose with the arbitrary-packet localization theorem

The old written proof in `WeilLocalizationDefectV1.md`, appendix (6)-(8),
already constructs a support-preserving inverse of D^2-1/4 and a finite
legal local decomposition of EVERY packet. Those complete arguments
are retained; their absence from Lean would not invalidate them.

However, the resulting pieces have independent centers. Equation (1)
requires those centers to be exactly a+i log(33/16), i=0,...,10, within
the stated small windows. The arbitrary-cover theorem does not supply
that geometry. There is a concrete legal test ruling out that particular
universal reconstruction even when a is freely chosen for every target.
Choose a smooth compact potential psi equal to 1 on [0,1], supported
in [-1,2], and put H=psi''-psi/4. Integration by parts gives both
exponential moments zero, while H=-1/4 on [0,1]. The actual packet
`g(x)=x^(-1/2) H(log x)` for x>0, extended by zero, is smooth legal.
For every a the eleven certified logarithmic windows have total measure
at most 11/128<1. They leave a positive-measure part of [0,1] uncovered.
Every proposed eleven-window sum vanishes there and H does not. Thus
this particular all-packet reconstruction is false, not just uncompiled.
This test is about the attempted composition, not a counterexample to RH.

This is a precise failed unification with the existing reconstruction,
not a refutation of either theorem, not a theorem that no other
reconstruction works, and not a conclusion that the corpus lacks RH.
The older source also already proves why simply shrinking a square
partition does not make the full arithmetic assembly defect vanish.
That argument is reused, not generated a second time.

Consequently the missing all-packet application is mathematical as well
as potentially formal: it needs an actual certified cover/reconstruction
and its cross-window budget, or another unconditional route. This
checkpoint supplies no such global producer and keeps rh_proven=false.
