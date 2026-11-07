# Existing optimized eleven-lattice weights with the actual mixed input supplied

This is an ordinary mathematical composition of the existing source theorems.
It is not a new choice of weights, a new Schur theorem, or a proof of RH.
The preceding four-phase polarization argument is reused, with rescaling to
produce the exact mixed-input type of the existing variable-energy consumer.
The final inequality below has no additional `hcross` premise on its stated
packet family. The analytic Lean adapter has not been replayed here.

## Source and exact statement

Use Aegis-Omega/formal-conjectures at commit
`1f70364296eee931d0cae5ecc16a0c9810c0c4cc`. The source
`AEGISOverlay/RHActualElevenLatticeV1.lean` has Git blob
`97a98db382e433488ed20f7df0980f41b20e4cbc`.

Keep the repository's actual arithmetic sesquilinear Weil form B, packet
energy E, translation, logarithmic support, and both moment conditions.
B is linear in its first input and conjugate-linear in its second. E is
the positive ordinary L2 energy, not an assumed positive Weil form.

For i=0,...,10 let T_i be translation by i log(33/16). Fix any real a.
Choose independently eleven complex smooth compact positive-axis packets h_i
with BOTH repository moments zero and logarithmic support inside

    [a-1/256,a+1/256].

For EVERY choice of complex coefficients z_i set F=sum_i z_i T_i h_i.
Then

    -Re B(F,F) >= (394709/1136000) sum_i E(h_i)|z_i|^2.          (1)

The source moment-zero explicit formula consequently gives the same lower
bound for the canonical zero quadratic of F. The h_i are arbitrary functions
in the specified carrier, with arbitrary individual energies and shapes.
They are not a finite basis or scalar multiples of one mother.

## 1. Reuse the actual original analytic bounds

Put A=5671/3200. For i!=j define

    c_ij=57/100       if |i-j|=9,
         837/3700     if |i-j|=10,
         1/100       otherwise;
    c_ii=0.

The existing `all_actual_eleven_mixed_bounds` proves, for EVERY admissible
mother w in the same common window,

    |B(T_i w,T_j w)| <= c_ij E(w).                             (2)

The existing `all_actual_eleven_diagonal_bounds`, applied individually to
each h_i, gives

    -Re B(T_i h_i,T_i h_i) >= A E(h_i).                        (3)

These are estimates of the actual prime-power and Archimedean form. All
their original conventions and hypotheses are retained. No substitute
matrix, prime omission, or global Weil sign is introduced.

## 2. Reuse four-phase polarization, retaining its factor two

For fixed distinct i,j let S(u,v)=B(T_i u,T_j v) and q(w)=S(w,w).
The space of legal mothers on the common window is closed under addition
and complex scaling. Hence (2) applies to all four sums used in

    4S(u,v)=q(u+v)-q(u-v)+i q(u+iv)-i q(u-iv).

This identity holds for a general complex sesquilinear S; S need not be
Hermitian. It is the already written independent-shape polarization
argument, not a new positivity assumption. The triangle inequality and
the two ordinary L2 parallelogram identities give

    |S(u,v)| <= c_ij [E(u)+E(v)].                             (4)

Now use real r>0. Sesquilinearity gives S(ru,r^-1 v)=S(u,v), while ordinary
energy homogeneity gives E(ru)=r^2E(u), E(r^-1v)=r^-2E(v). Applying (4),

    |S(u,v)| <= c_ij [r^2 E(u)+r^-2 E(v)]  for every r>0.

If both energies are positive choose r=(E(v)/E(u))^(1/4). If E(u)=0 let
r tend to infinity; if E(v)=0 let r decrease to zero. The corresponding
nonnegative numerical upper bound tends to zero, so the mixed coefficient
is zero in either zero-energy case. Thus in every case

    |B(T_i u,T_j v)| <= 2 c_ij sqrt(E(u))sqrt(E(v)).             (5)

Only scalar limits of an explicit real upper bound were used in the zero
cases. There was no interchange of a zero sum, integral, or form limit.
All four mothers and their rescalings remain in the same source domain.
This supplies exactly the square-root-energy `hcross` input for this
family, with cost matrix 2c. It does not supply an input of arbitrary
geometric scope outside this statement.

The factor two is retained. It cannot be discarded from a general
non-Hermitian polarization argument: S(u,v)=2u_1 conjugate(v_2) on C^2
has |S(w,w)|<=||w||^2 but S(e_1,e_2)=2.

## 3. Reuse the original optimized weights and pay all eleven rows

Use the existing `elevenOptimizedWeightUnits`:

    w=(427,355,24,24,24,24,24,24,24,355,427).

This is the original source's choice. It is not an optimization performed
by the present work. With the original EXACT costs c, rather than their
Q16 outward roundings, the eleven weighted rows are

    (225089/315980, 25289/35500,
     427/600,427/600,427/600,427/600,427/600,427/600,427/600,
     25289/35500,225089/315980).

Their maximum is S=25289/35500, attained at indices1 and9. Every diagonal
cost is excluded, and every one of the110 ordered off-diagonal entries is
included. These rational comparisons are verified by the emitted integer
certificate; it is finite exact data, not a numerical eigenvalue estimate.

## 4. Apply the existing variable-energy weighted Schur theorem

Apply `AEGIS.WeightedSchur.weighted_gram_variable_energy` with

    H_ij=B(T_i h_i,T_j h_j), E_i=E(h_i), D=A,
    matrix cost=2c, weights=w, row constant=2S.

Nonnegative energies, symmetric nonnegative costs with zero diagonal, and
positive weights are established independently of the sign of B. Equations
(3) and (5) supply the actual diagonal and mixed inputs. Section3 supplies
the row input. The existing theorem therefore proves, for every complex z,

    Re sum_ij z_i conjugate(z_j) H_ij
       <= -(A-2S) sum_i E_i |z_i|^2.

The existing finite Gram expansion identifies this sum with B(F,F). Finally

    5671/3200 - 2*(25289/35500) = 394709/1136000 > 0.

This proves (1), including zero packets and all complex phases.

With the old already-existing weights (89,74,5,...,74,89), the exact-cost
maximum row is58648/82325 and the corresponding margin is732143/2107520.
Their difference from the margin in(1) is strictly positive. No claim of
newly discovering either weight vector is made.

## 5. Moment/zero-side transport and arbitrary within-window combinations

Translation by s shifts the logarithmic lift, multiplying its exponential
moment M_sigma by exp(sigma s). Scaling and finite addition are linear.
Thus both zero moments remain exactly zero for F. The existing actual
moment-zero explicit-formula theorem identifies -Re B(F,F) with the
canonical zero-index quadratic, with its original multiplicities and
summability. No external RH placeholder proof is used.

Each h_i may itself be ANY finite complex combination of different legal
packets in the common source window. Existing `fine_width_packetSum`,
moment linearity, and the exact Gram identities give that membership.
The resulting energy is E(h_i), retaining all within-window L2 mixed
terms; it is not replaced by the sum of the constituent energies.
Thus the proof includes arbitrary finite within-window blocks. The
existing `fine_local_exact_counterpart` remains available in its full
arbitrary-coefficient form; it is not reproved as an eleven-dimensional
special case.

The existing universal fine reconstruction of an arbitrary legal packet
also remains valid. Its centers are unrestricted; it does not assert that
all reconstructed pieces fit into this particular union of eleven windows.
Consequently (1) is an unconditional source composition on the exact
stated infinite-dimensional family, not an unconditional all-packet RH
application. No additional support/globalization conclusion is asserted.

## Verification boundary

The complete analytic argument above is ordinary mathematics reusing the
identified proof bodies. Its port to an actual-B Lean theorem is still
pending compilation with the required Mathlib/AEGIS import closure.

`WeightedIndependentShapeArithmetic.lean` proves only seven finite integer
statements interpreting the exact rows, margin and comparison. It was
compiled from identical source in two fresh directories with Lean4.33.1
`--trust=0`, and checked by `leanchecker --fresh -v`. Its axiom ledger
explicitly records the allowed standard `propext` dependency of its
list-based declarations. It does not certify the analytic bridge or RH.

The source-bound parser verifies that its input is precisely the original
Git blob and extracts the original definitions before emitting this
arithmetic data. This source binding is not itself a kernel theorem
relating the standalone data to the original module. Both that boundary
and the ordinary interpretation of cleared positive denominators remain
explicit.
