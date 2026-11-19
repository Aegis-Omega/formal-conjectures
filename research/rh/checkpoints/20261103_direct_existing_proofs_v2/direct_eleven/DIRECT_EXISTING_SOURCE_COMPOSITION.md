# Direct reuse of the existing distinct-packet bounds

Source checkout: Aegis-Omega/formal-conjectures,
`1f70364296eee931d0cae5ecc16a0c9810c0c4cc`.
This is an ordinary mathematical composition, not a new choice of weights,
an RH equivalence, or a kernel-checked analytic adapter.

The previous independent-shape argument in commit
`44b78e21321a9a96ca714e540e04ee46c84fc63e` remains valid. It used an
unnecessary factor two by polarizing a same-mother estimate. Existing
distinct-packet correlation and Archimedean theorems allow a stronger
direct composition on exactly the same family. They are reused below.

## Existing sources, with their actual roles

* `AEGISOverlay/RHActualMixedDefectV1.lean`, blob
  `f3d1ccf81ba8c9fbefc41886ddf163db10656148`:
  `distinct_logCross_norm_le_mean_energy` proves
  `||logCross(p,q,t)|| <= (E(p)+E(q))/2` for arbitrary packets.
  `distinct_fine_far_arch_norm_le` proves the actual Arch bound
  `(E(p)+E(q))/200` for distinct legal fine packets at gap at least log 2.
  `distinct_fine_far_mixed_one_zero` and
  `distinct_fine_far_actual_B_norm_le_prime_plus_arch` give the actual
  full off-diagonal B decomposition and bound. These are existing results;
  they are not rebuilt here.
* `research/rh/aegis_pr721_fb983fd/lean/RHRationalNinePacketPrimeWindowV1.lean.src`,
  blob `7175f243640df980d9c2effc610cbb6748ffc29b`: the eight
  `gap_*_vonMangoldt_zero_v1` theorems are arithmetic window statements
  about integers m, independent of the shape or identity of a mother packet.
* The neighboring gap-nine source, blob
  `6f0ce19532bb422649d764a0bea930e3756a8c59`: the window is within
  integers671..680 and its only nonzero von Mangoldt samples are673,677.
  Each satisfies `log(m)/sqrt(m) <= 7/25` by the source's scalar bounds.
* The gap-ten source, blob `c1771ca493a3292d962b77332437c2de3a693ac2`:
  the window is within1383..1403 and its only nonzero sample is1399,
  with `log(1399)/sqrt(1399) <= 8/37`.
* `AEGISOverlay/RHActualElevenLatticeV1.lean`, blob
  `97a98db382e433488ed20f7df0980f41b20e4cbc`: the actual fine
  diagonal, existing eleven costs and optimized weights, and the source's
  Q16 row consumer. The exact-cost row ledger used here is from the
  previously emitted `WeightedIndependentShapeArithmetic.lean` in commit
  `44b78e21321a9a96ca714e540e04ee46c84fc63e`: `exact_row_ledger`,
  `all_eleven_weighted_rows`, and `maximum_attained`. That standalone
  arithmetic certificate already checks these same rows; it is not
  regenerated or misattributed to an original Q16 declaration.
* `AEGISOverlay/RHWeightedSchurV1.lean`, blob
  `1860b9a94d1fd5dec368283c6c914effab053cc3`: the existing
  `weighted_gram_variable_energy` consumer.

The .lean.src files are the exact archived mathematical sources stored
in the source checkout. They are not silently substituted for a differently
named compiled module. A future analytic port must retain that distinction.

## Statement

Fix a real a. Independently choose eleven actual complex smooth compact
positive-axis Weil packets h_i, each with both repository moments zero and
with logarithmic support in `[a-1/256,a+1/256]`. Put

    s_i=i log(33/16), T_i h=translatePacket h s_i,
    F=sum_(i=0)^10 z_i T_i h_i,                z_i in C arbitrary.

Then, with the repository's unchanged B and ordinary energy E,

    -Re B(F,F) >= (1203957/1136000) sum_i E(h_i)|z_i|^2.       (1)

All independent shapes and complex coefficient choices are included. This
does not assert that arbitrary global packets lie in this specified family.

## 1. Direct actual prime bounds for independent shapes

Take i<j and let `d=s_j-s_i`, `p=T_i u`, `q=T_j v`. Their widths are the
same fine widths and `d>=log(33/16)>log2`. By the existing support theorem
`logCross_zero_outside`, their log cross-correlation vanishes outside

    [-d-1/128,-d+1/128].

The exact multiplicative/additive identity
`logCross(p,q,t)=exp(t/2)mixed(p,q,exp(t))` is the already proved
`WeilThreeBlockCrossPrimeV28.logCross_eq_mixed_v28`.
Thus `mixed(p,q,m)=0` for every positive integer m: its log is nonnegative
whereas the displayed support interval is strictly negative. A reciprocal
sample can be nonzero only when

    |log(m)-d|<=1/128.

At that reciprocal sample the same identity gives exactly

    (1/m)mixed(p,q,1/m)=m^(-1/2)logCross(p,q,-log(m)).

The existing distinct-packet mean-energy theorem therefore bounds its norm
by `m^(-1/2)(E(u)+E(v))/2`. Translation preserves each ordinary energy.
The logarithmic support and integer-window proofs require no shared shape.

When j-i is1..8, apply the existing eight arithmetic von Mangoldt-zero
theorems; every actual prime term is zero. When j-i=9, only673 and677
remain and the source scalar estimates give total prime cost
`(14/25)(E(u)+E(v))/2`. When j-i=10, the cost is
`(8/37)(E(u)+E(v))/2`. All prime-power terms are included; values outside
the listed windows vanish by actual support, and the remaining composite
integers vanish by the exact source von Mangoldt proofs. No truncation
error, new assumption about primes, or infinite prime tail is left.

## 2. Reuse the already proved independent Arch bound

Apply `distinct_fine_far_arch_norm_le` directly to p,q at centers
`a+s_i,a+s_j`. The source hypotheses hold individually; the first packet
has its actual zero moments. This gives

    ||Arch(mixed(p,q))|| <= (1/100)(E(u)+E(v))/2.

The actual center sample at1 is zero by the same source disjoint-support
lemma. Consequently the full B estimate is

    ||B(T_i u,T_j v)|| <= (c_ij/2)(E(u)+E(v)),                 (2)

where `c_ij=57/100` for distance9, `837/3700` for distance10,
and `1/100` for all other off-diagonal distances. Hermitian symmetry
supplies the reversed ordered pair. These are exactly the original costs.

## 3. Existing reciprocal-rescaling argument, without polarization

The earlier checkpoint already gives the reciprocal-rescaling argument.
Apply it to (2), which has the essential factor1/2. For each r>0,
replace u,v by r*u,r^(-1)*v. B is unchanged by sesquilinearity and the
positive real scaling; moments and support conditions are preserved.
Its upper bound becomes

    (c_ij/2)(r^2 E(u)+r^(-2)E(v)).

For positive energies its infimum is `c_ij sqrt(E(u))sqrt(E(v))`.
If either energy is zero, the corresponding scalar limit of this bound
is zero. Thus

    ||B(T_i u,T_j v)|| <= c_ij sqrt(E(u))sqrt(E(v)).             (3)

No polarization identity or positivity of B has been used. Cauchy-type
control came from the existing ordinary-energy theorem, not from the
Weil form whose sign is being investigated.

## 4. Compose the existing actual diagonal and weighted consumer

Use `all_actual_eleven_diagonal_bounds` separately for each h_i. Its
unchanged diagonal lower constant is `A=5671/3200`.
Keep the source's existing weights

    (427,355,24,24,24,24,24,24,24,355,427).

The already certified maximum exact weighted row for c is
`S=25289/35500`. The prior factor-two adapter used2c and2S; equations
(2)--(3) now supply c and S themselves. Applying the existing
`weighted_gram_variable_energy` and exact finite Gram expansion gives

    -Re B(F,F) >= (A-S)sum_i E(h_i)|z_i|^2.

The exact rational identity is

    5671/3200 - 25289/35500 = 1203957/1136000 > 0.

This proves (1). The previous constant394709/1136000 remains a valid
weaker corollary. The improved constant is not a newly optimized choice
of weights; it restores the original exact-cost margin for independent
shapes by using stronger existing inputs.

Translation, complex scaling, and finite addition preserve both moments.
The existing actual moment-zero explicit formula therefore transports
(1) to the canonical zero quadratic with its original zero multiplicities
and convergence. Each h_i can itself be an arbitrary finite combination
inside its source window; its E(h_i) retains every internal L2 mixed term.

## Status and continuation scope

This written proof on its exact family has passed the separately recorded
`INDEPENDENT_DIRECT_ELEVEN_REVIEW.md`. The source-to-new-adapter analytic Lean port has not
been compiled. Prior numeric row kernels are reused only for their actual
finite arithmetic claims. No unrestricted packet representation, global
Weil sign, new RH equivalence, or RH theorem is asserted. All earlier
verified wider-domain results retain their original scopes.

## Existing signed-sector and per-packet certificate consumers

Let V_11(a) be the complex vector space of these eleven-window sums with
arbitrary legal h_i. The windows are disjoint, so (1) implies
`-Re B(F,F)>=mu E(F)` on this space, `mu=1203957/1136000`.
The existing signed-sector composition in
`signed_sectors/SIGNED_SECTOR_COMPOSITION.md` uses only this positivity,
the already proved linear closure, and exact finite B expansion.
It therefore applies with this stronger mu without a new closure proof:

    2 Re B(U,cV)+mu E(U+cV)
        <=-Re B(U,U)-Re B(cV,cV),               for every c in C,

when the eight synthesized source packets all belong to this same V_11(a).
No physical or B-sector orthogonality is assumed. The already existing
strict-sign-to-refinement certificate construction supplies its actual
mixed-budget certificate for each nonzero F in this space; its zero branch
handles F=0. The independent review checks this exact corollary.

The universal consumer quantifies over every legal packet. No claim that
this particular V_11(a) covers that full carrier follows from the above.
