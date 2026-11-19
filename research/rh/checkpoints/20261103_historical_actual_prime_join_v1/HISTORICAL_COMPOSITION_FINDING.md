# Historical composition finding

`rh_proven = false`. This is a source-body and mathematical integration review,
not a Lean kernel verification. No downloads, archived code execution, or GitHub
modifications were performed. The 804 historical Lean bodies (291 distinct paths)
were searched by declaration types, proof bodies, constructors, field assignments,
instances, and aliases. The concrete arguments below use the exact blobs listed
in `HISTORICAL_COMPOSITION_SOURCE_SCOPE.json`; their SHA-256 hashes were rechecked.

## A universal sparse-reconstruction premise is actually false

The strongest concrete finding is an obstruction to the universal premise of
`riemannHypothesis_of_universal_actual_weighted_sparse_reconstruction`, not a new
RH equivalence. Its exact historical source is
`14b9403acf5e6c64e4a3da9f80cbe972db949e9c.lean`, lines 634–688.

`HasActualWeightedSparseReconstruction source` requires a finite identity

    source = packetSum z gs

in which every atom has log support in

    [center i - 1/256, center i + 1/256]

and, for `i < j`,

    (65/32) * Nat.dist i j <= center j - center i.

Consequently every pair of distinct centers is separated by at least `65/32`.
These support and separation requirements alone prevent this interface from
covering all smooth moment-zero packets. Neither the common-mother restriction
nor the additional exact four-log-three spacing is needed for the obstruction.

Here is an exact two-point proof. Suppose the source log lift is nonzero at
`t = 0` and `u = 1/64`. The finite sum identity implies that some atom `i` is
nonzero at `t` and some atom `j` is nonzero at `u`; hence

    |center i - t| <= 1/256,
    |center j - u| <= 1/256.

If `i = j`, the triangle inequality gives

    1/64 = |u - t| <= 2/256 = 1/128,

which is false. If `i != j`, the same triangle inequality gives

    |center j - center i| <= 1/256 + 1/64 + 1/256 = 3/128,

whereas the source separation gives

    65/32 <= |center j - center i|.

This is also false (`65/32 = 260/128 > 3/128`). Thus no certificate of this exact
type can represent any packet nonzero at both selected log coordinates.

Such genuine moment-zero packets exist. Choose a smooth compact cutoff `phi`
equal to 1 on a neighborhood of `[0, 1/64]` and put

    k(t) = phi''(t) - phi(t)/4,
    g(x) = exp(-log(x)/2) * k(log(x))  for x > 0,
           0                            for x <= 0.

Then `k(0) = k(1/64) = -1/4`. The existing source provides precisely this
construction: `RHKreinMultiplicativeTransportV1.unliftWeilPacket`,
`lift_unlift`, and `unliftWeilPacket_kreinAtom_moments` in
`b333aacb298fd1908e946b608d4e17d9cb4cca60.lean`, lines 43–53 and 159–192.
Smoothness and compact support give a genuine `WeilCompactSmoothGV1`, and the
Krein differential factor gives both required vanishing moments. The exact
moment calculation is integration by parts against `exp(±t/2)`; the compact
boundary terms vanish. Smooth compact cutoffs with a plateau are standard and
do not require any zeta-zero assumption.

Therefore the universal `hglobal` of this sparse consumer cannot be supplied
without changing its mathematical interface. The local sparse positivity
theorem itself is not refuted by this argument.

The historical Bagua constructor in
`edb1e53d381897a5458792c3c20f1954384d54da.lean`, lines 330–355, does not evade the
obstruction. Its conclusion is a certificate for the already supplied sparse
sum `packetSum (rotatingBaguaCoeff z q) gs`, and its body is literally the tuple
of the supplied family, geometric assumptions, and `rfl`. It does not construct
a sparse representation of an arbitrary source.

## Why the actual universal partition does not feed that consumer

The existing universal Krein partition really does preserve the same arbitrary
source and both moment conditions. The proof in
`b333aacb298fd1908e946b608d4e17d9cb4cca60.lean`, lines 308–355, transports each
localized Krein atom back into a genuine packet and proves exact reconstruction.
This is useful unconditional mathematics, but it produces different local
cutoffs of the original Krein factor; it supplies neither widely separated
centers nor a common translated mother.

Trying to force the widely separated sparse geometry cannot work for the
two-point packet above. Grouping local atoms does not change the source support
and therefore cannot repair this mismatch. A complete proof must instead pay
the actual inter-block Weil interactions, or use a different sufficiently rich
certificate family.

## Concrete local arithmetic producers remain local

The deleted `RHLogThreeSignedPrimeProducerV1` body
`65f36e375b7745bda76e7679c78771fb9f080e0c.lean` contains a genuine nonlocal
two-packet arithmetic producer. Under fine support and moment conditions on one
mother, `actual_two_log_three_gram_coercive` proves

    Re B(g + T_(2 log 3) g, g + T_(2 log 3) g)
      <= -(10517/4800) * energy g.

The prime entry is computed from the true von Mangoldt expression; it is not a
free PSD matrix input. Its actual theorem argument list still fixes this one
same-mother translate pair. It does not cover the differently shaped atoms in
the universal Krein partition.

The stronger L=4/3 body
`a2ee122a68a934933158c018bd13aacbea4bcc3b.lean` proves the complete weighted
Hermitian Weil sign for any finite family in one common half-width-2/3 window,
and a signed bound for fine pairs with center distance at most `509/384`.
These are valid source compositions with actual mixed terms retained. They
cannot cover arbitrary supports or discard inter-window interactions.

Even knowing the sign on every two-atom subfamily is insufficient as a general
matrix argument: a 3-by-3 real Hermitian matrix with diagonal `-1` and every
off-diagonal `3/4` has every 2-by-2 principal block negative definite (eigenvalues
`-1/4, -7/4`), while its all-ones quadratic is `-3 + 6*(3/4) = 3/2 > 0`.
This is an algebraic counterexample to the proposed inference, not a claim
that this matrix is an actual Weil Gram matrix.

The source-correct residual consumer is visible in
`65d2163724a5ac23d4aed62c33ea7bebc8670034.lean`: the universal exact fine
partition and the prime-log-free pair estimates are produced, but all excluded
interactions remain in a signed symmetric residual whose row total must be
bounded by `57430/65536`. The final theorem takes that universal residual
producer explicitly. The log-three pair and bounded common-window producers
do not supply the residual for arbitrary reconstructed families.

## Cofinal/Schur body tracing

No historical constructor was found that supplies the all-packet
`PacketSchurFamily`, `PacketScaledSchurFamily`,
`EveryPacketCofinalLowerCertificate`, or either `UniversalActualCvS...`
approximation premise. Searches included explicit structure field assignments
(`reproducesZeroQuadratic :=`, `schurLower :=`), constructor uses, and instances,
not only module names.

The reviewed `RHCofinalSchurAdapterV1` body
`14795b07bbe8710caf80d99a4bce3bb6bf8932dc.lean` converts an already supplied
actual Schur family and norm convergence into the terminal certificate. The
scaled variant `674022d86e855cca0d2b52ae9932555f66537296.lean` replaces norm
convergence by scaled-error convergence but still takes the family explicitly.
The CvS adapter `665722f84a710f1453dc75fdf10b519db6fe22f0.lean` retains fixed
dimension 139 and L=6/5 in its approximation hypothesis. No substitution of the
ordinary growing-dimension approximation for this hypothesis was justified.

Historical official statements with `apply ...restricted_weil_criterion_v13`
do not supply a lost unconditional producer. In exact blob
`804b71f3f7a226173533088ca42ea95eee429b43.lean`, that theorem's type is
`RestrictedWeilCriterionKernelBridgeV10`, i.e. the implication from the universal
zero quadratic to RH; the next theorem explicitly applies it to an input `h`.
An `apply` in the official theorem leaves this mathematical premise to prove.
Source text containing that tactic is not evidence of a successful complete
Lean proof.

The useful recovered conclusion is thus a precise exclusion: sparse lattice
positivity cannot be promoted through this universal reconstruction interface,
because that interface excludes elementary genuine moment-zero packets. The
remaining general signed interaction bound has not been produced.
