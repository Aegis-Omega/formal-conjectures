# Independent audit of the eleven-window shape composition

Verdict: the displayed mathematical composition is valid on its stated
common-window domain. No missing analytic premise or algebraic error was
found in the passage from the existing same-mother bounds to independent
shapes. This is an ordinary mathematical audit, not a kernel verification
of the new analytic adapter or of the full imported analytic closure.

The inspected checkout is detached at
`1f70364296eee931d0cae5ecc16a0c9810c0c4cc`. Its actual Git blob for
`AEGISOverlay/RHActualElevenLatticeV1.lean` is
`97a98db382e433488ed20f7df0980f41b20e4cbc`, as specified. The inspected
`AEGISOverlay/RHWeightedSchurV1.lean` has blob
`1860b9a94d1fd5dec368283c6c914effab053cc3`.

## Analytic input and domain

`all_actual_eleven_mixed_bounds` has the full complex-norm conclusion
`norm(B(T_i w,T_j w)) <= c_ij E(w)` for every legal mother `w` in the
specified window and all distinct indices. Its premises are exactly that
common window and the two moment conditions; its displayed proof reduces
all gaps1--10 to the corresponding actual source bounds. This is stronger
than a real-part-only estimate and is the input the polarization uses.

The common-window legal functions form a complex vector space: finite
addition and scaling preserve compact smooth positive support, the common
logarithmic support interval and both linear zero moments. Translation is
the linear half-density map `T_s u(x)=exp(-s/2)u(exp(-s)x)`. Thus
`S(u,v)=B(T_i u,T_j v)` is linear in its first argument and conjugate-linear
in its second. The actual `B_add_left/right` and `B_scale_left/right`
conventions agree with this choice. The source energy is the ordinary
integral of `norm(u)^2`, so its homogeneity and parallelogram laws require
no positivity assumption about the Weil form.

## Polarization, reciprocal scaling and zero energies

For this possibly non-Hermitian `S`, direct expansion gives exactly

    4S(u,v)=q(u+v)-q(u-v)+i q(u+iv)-i q(u-iv), q(w)=S(w,w).

The signs of the two imaginary terms are correct for the source convention.
Applying the norm bound to all four legal mothers and adding the two L2
parallelogram identities yields `|S(u,v)| <= c_ij(E(u)+E(v))`.

For every real `r>0`, the two scaled mothers remain legal and
`S(ru,r^-1 v)=S(u,v)`. Hence

    |S(u,v)| <= c_ij(r^2 E(u)+r^-2 E(v)).

When both energies are positive, `r=(E(v)/E(u))^(1/4)` gives
`|S(u,v)| <= 2c_ij sqrt(E(u))sqrt(E(v))`. When `E(u)=0`, let `r` increase
without bound; when `E(v)=0`, let `r` decrease to zero. The fixed left
side is then zero. If both energies vanish it is zero already. These
arguments use only limits of scalar bounds, with no continuity or limit
interchange for `B`, integrals or zero sums. Alternatively ordinary
continuous-packet L2 energy zero implies the packet is identically zero.

The factor2 is necessary for this general inference: on C² the form
`S(u,v)=2u_1 conjugate(v_2)` satisfies `|q(w)|<=||w||²` and
`S(e_1,e_2)=2`. No Hermitian numerical-radius shortcut was used.

## Existing weights, exact rows and the consumer

The original weights are retained unchanged:
`(427,355,24,24,24,24,24,24,24,355,427)`. A separate delegated audit using
fresh `Fraction` arithmetic, with no archived code execution or optimization,
confirmed the eleven exact rows for the original exact costs:

    i=0,10: 225089/315980;
    i=1,9:  25289/35500;
    i=2,...,8: 427/600.

The maximum is `S=25289/35500`, attained only at1 and9. Doubling the cost
matrix doubles every row, including all110 ordered off-diagonal entries;
the zero diagonal remains excluded. These exact costs are supported by
the original mixed theorem. The source's Q16 row theorem is a separate
rounded statement and is not being silently substituted for these rows.

The existing `weighted_gram_variable_energy` accepts precisely the derived
cross input with cost matrix `2c`, diagonal constant `D=5671/3200`, original
positive weights, individual nonnegative energies, and row constant `2S`.
It imposes no equal-energy or common-shape premise. Its real Gram conclusion
and the finite sesquilinear expansion therefore give

    -Re B(sum_i z_i T_i h_i, sum_i z_i T_i h_i)
      >= (394709/1136000) sum_i E(h_i)|z_i|²,
    5671/3200 - 2(25289/35500) = 394709/1136000 > 0.

Zero packets, zero coefficients and arbitrary complex phases are covered.
If a mother itself is a finite within-window combination, its energy is
the energy of that actual sum, retaining its L2 mixed terms. Replacing it
by a sum of constituent energies would be a different, unproved statement.

## Verification boundary

The integer-only kernel receipt was read and its stated scope retained.
It is not evidence that the new actual-B analytic adapter compiled. This
audit did not build Lean, rerun the Schur proof, optimize weights, execute
archived scripts, or change GitHub. Local reads and the audit-file write
were available; no usage or tool limit prevented this mathematical review.

The zero-side conclusion uses the separately existing moment-zero explicit
formula with its original multiplicities and convergence. The new finite
sum preserves both moments, so the source theorem applies mathematically;
its full import closure was not independently rebuilt in this audit.

The result is infinite-dimensional in the independent shapes, but its
geometry remains exactly the eleven translated copies of the one common
source window. Arbitrary-center reconstruction does not place an arbitrary
legal test in this union. No global-support or RH conclusion follows here.
