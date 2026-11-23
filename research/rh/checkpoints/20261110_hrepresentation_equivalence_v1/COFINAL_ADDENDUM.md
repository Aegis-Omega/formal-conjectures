# Cofinal variant

Date: 2026-11-10. Evidence kind: `lean_kernel` for the abstract theorem. RH status: OPEN.

`UniversalActualCvSCofinalApproximation` and `UniversalActualCvSLowBlockApproximation`
(`AEGIS_RH_CvS_Cofinal_ActualWeil_JoinV1.lean`) have the shape of `hrepresentation` plus
`Tendsto M atTop atTop`, with the genuine Weil zero quadratic of `g` as the limit. The vectors
`v j` are still not related to `g`.

`RHCofinalRepresentationEquivalenceV1.lean` proves `cofinal_representation_iff_nonneg`: if the
forms are nonnegative for `3 ≤ M` and strictly positive at one fixed vector for every `3 ≤ M`,
the cofinal hypothesis holds if and only if every `zeroSide g` is nonnegative. The witness uses
cutoffs `j + 3` and a real multiple of the fixed vector at each cutoff.

Run: same toolchain and Mathlib revision as `README.md`; `lean --trust=0`, exit 0, no `sorry`;
axioms `[propext, Classical.choice, Quot.sound]`; `leanchecker` exit 0.
Source SHA-256: `b6be78b743ad628de85ac30c6b615a6cabee52bb4f392d0be9c545d42023eab2`.
The module imports `RHRepresentationHypothesisEquivalenceV1` from this directory.

Instantiation (read from source, not compiled here): `projected_lower_L12_of_check` holds for
every `M ≥ 3` and `cert_margin_positive` is strict, so every nonzero vector satisfies the
positivity premise at every cutoff. `Q_CvS M (6/5) atomCenter (R_basis v)` equals
`projectedQ M v` by `hTransport`.

Consequence: both definitions are equivalent to `∀ g, WeilMomentConditionsV1 g → 0 ≤ Z g`.
They are not stronger than the universal sign and the 139-dimensional certificate plays no part
in them. The certificate is bound to `g` only in the window theorems
(`window_of_certificate_gram_moment`, `window_L118`).
