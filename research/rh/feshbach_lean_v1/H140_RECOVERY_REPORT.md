# H140 recovery and finite residual transfer

Recovery base: `tarikskalic33/formal-conjectures`, existing branch
`proof/rh-feshbach-schur-v1`, commit
`9f6abc070b833df36e7fc7476ed306c9fef5ab14`.
PR #89 remains at `da0103e7afa0bb0ade1441f87d01e1b9416ef9c4`.

## Original artifacts

**LOCAL_H140_ARTIFACTS_NOT_ACCESSIBLE.** The indicated Claude scratchpad is
not mounted in this environment. Searches of the checkout, ignored files,
workspace results, `/tmp`, and the available agent home did not recover
`CvSPackedGramV1.lean`, `packed.lean`, `c40.lean`, a Hilbert H140 certificate,
its generator, or its 14-theorem audit. Exact original artifact hashes are
therefore unknown. No original certificate has been recreated or certified.

The supplied screenshots identify H140 as the **Hilbert matrix demonstration**
of Claude's packed Gram checker. They report a 143-second kernel test and a
26-second generator, followed by a generated-source line-wrapping repair.
The stated 14/14 audit and approximately 215-second final validation remain
unreproduced reports. H140 does not identify an actual CvS/Weil matrix in this
evidence. No positivity margin, rounding precision, or packing width has been
recovered.

The earlier run [39223778272](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39223778272)
is successful at the base SHA. Its `krein-ring` job contains 110 successful
axiom audits and no H140 source or artifact. It certifies the existing
Feshbach source closure, not Claude's missing checker or the new source below.

## New, independently checked work

`CvSResidualCertificateV1.lean` is a new reconstruction of the residual-transfer
argument, not a recovered Claude file. Five lemmas compile with Lean 4.33.1
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`:

* `residual_entry_le`: the scalar quadratic estimate for a signed entry.
* `abs_sub_le_of_enclosure`: an entry interval gives an outward error radius.
* `residual_quadratic_le`: a symmetric entry majorant with row sums at most
  epsilon bounds the real residual quadratic form by epsilon times the
  squared Euclidean norm.
* `actual_quadratic_nonneg`: transfers an epsilon-coercive centre matrix to
  the actual matrix under that residual budget.
* `actual_hermitian_nonneg`: gives nonnegativity of the real part of the
  complex quadratic form for the real actual matrix.

The final statement, for any finite index type, has these explicit inputs:

```
abs (A i j - A0 i j) <= R i j
R i j = R j i
sum_j R i j <= epsilon
epsilon * sum_i (x i)^2 <= sum_ij x i * x j * A0 i j   for every real x
```

Its conclusion is `0 <= Re(sum_ij conj(z i) * z j * A i j)` for every complex
`z`. Symmetry of `R` is essential to this row argument. The theorem does not
assert that an arbitrary input `A` is symmetric; a Hermitian matrix claim
also requires the actual matrix's symmetry. For CvS entries this is the
separate existing `CvSRowTailV1.cvsEntry_symm` theorem.

Every new lemma's `#print axioms` output is exactly a subset of
`propext`, `Classical.choice`, and `Quot.sound`. There are no new axioms,
placeholders, floating-point computations, or uses of `native_decide`.

The regression file checks the sharp singular boundary (centre `2 I`,
all-one entry radius, row budget `2`), the failure of a one-sided nonsymmetric
row argument, rejection of an underestimated row budget, and rejection of
an inward-rounded sub-ulp upper bound. It does not benchmark H140.

Reproduction from the repository root:

```bash
mkdir -p .lake/feshbach
lake env lean -DwarningAsError=true -o .lake/feshbach/CvSResidualCertificateV1.olean research/rh/feshbach_lean_v1/CvSResidualCertificateV1.lean
export LEAN_PATH="$PWD/.lake/feshbach:$(lake env printenv LEAN_PATH)"
lake env lean -DwarningAsError=true research/rh/feshbach_lean_v1/tests/CvSResidualCertificateTestV1.lean
```

The existing Feshbach workflow now runs these checks and audits all five
new named lemmas. Its earlier jobs and mathematical consumers are retained.

## Relation to exact LDLT and the RH spine

The existing `RHExactLDLTV1.ldltCheck_sound` certifies the rational centre's
quadratic form from an exact factorization. To use it here, one needs an
LDLT certificate for the **shifted** centre `A0 - epsilon I`, together with
the index, rational-cast, and diagonal identities. Positivity of unshifted
`A0` alone does not supply the coercivity input. No H140 factorization was
available to instantiate this step.

The actual CvS matrix is the existing `CvSLowBlockMatrixV1.cvsEntry M LT`.
Its definition includes the factor `1 / (2*pi)`, the integral against
`hplus`, and the finite prime block. Neither its definition nor the Fourier
normalization has been changed.

The nearest window consumer is
`CvSRowTailV1.window_of_certificate_tail`. Its `hlow` requires, for **every**
low-block coefficient vector `c`, the actual CvS quadratic form to dominate

```
Brow c / (2*pi*LT) / (m - T/(2*pi)).
```

Its `hfin` separately bounds the finite cross rows **plus** the explicit
`rowTail`; `hcpos` requires `0 < m - T/(2*pi)`. It also requires a genuine
Krein pointwise certificate and the trace/slack bound. A bare positive
Hilbert matrix discharges none of these premises. The new residual theorem
can certify a correctly assembled real Schur matrix only after those matrix
identities and actual entry enclosures are supplied. No application to the
CvS consumer has succeeded in this session.

The precise next finite obligation is to supply source-derived entry
enclosures for that actual Schur matrix and an epsilon-shifted centre
certificate whose residual row budget fits the proved margin. The missing
Claude packing source would additionally need its signed-digit and carry
soundness audit before its benchmark could be reproduced.

A certified fixed finite matrix or fixed window would still require the
existing cofinal/all-window producer and limiting control before the
canonical unconditional `RiemannHypothesis` target follows. This session
does not claim that target or a recovered H140 kernel certificate.
