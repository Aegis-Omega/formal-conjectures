# `hrepresentation` is equivalent to its own conclusion

Date: 2026-11-10. RH status: OPEN (unchanged).
Evidence kind: `lean_kernel` for the abstract theorem below. The instantiation to `projectedQ`
is read from source and was NOT compiled in this run.

## Finding

`AEGIS.RHCvSUniversalSignKernelV1.universal_nonnegative_of_projected_sequence`
(`AEGIS_RH_CvS_UniversalSignKernelV1.lean`) assumes

    hrepresentation : ∀ g, ∃ (M : ℕ → ℕ) (v : ℕ → Fin 139 → ℂ),
      (∀ j, 3 ≤ M j) ∧ Tendsto (fun j => projectedQ (M j) (v j)) atTop (𝓝 (zeroSide g))

and concludes `∀ g, 0 ≤ zeroSide g`. The hypothesis and the conclusion are logically equivalent.
Given `0 ≤ zeroSide g`, the constant sequence `M j = 3`, `v j = sqrt (zeroSide g / q0) • v0`
(with `q0 = projectedQ 3 v0 > 0`) satisfies the hypothesis. Nothing in `hrepresentation` ties
the vectors `v j` to the object `g`.

So an unconditional producer of `hrepresentation` is exactly as hard as the sign statement it is
meant to deliver. The theorem is correct, but as formalized it moves no difficulty.

## Kernel-checked here

`RHRepresentationHypothesisEquivalenceV1.lean` (imports Mathlib only):

- `quadRe E v` is the body of `projectedQ` with the entry matrix `E` left abstract.
- `quadRe_smul`: `quadRe E (c • v) = c ^ 2 * quadRe E v` for real `c`.
- `representation_iff_nonneg`: if `quadRe (E M)` is nonnegative for `3 ≤ M` and
  `0 < quadRe (E 3) v0` for one `v0`, then the hypothesis of the shape above holds
  if and only if `∀ g, 0 ≤ zeroSide g`.

Run: Lean 4.33.1 (githash `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, `lean --trust=0`, exit 0, no `sorry`.
`#print axioms` for both theorems: `[propext, Classical.choice, Quot.sound]`.
`leanchecker --verbose RHRepresentationHypothesisEquivalenceV1`: exit 0.
Source SHA-256: `9fa929c4dd94b9ee62fa1f8de46b2f37aa1bc2e236ffdc4f38e6fde69fe1fa27`.

## Instantiation to `projectedQ` (read from source, not compiled here)

- `n = 139`, `E = projectedEntry`; `projectedQ M v` unfolds to `quadRe (projectedEntry M) v`
  (`research/rh/feshbach_lean_v1/CvSProjectedSchurBridgeL12V1.lean`).
- `hnonneg` is `AEGIS.RHCvSKernelFiniteV1.certified_source_projectedQ_nonneg`.
- `hpos`: `projected_lower_L12_of_check` gives
  `(certEps - certEta) * ∑ ‖v i‖ ^ 2 ≤ 2 ^ certQ * projectedQ M v`, and `cert_margin_positive`
  is strict, so every nonzero `v0` works.

Not compiled here because the CvS import chain reaches `Lc.*` and `Hadamard.*`, which are
fetched only inside the CI workflows.

## Consequence

To carry content, the hypothesis has to bind the sequence to `g`: `v j` must be the coefficient
vector of `g` (or of approximants of `g`) in the CvS basis, and `projectedQ (M j) (v j)` must be
shown to converge to the Weil zero-side value of that same `g`. That same-object convergence is
the open obligation. It is not expressed by the current `hrepresentation`.

## Not claimed

No sign of any Weil functional is proved. Nothing here bears on the truth of RH.
`hresidual` (`AEGISOverlay/RHPrimeFreeRecompositionJoinV1.lean`) is not covered: it is not
equivalent to its conclusion in this way and remains unassessed.
