# STRONGEST_VERIFIED_RESULT_WITH_EXACT_REMAINING_OBLIGATION

No term of `unconditional_riemannHypothesis : RiemannHypothesis` was constructed. No new axiom or weakened Mathlib definition was introduced.

The concrete new result is a native kernel-verified complete first column of the existing Q96/Q80 interval envelope: all 139 entries match their original target boxes and have the checked containment, weighted-column and row-order proofs. The composition theorems are `RowBudgetFirstColumnV1.first_column_contains`, `first_column_mem` and `all_rows_covered`. They cover 139 of 19,321 entries. They are not by themselves entry enclosures of the actual analytic matrix.

A uniform new execution theorem, `CvSColumnEnvelopeV1.envelope_pair_eq`, preserves the exact mixed entry at every finite dimension. Another, `CvSPackedIntervalDotV1.cachedIntervalDot_eq`, proves that signed, carry-safe cached packing gives exactly the existing outward interval dot. Its real 301-element Z0 pilot passes all six kernel audits, including rejection of corrupted packing. These are proved computational identities, not dimension-uniform positivity claims.

The actual-source input continuation at commit 177dcd64 passed original-import CI 39455515829. It includes sourceZ_mem for every one of the 301 residual rows, every atom index, M≥3 and every explicitly enclosed real projection. The observed 37 workflow audits and the additional emitted sourceZ audit all use only standard axioms. The new first-column original-import CI 39463716271 at f8ff0e20 is recorded separately; consult the machine receipt for its final status. The packed-dot extension is native-verified and is outside that CI scope.

The selected native graph has 102 roots, 28,139 declarations, 1,058 located sources, no missing dependencies and no proof cycles. All axioms are standard. Raw graphs, exact custom sources, full compiler outputs and immutable source bindings are preserved alongside this report. No independent human review or global proof sign-off is implied.

## Immediate finite obligation

Identify the literal Q96 data with the already proved actual Q/X/G/tau/Z/LP2 input formulas and the chosen exact rational projection. Prove every stored output entry encloses the actual matrix

```
40*A(i,j) - budgetMatrix(actualZ, actualGramTail)(i,j).
```

The pure finite comparison may use the existing hull/tableCheck or a complete entrywise producer. One sufficient explicit target remains

```
tableCheck 139 target (fun i j => downscale 16 (hull
  (envelope 96 Q X G tau Z LP2 i j)
  (envelope 96 Q X G tau Z LP2 j i))) = true.
```

The first column and the new packed evaluator are verified progress toward that target; the full Boolean has not been proved. `CvSRowBudgetGramBridgeV1.budgetEnergy_le_of_Iv` consumes the completed hI, with its symmetry hypotheses, once the actual residual and tail are identified. The existing finite positive certificate and its margin are preserved.

## Remaining analytic and universal obligation

The fixed-window consumer still requires a genuine all-real-t Krein certificate, trace/integrability control and the compatible scalar gap. A certificate for L=6/5 does not imply a cofinal/all-window family.

The exact universal target retained from `rh_iff_one_actual_sharp_signed_budget` is

```text
∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
  ∃ n (gs : Fin (n+1) → WeilCompactSmoothGV1),
    g = packetSum (fun _ => (1 : ℂ)) gs ∧
    actualMixedDefect n gs ≤ -(∑ i, (B (gs i) (gs i)).re).
```

It is RH-equivalent. Requiring it as an assumption would not close RH. The hselect route instead needs one valid selected reconstruction per supplied source packet/decomposition; arbitrary repeated or nearly coincident decompositions are not required to pass. Neither an RH-independent universal signed estimate nor such a universal Schur selector is constructed here.

The earlier route review therefore remains scoped: continue the actual finite Feshbach component and targeted signed estimates; hold universal promotion until a non-circular producer is proved. This is a mathematical gap, not a claim that an uncompiled or unexamined source has no proof.
