Original-import CI[39571212916](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39571212916) is **SUCCESS** at `9d98c4e99e3ab3d271215192f100964a5fdaac0c`. The full current graph has 82601 declarations, 14 selected roots and 3113 source modules, no missing dependencies or proof cycles, and only standard axioms. Independent artifact validation checked all 1044 binaries. The current run reuses 433 exact-source mathematical modules and freshly compiles 0; earlier fresh compilation is preserved at f118d062. The graph and receipts describe actual finite CvS bounds and a conditional fixed-window result, not unconditional RH.

# STRONGEST_VERIFIED_RESULT_WITH_EXACT_REMAINING_OBLIGATION

The actual finite CvS budget, both original-coefficient consumer contracts and their fixed-window composition are kernel verified. The canonical unconditional RiemannHypothesis theorem remains unproved.

## New verified results

The complete 139-dimensional certificate checks every one of 19,321 ordered output entries. Its actual analytic input join preserves the essential 2*pi normalization and the original interval/projection data. The exact positive margin is 167597168023440173239/604462909807314587353088.

`CvSActualRowConsumerV1.hfin` includes all 301 finite residual rows and the actual Gram-tail majorant. `hB` proves `Brow M c <= 40 * Q_CvS M (6/5) atomCenter c` for every M>=3 and original complex coefficient vector c.

`CvSActualGramWindowV1` proves uniform positivity of the Gram majorant, actual low-form nonnegativity and the exact Schur composition. Its `window_of_trace_le_six` gives nonnegativity of the original indexed zero sum for every admissible moment-zero packet with 2*r<=6/5, under explicit Krein/trace and regularity hypotheses. No hfin/hB or scalar-budget premise remains in that corollary: the new parameterized scalar theorem proves that m>=31/16 and trace budget<=6 suffice, with exact reserve 1/2.

CI 39569164255 at f118d062 accepted all 433 mathematical modules (431 source-identical reuse and two fresh compilations), with 2055 axiom audits. Independent artifact verification checked all 1044 binary hashes and the exact source/pin bindings. Only propext, Classical.choice and Quot.sound occur in accepted audits. The overall run failed later in graph source-path resolution; it is not relabelled SUCCESS. The corrected provenance exporter passed CI 39571212916 at 9d98c4e9 without changing the mathematical sources.

## Exact remaining mathematics

The general verified window theorem retains concrete regular H,d,j,s,cf witnesses, its pointwise Krein inequality for every real t, an actual trace upper bound T, and the compatibility inequality

```
40 <= (2*pi)^2*(6/5)*(m-T/(2*pi)).
```

That is the remaining interface on this fixed-window route. The new specialization m>=31/16 and T<=6 is a proved sufficient range, not a necessary or optimal condition. Its LP candidate is not a proof of the pointwise inequality or trace integral. Finite matrix memberships, basis transport and hfin/hB are already discharged.

For canonical RH a universal obligation remains. The exact existing signed route is:

```lean
∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
  ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
    g = packetSum (fun _ => (1 : ℂ)) gs ∧
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re)
```

`RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget` identifies that universal target; the equivalence is not a proof of its right-hand side. A genuine cofinal-window family and the required exhaustion limit would be another route. One fixed window and a finite congruence identity supply neither universal quantifier.

The work and source-bound receipts are preserved on the existing development branch. No main merge, new branch, changed RH definition, added mathematical axiom, production or billing change was made. No independent human review or unconditional RH success is asserted.

PR90 changed to b0d8b2661132b3ae109c03c16f8b51597251d2e4 on the final API reread. Its new `riemannHypothesis_of_universal_actual_cvs_cofinal` explicitly requires `UniversalActualCvSCofinalApproximation`. This assumes convergence to the actual zero quadratic for every moment-zero packet. Its cofinal parameter is a prime cutoff, not an exhausting window width. The latest dedicated join CI 39568506309 is FAIL; the source is inspected separately, not imported or relabelled as part of our successful graph. No strict-strength claim is inferred from its comments. See actual_input_execution/PR90_B0D8_SOURCE_AUDIT.json.
