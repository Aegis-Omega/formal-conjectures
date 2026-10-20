# STRONGEST_VERIFIED_RESULT_WITH_EXACT_REMAINING_OBLIGATION

No unconditional RiemannHypothesis theorem was constructed.

Verified progress: the existing source now has a kernel-proved original bigCheck, unconditional actual low-block coercivity at L=6/5, a uniform Gram tail and the R1 tau boxes through 150. Those are verified at exact source 6230b75b, green CI 39379596732. This session adds four dimension-independent native Lean algebra/enclosure lemmas and a new n=139 exact interval-box certificate with positive margin 335194336046880346478/2^80, checked by the pinned Lean kernel in 96.35 seconds. All new printed axiom lists are standard; the Boolean certificate uses only propext and its integer margin needs no axioms.

Exact immediate obligation: let X=atomWeight*R and let Lambda be the stored rational projection. Let Z_m be the actual cross-row coefficient of X minus X*Lambda on rows |m|<=70, and the actual cross-row coefficient of X on rows 70<|m|<=150. Let G=gramUp 150 and D=diag(tau_n), |n|<=70. Prove entrywise enclosure of

C = 40*projectedEntry - Z^T Z - (L/pi)^2*(2*(D X)^T G (D X) + 338*X^T G X), L=6/5,

in the generated Q80 intervals. The new scalar/product/Gram lemmas and source tau/diag/pi boxes supply the ingredients, but this instantiation is not yet a Lean theorem. With it, the existing packed soundness and signed matrix lemma yield the actual relative row budget. No floating witness correctness is needed.

Then the fixed-window consumer still needs a proved all-real-t Krein certificate, its slack trace integral bound and a compatible positive Schur gap. The numerical LP/trace results alone are not those proofs.

For canonical RH, the exact universal actual signed obligation remains:

forall g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g ->
  exists n (gs : Fin (n+1) -> WeilCompactSmoothGV1),
    g = packetSum (fun _ => (1 : Complex)) gs and
    actualMixedDefect n gs <= -(sum i, (B (gs i) (gs i)).re).

The existing rh_iff_one_actual_sharp_signed_budget consumes this universal statement. It is not proved by one L=6/5 window. A cofinal/universal producer or another actual universal analytic argument is still required. This is a precise outstanding obligation, not a claim that no proof exists elsewhere.

All checkpoint source, input data and receipts are committed to the existing development branch. No new branch, force push, main mutation, merge, production or billing action is used.
