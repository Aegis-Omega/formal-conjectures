> Current verified result: CI39569164255 at f118d062 accepted all433 mathematical modules (431 source-verified reuse, two fresh source compilations), with2055 axiom roots. The actual hfin/hB-to-window composition and uniform scalar theorem are PASS with standard axioms. All1044 artifact binary hashes and exact sources were independently validated. The run failed only in subsequent graph source resolution; this is not a whole-run SUCCESS. CI39571212916 at9d98c4e9 checks the repaired graph provenance using the same433 verified modules. ACTUAL_WINDOW_KERNEL_PASS.json contains the complete new terminal types and audits. Earlier pending replay wording below is historical and superseded by this receipt.

# Mathematical alignment

Status: **STRONGEST_VERIFIED_RESULT_WITH_EXACT_REMAINING_OBLIGATION**. No unconditional RH theorem is asserted.

## Source and canonical target

Repository: `tarikskalic33/formal-conjectures`; existing branch: `proof/rh-feshbach-schur-v1`. The current mathematical source snapshot is `7cc836ab5f6dff66b5643c9838d9c79d330ab68e`. On the 2026-10-21 API reread, PR89 is `5d7425dcc6f4137b2cf3f57bc953504135a388e6` and PR90 is `7fc73ce1ae0eb2afbaac778ae8ca8e7fbac07fcc`. Neither PR was merged or overwritten.

Lean is 4.33.1; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. The existing Li provider is `35df682f3b709ffe5fbcfdd452dfa964bd622b87`, built with the recorded PR53 recipe. The canonical Mathlib definition is unchanged:

```lean
∀ (s : ℂ) (_ : riemannZeta s = 0)
  (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## Existing local Krein chain

`RHKreinFirstCellV1.firstCell_sound_of_jet_enclosures` concludes `CellAnalyticSoundV1 firstCell`, where `firstCell = ⟨0,75/4096,114511397055347687⟩`. The original analytic jet enclosures, first-fifteen proof and reflective remainder feed `RHKreinAllCellsV1.allCellsAnalyticSound`.

`RHKreinAllCellsV1.zero_quadratic_margin_two_fifths` retains `0 ≤ r`, `r ≤ 2/5`, `HalfWidthAt g r a` and `WeilMomentConditionsV1 g`. It controls the actual indexed nontrivial-zero sum by `(1/16) energy(g)`. Its bounded support domain is not the universal Weil domain. This session does not claim a fresh replay of all 2,199 cells.

## Complete finite certificate and actual analytic inputs

The actual finite certificate has 139 atom coefficients, 141 Fourier frequencies `-70..70`, and 301 residual rows `-150..150`. It differs from the recovered Hilbert H140 stress test. All 19,321 ordered output comparisons, all 278 Gram-column products and all 139 packing witnesses passed original-import CI39505154095 at `2d2ea90d`: 445 freshly compiled modules, 868 standard-axiom audits, and 611 independently hash-validated compiled binaries.

`CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs` first proves a complex row budget with six explicit real input-membership families and symmetry. Its exact positive margin is

```
delta = 167597168023440173239 / 604462909807314587353088.
```

The analytic-to-literal join is now proved, rather than left as an input premise. At source `96e25af7`, CI39538781739 freshly accepted `CvSActualLiteralInputsV1` and `CvSActualBasisBudgetV1`, plus the three unchanged basis modules. `actual_budgetEnergy_margin` quantifies over every M>=3 and every complex coefficient vector; the six actual memberships and symmetries are discharged using the original analytic enclosure lemmas. `actualBudget_le_original` transports the resulting inequality to the actual `Q_CvS` form. That CI later failed in a different consumer module; the five named module results remain PASS, not a whole-run success.

The cross kernel is **2*pi times** the signed low-block kernel. Accordingly `X^T Y = 2*pi*projectedEntry`; the Q enclosure uses the rigorously enclosed inverse `2*pi`. The unnormalized substitution is explicitly rejected. Original Q48 projection entries and every interval endpoint remain unchanged.

## Original coefficient contracts

At source `d6c13a47`, CI39541303124 accepted the complete `CvSActualRowConsumerV1` module and the unchanged `CvSTauFarL12V1`. Its `hfin` bounds the actual finite residual rows plus the actual Gram-tail majorant by `Brow M c`, for every original coefficient vector c. Its `hB` gives

```
Brow M c <= 40 * Q_CvS M (6/5) atomCenter c,    M >= 3.
```

Surjectivity of the existing basis transformation discharges the original-coordinate quantifier. No Frobenius estimate or norm loss replaces the relative budget. The residual identity subtracts X*Lambda exactly on Fourier rows -70..70; all 301 residual rows are retained. Complex conjugation is preserved. `HFIN_HB_KERNEL_PASS.json` records full compiler types and standard-axiom audits. The overall run later failed only in the new window wrapper.

## Window composition and scalar improvement

Source `7cc836ab` repairs that wrapper and adds `CvSKreinScalarUniformV1`. The scalar module passed native kernel execution; its original-import replay and the window wrapper are being checked in CI39543410933. Until its receipts say PASS, those new original-import roots are candidates.

The uniform scalar theorem proves, for real m,T,

```
m >= 31/16, T <= 6
  ==> m-T/(2*pi) >= 15/16
  ==> 40+1/2 <= (2*pi)^2*(6/5)*(m-T/(2*pi)).
```

`CvSActualGramWindowV1.window_of_actual_rows` composes hfin/hB with the existing `window_of_certificate_gram`. `window_of_trace_le_six` uses the new scalar theorem. Both retain the actual all-real-t Krein inequality, the integrable trace witness, regularity and support hypotheses. Their conclusion concerns the original indexed zero sum for moment-zero g with `HalfWidthAt g r a` and `2*r <= 6/5`.

The newly reconstructed `UNTRUSTED_KREIN_*` LP data are numerical witness candidates only. Their validator text does not prove the all-real-t inequality or trace integral in Lean.

## Exact remaining obligations

To instantiate the fixed-window result, construct concrete H,d,j,s,cf satisfying its regularity/support hypotheses, prove the stated pointwise Krein inequality for **every real t**, and prove the actual trace integral is at most 6 with m>=31/16. The numerical feasibility evidence is not such a proof.

After that, universal closure still needs a cofinal/all-window producer with a proved exhaustion limit, or the actual signed mixed-budget producer for every admissible moment-zero Weil packet. `RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget` states an equivalent obligation; it does not supply its proof. Its optimized row producer selects one certified reconstruction per packet, not every arbitrary decomposition.

Time-slice unit modulus at nonzero log shift is equivalent to the critical real coordinate. No unconditional unitary-transport premise, new axiom, changed RH definition, or finite-to-universal inference is introduced.

## Verification boundaries

Successful named modules in a later failed run are distinguished from whole-run PASS. Native narrowed-import replay, original-import CI, validated binary reuse and fresh compilation have separate receipts. The historical graphs and source snapshots remain in Git; the active machine graph and kernel receipt specify their own scope. Missing tooling is not used to infer mathematical impossibility.
