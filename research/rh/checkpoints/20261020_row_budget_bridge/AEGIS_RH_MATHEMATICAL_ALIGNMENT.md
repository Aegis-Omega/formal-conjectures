## Exact next source joins

The actual analytic enclosure lemmas already exist. The remaining input step is their finite integration with the literal data, not an assertion that those analytic estimates are absent. Sufficient exact identities are:

```
coeff(columns)(k,i) = CvSActualRowInputL12V1.xBox(k,i)
residual(columns)(r,i) = CvSActualRowInputL12V1.zBox(Lambda96)(r,i)
T[k] = CvSActualRowInputL12V1.tauBox(96, signedFreq(k))
G[k,l] = rationalRange(96, gramRat(150,signedFreq(k),signedFreq(l)), same)
LP2 = CvSFrequencyIntervalV1.lpSquaredInterval(96)
Q[i,j] = upscale(32, Im(CvSProjectedPackedCertificateL12V1.certI,i,j)).
```

Lambda96 must encode the unchanged stored Q48 projection exactly. SourceZ_mem already handles this arbitrary enclosed projection. The Y=E*X and inner X*Lambda interval products are distinct from the now-verified G*X/G*(tau*X) products. Their exact integer reconstruction is preserved for the next staged source join. An identity or rigorously outward containment is sufficient; no input may be silently tightened.

The fixed-window consumer still needs its all-real-t Krein certificate and scalar/trace conditions. Universal closure then requires a cofinal/all-window producer or the existing signed Weil producer for every admissible moment-zero packet. A finite congruence identity preserves the index domain. It does not supply these quantifiers. The time-slice unit-modulus condition remains RH-equivalent and cannot be introduced as an unconditional lemma. No failure of tooling is used as a mathematical nonexistence argument.

## Full-table continuation

The complete ordered 139 by 139 output comparison now passes the native kernel, replacing the earlier first-column-only scope. `CvSFullTableClosureV1.full_table_contains` relates every checked entry to the original Q96 interval envelope, with no unproved output check. `real_envelope_mem` transfers all entries to Q80, retaining exactly six real input-membership families.

`CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs` composes the complete finite table with the original complex interval-box positivity theorem. For every complex vector v it gives

```
delta * sum_i ||v_i||^2 + budgetEnergy(z, tailMatrix(x,g,t,lp2), v)
  <= 40 * Re sum_ij v_i * conjugate(v_j) * q_ij

delta = 167597168023440173239 / 604462909807314587353088 > 0.
```

Its premises are symmetry of q and g and the explicit Q96 memberships of q, x, g, t, z and lp2 in the unchanged literal inputs. It has no output-table, matrix-positivity or RH premise. These memberships still need to be connected to the original CvS definitions; the theorem must not be described as an unconditional actual-CvS bound before that connection is proved.

All 139 input-column caches, 278 original Gram-column products and 19321 ordered output entries compiled. Signed packing includes bounds, lengths and carry control. The source JSON reconstructs byte-for-byte from the original stored Q48 projection and source tables without executing a floating fit. Existing first-column proofs now supply the weighted identities directly, avoiding an unnecessary global re-evaluation. Only proof composition changed; no interval endpoint changed.

The selected new graph has 12 roots, 19752 declarations and 984 located source modules. It has no missing dependency or proof cycle and only the standard three axioms. The 451 inductive/constructor metadata groups are separately condensed. The earlier 102-root graph and original-import CI receipts remain historical evidence in Git and the archived native graph; their scopes are not relabelled.

# Mathematical alignment at the continued source checkpoint

This is a scoped research result, not an unconditional RH proof. Lean is 4.33.1 and Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`. The canonical definition in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185` is unchanged:

```lean
∀ (s : ℂ) (_ : riemannZeta s = 0)
  (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## Source identities and verified scopes

PR #89 is still `5d7425dcc6f4137b2cf3f57bc953504135a388e6`; PR #90 is still `7fc73ce1ae0eb2afbaac778ae8ca8e7fbac07fcc` on the API reread. Work continues on the existing Feshbach branch. No branch, definition, factor or stored interval was replaced. Final published source hashes are recorded in `FINAL_SOURCE_BINDING.json`.

The original-import actual source continuation passed CI 39455515829 at `177dcd648c5497d923586f1d94eb701880389c04`. Its 37 explicit workflow audits pass; the additional emitted `sourceZ_mem` audit also contains only standard axioms. The subsequent first-column continuation is at `f8ff0e2006b6393055dcc97597c79ef3f0dcfcf1`, with all original-import source modules compiled in CI 39463716271. That run failed only because its final Python audit searched the wrong log for two packed soundness declarations. All 105 relevant compiler axiom outputs pass the corrected audit. The overall run remains FAIL; the repaired workflow records validated dependency reuse separately from fresh compilation.

## Local Krein certificate and the universal target

`RHKreinFirstCellV1.firstCell_sound_of_jet_enclosures` has the closed local type `CellAnalyticSoundV1 firstCell`. The literal first cell is `⟨0, 75/4096, 114511397055347687⟩`. Its existing proof supplies the analytic jet enclosures, rather than assuming decimal estimates as axioms. The existing first-fifteen proof and reflective remainder form `RHKreinAllCellsV1.allCellsAnalyticSound`; the literal split uses the first 15 cells and the remaining serialized cells.

The existing terminal `RHKreinAllCellsV1.zero_quadratic_margin_two_fifths` quantifies over `g,r,a` and explicitly requires `0 ≤ r`, `r ≤ 2/5`, `HalfWidthAt g r a` and `WeilMomentConditionsV1 g`. Its conclusion is `(1/16) energy(g) ≤ Re(∑' rho, WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho)`, using the actual indexed nontrivial-zero sum. This continuation does not erase the support condition or claim a fresh replay of the whole 2,199-cell DAG. That earlier analytic source chain is distinct from the new native interval graph.

## Actual CvS coordinates and residual

The fixed window is `L=6/5`. There are 139 atom coefficients, 141 Fourier rows indexed by `signedFreq k=k.val-70`, and 301 finite residual rows indexed by `rowIndex r=r.val-150`. Fourier indices are not zeta-zero ordinates.

`sourceY_eq_actual_crossRow` already proves the exact complex cross-row transport in the original context. There is no missing new positivity principle for the finite congruence identity. The source kernel normalization is

```
K_M(m,n) = π (cvsEntry M (6/5) n m + cvsEntry M (6/5) m n),
K_M(n,n) = 2π cvsEntry M (6/5) n n,
K_M(m,n) = ((6/5)/π) (tau(n)-tau(m))/(n-m),   m≠n.
```

`CvSActualRowInputL12V1` encloses the actual transformed coefficients, exact rational harmonic Gram upper kernel, signed diagonal, actual cross kernel and sourceY. These statements retain `M≥3` and the stated frequency ranges. `sourceZ_mem` now encloses all 301 residual rows for every real projection whose entries have the supplied Q96 enclosures. On rows `80≤r.val<221` it is exactly `sourceY−X*Lambda`; on the outer rows it is sourceY. Its `hLam` hypothesis is explicit and does not assert arbitrary projection data are valid.

## Exact interval envelope and the new proofs

For the proposed exact Q48 projection, the unchanged interval computation is

```
C = 40 Q - ZᵀZ - (L/π)² [2 (diag(tau)X)ᵀ G (diag(tau)X) + 338 Xᵀ G X].
```

Here `338=2*13²`, corresponding to the existing Gram-tail estimate with Young parameter 1 and far tau bound 13. The remaining tail/residual identification must preserve this normalization. G is the matrix representation of the proved Gram-tail majorant; equality of its diagonal upper bound with the exact infinite tail is not required.

`CvSIntervalMatrixProductV1` proves the outward midpoint-radius dot and matrix product. `CvSRowBudgetEnvelopeV1.envelope_mem` composes those input memberships, and `stored_envelope_mem_of_check` transports the result into the stored Q80 box only after its concrete output comparison is proved.

New `CvSColumnEnvelopeV1.envelope_pair_eq` identifies a mixed entry of the original finite envelope with a list computation that reuses a right Gram column. All lengths and weighted-column identities are explicit. It holds at every finite size, without a symmetry or positivity premise. It is an equality of computations, not a positivity theorem at every size.

Fourteen kernel-checked batches now cover all 139 entries of the first stored column. They check the weighted columns, numerical envelope containment, exact identity with the original stored target boxes, and row order. `RowBudgetFirstColumnV1.first_column_contains`, `first_column_mem` and `all_rows_covered` compose these checks. The batch kernel time totals 357.111 seconds. This is 139 of 19,321 output entries; it does not identify every literal analytic input or supply the full hI premise.

The new packed extension reuses `CvSPackedGramV1.gramEntry_eq`. `packedIntervalDot_eq` expresses the original center and radius as four exact signed dot products; its length, component and carry bounds are explicit. `cachedIntervalDot_eq` permits reuse only after exact cache-preparation identities. All rounding remains identical. A 301-element unchanged Z0 pilot checks the complete cache, signed component and carry bounds, exact output, equality to the old dot, and rejection of one corrupted packed coefficient. No full-matrix speedup or full-matrix proof is inferred from this pilot.

## Exact next interfaces

The existing consumer is `CvSRowBudgetGramBridgeV1.budgetEnergy_le_of_Iv`. It requires symmetry and **every** stored entry to enclose `40*A(i,j)-budgetMatrix Z G(i,j)` at Q80. Our first-column result supplies a checked computation for one column; it does not discharge this universal-over-entries premise. The literal Q96 inputs must be identified with the actual source formulas, all output entries must be covered, and the actual complex residual/tail must match the consumer.

The existing `CvSGramTailV1.rows_gram_le` already bounds every outer cutoff N by a right side independent of N, under its explicit finite support, far-tau and positive Young-parameter hypotheses. That uniform tail theorem is preserved; it is not a missing all-frequency estimate. It controls frequency exhaustion for a fixed window, rather than supplying positivity at every window width.

The next window consumer is `CvSWindowGramL12V1.window_L12_gram`. Even after the row budget it retains an all-real-t Krein certificate, integrability/trace hypotheses and the scalar Schur-gap inequality. Its conclusion covers packets with `2r≤6/5`, not every packet.

The existing universal sharp target is exactly:

```text
∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
  ∃ n (gs : Fin (n+1) → WeilCompactSmoothGV1),
    g = packetSum (fun _ => (1 : ℂ)) gs ∧
    actualMixedDefect n gs ≤ -(∑ i, (B (gs i) (gs i)).re).
```

`RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget` proves equivalence with RH. This is an explicit remaining mathematical obligation, not a premise-free RH proof. Its hselect alternative chooses one certified reconstruction for each admitted source/decomposition; it does not bound every arbitrary decomposition. Absolute Schur bounds can lose cancellation; no uniform mixed-cost bound is inferred from the eleven-shift or any fixed matrix certificate.

## Closing-route comparison

| Route | Proved logical relation | Current decisive obligation |
| --- | --- | --- |
| Adaptive actual Schur selector hselect | Sufficient for RH; no converse or strict-strength claim is established here | For each admitted source packet, construct one exact reconstruction and its actual diagonal/mixed weights within 46688/65536. |
| Sharp signed mixed budget | Exactly RH-equivalent by the existing source theorem | Prove the universal signed inequality from independent analytic information; the equivalence supplies no sign. |
| Local Krein positivity plus transfer | The existing bounded-support theorem is a scoped local result | Supply a cofinal/all-window producer, or a valid density/continuity argument controlling the form on every finite combination. |

A spanning or dense collection of individually positive vectors is insufficient by itself: the real symmetric matrix [[1,2],[2,1]] is positive on each coordinate vector, but its quadratic form at (1,-1) is -2. This is a countertest to the proposed inference, not a counterexample about the actual Weil form. Likewise, a successful finite certificate gives no all-dimension or all-window quantifier.

PR90's existing `radius_row_real` bounds projected-entry approximation radii by 1/230000. That is a different matrix quantity from the cross-residual-plus-tail hB. It cannot be substituted for the missing hI/hB producer. Cached exact arithmetic changes execution cost, not these analytic Schur budgets.

## Verification boundary

The native selected graph now contains 102 roots, 28,139 declarations and 1,058 located source modules. It has zero missing dependencies and zero theorem/definition cycles; 684 inductive/constructor metadata groups are separately condensed. All axioms are among propext, Classical.choice and Quot.sound. Native RHFixInterval and PackedGram copies change only imports; their complete mathematical bodies are byte-identical after import-line removal. Original-import analytic CI is a separate receipt. The new packed closure was also freshly compiled from the published archive in an isolated custom-module directory: 11 modules, same host, no pre-existing custom module cache. No independent human mathematical sign-off or unconditional RH theorem is claimed.

Final verification: exact-source CI [39470677222](https://github.com/tarikskalic33/formal-conjectures/actions/runs/39470677222) passed at `16d487f11ed122113c186c573b9268f5bfc4d1e7`. All 105 explicit type/axiom re-audits pass after validating the 166 reused f8ff0e20 dependencies against source, pin, log and binary hashes. The earlier f8ff0e20 source compilation and its audit-routing CI failure remain distinct evidence. The new packed extension additionally passes the isolated 11-module native reproduction. No unconditional RH claim follows.
