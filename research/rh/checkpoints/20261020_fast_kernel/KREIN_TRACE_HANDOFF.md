# Krein and trace premises at L = 6/5: handoff for other agents (2026-10-24)

Status: open. One window only. Not RH.

Read this before you write any new Lean for the L = 6/5 window. It lists what already exists,
the chosen route, the numbers, the Lean plan and the traps. Branch: `proof/rh-feshbach-schur-v1`.

## 1. Where the window stands

The conclusion we want is the one in
`row_budget_bridge/CvSActualMomentWindowJoinV1.window_of_actual_rows_moment`:

```
0 ≤ (∑' ρ, WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) ρ).re
```

It holds for moment-zero `g` with `HalfWidthAt g r a` and `2r ≤ 6/5`. That is **one window**. It
is **not** Weil positivity for all test functions, so it is **not** RH.

**Already closed in Lean**
- The row budget: `hfin` and `hB` (κ = 40), from `CvSActualRowConsumerV1`.
- The τ boxes and the Gram tail: `CvSGramTailV1` and `CvSTauFarL12V1`.

**Join**
- `57bc5add` fixed the hang with one `open` line (see §6).
- CI run 40116354368 replays it. Check the step
  "Replay actual 139-row to 141-moment window (7 axiom roots)".

**Still open**
- The **inputs to construct**: `s`, its measurability (`hsm`), `B` and `hsB`, `hs0`, and the
  correction terms `H`, `d`, `j`.
- The **premises to prove**:
  - `hcert`: the Krein inequality for **every real t**;
  - `cf`: the trace coefficients `ℝ → Fin 141 → ℂ`;
  - `hR`: integrability of `s · trialDist`;
  - `hT`: `∫ s · trialDist ≤ T`;
  - `hk`: `40 ≤ (2π)²·(6/5)·(m − T/(2π))`. This is the same as `T ≤ 2π(m − 0.8443)`.

## 2. Chosen route: a slack-only certificate

Take M = 3, empty `H` and `d`, and any `L > 6/5` (the `hHs` premise is then vacuous).

**The symbol and `hcert`**
- `ScertM 3 t ≥ h₊(t) − w₂⁺ − w₃⁺`. This is `CvSHplusBoundsV1.scertM_three_ge`, with
  `w₂⁺ + w₃⁺ ≈ 2.2486`.
- Choose a step function `s(t) = Σ_j s_j·1[|t| ∈ [a_j, a_{j+1})]` with
  `s_j ≥ m + w₂⁺ + w₃⁺ − h₊(a_j)`.
- Then `hcert` is pointwise, because `Wt > 0`.
- On the tail `|t| ≥ t*`, `s = 0`, and you need `h₊(t*) ≥ m + w₂⁺ + w₃⁺`. Use monotonicity:
  `CvSHplusBoundsV1.hplus_ge_of_sq`.
- With m = 3/2, `t* ≈ 267`, and the allowed trace is `T ≤ 4.1196`.

**Lower bounds for h₊**
- Use `CvSDiagL12V1.hplus_bounds`. It takes `r² ∈ [ql, qh]`, uses 40 series terms plus the
  `hplus_tel` tail, and its error is about 1e-8.
- **Do not write a new h₊ evaluator.** The first version of `CvSHplusBoundsV1` did exactly that
  and duplicated this lemma. It was slimmed down in the same commit as this note.

**Why the moment directions are needed**
- Without `γ`, `trialDist(0) ≈ 6/5`.
- At t = 0 the slack is largest (`s(0) ≈ 9.1`), so `T` would blow up.

**The trace coefficients `cf(t)`**

These are explicit. Write `K = [−70, 70]`, `e_k = trigAtom L k`, `u_σ = 1[0,L]·e^{σx}` for
`σ = ∓1/2` (that is `momentFunction 0` and `momentFunction 1`), and
`f_t = 1[0,L]·exp(i x t)`. Then:

1. `ĉ_k(t) = fourierCoeffOn (f_t) k` and `q_{σ,k} = fourierCoeffOn (u_σ) k`.
2. Form the Gram matrix `G_{σs} = L Σ_K q_{s,k} conj(q_{σ,k})` and the vector
   `a_σ(t) = L Σ_K ĉ_k conj(q_{σ,k})`. Solve `G γ = a` by Cramer's rule.
3. Set `v_k = ĉ_k − Σ_s γ_s q_{s,k}`. Then `Σ_K v_k conj(q_{σ,k}) = 0` for both σ. Since
   `L·conj(q_{σ,k}) = (e^{σL} − 1)/(σ + iω_k)`, this means `Σ_K v_k/(iω_k ± 1/2) = 0`.
4. Partial fractions turn this into the two second-difference conditions `Σ b_k = 0` and
   `Σ k b_k = 0`, with `b_k = v_k/((iω_k)² − 1/4)`.
5. Atom coefficients: `α_n = −4 Σ_{k=−70}^{n−1} (n − k) b_k` for `n ∈ [−69, 69]`. This gives
   `Σ_n α_n · momentAtom L n = Σ_K v_k e^{iω_k x}`, because momentAtom has the sinSq weights
   (−1/4, 1/2, −1/4). Both boundary values `α_{±70}` and `α_{±71}` vanish by the conditions in
   step 4.
6. `cf t = Fin.append α γ`. On `[0, L]` the error is then `(f_t − P_t) − Σ_s γ_s (u_s − p_s)`,
   where `P_t` and `p_s` are the `K`-truncations.

**Bounds**

These use Parseval (`CvSFourierIntervalV1.hasSum_coef`, `norm_sub_trigPoly`). Write
`A(t) = ∫|f_t − P_t|²` and `h = 2π/L`.

- The trial distance:
  `trialDist(t) ≤ (1+ε)A(t) + (1+1/ε)(|γ₀|²+|γ₁|²)(τ₀+τ₁)`, where `ε` may change from cell to
  cell.
- The atom tail:
  `A(t) ≤ (|e^{itL} − 1|²/L)·140/((70h)² − t²)` for `|t| < 70h ≈ 366.5`.
  - Proof: telescoping, with `1/(hk−t)² ≤ (1/h)(1/(h(k−1)−t) − 1/(hk−t))`.
  - Keep the factor `|e^{itL} − 1|² = 2 − 2cos(tL)`. Dropping it doubles the A part, and T then
    no longer fits.
- The moment tails: `τ_σ = ∫|u_σ − p_σ|² ≤ ((e^{σL}−1)²/L)·140/(70h)²`. That is 1.76e-4 and
  5.83e-4.
- `γ` stays close to `γ* = G_uu⁻¹ y(t)`, where:
  - `G_uu = [[1−e^{−L}, L], [L, e^L−1]]`, with det 0.18131;
  - `y_σ(t) = (e^{(it+σ)L} − 1)/(it+σ)`.

  The perturbation `G = G_uu − E` and `a = y − e` is controlled by Cauchy–Schwarz:
  `|E_{σs}|² ≤ τ_σ τ_s` and `|e_σ|² ≤ A τ_σ`.
- **Do not bound `|γ|` by an operator norm.** `γ*` has large cancellations. At t = 0,
  `|N₀(0)| = 0.12`, while a norm bound gives about 16.
- **Use the closed form instead.** Write `N_0 = (e^L−1)y_0 − L y_1`. Then
  `|num(t)|² = P(t) − 2Q(t)cos(tL) + 2R(t)sin(tL)`, with `num = N·(it−1/2)(it+1/2)`, P and Q even
  quadratics, and R odd and linear.
  - The coefficients are `α₁ = e^{L/2}−e^{−L/2}−Le^{L/2}`, `β₁ = (e^{L/2}−e^{−L/2}+Le^{L/2})/2`,
    `α₂ = e^L−1−L` and `β₂ = (e^L−1+L)/2`.
  - Then `P = (α₁²+α₂²)t² + β₁²+β₂²`, `Q = α₁α₂t² + β₁β₂` and `R = t(α₁β₂ − α₂β₁)`.
  - `N_1 = (1−e^{−L})y_1 − L y_0` has the same shape, with
    `α₁' = e^{L/2}−e^{−L/2}−Le^{−L/2}`, `β₁' = −(e^{L/2}−e^{−L/2}+Le^{−L/2})/2`,
    `α₂' = 1−e^{−L}−L` and `β₂' = −(1−e^{−L}+L)/2`.
- Enclose cos and sin over a cell with `CvSTauPrimeL12V1.sinPi_bounds`. Take `u = tL/π` on the
  cell; cos is sin shifted by 1/2.

**Numbers**

All at m = 3/2, allowed T = 4.1196. Scripts are under `scratchpad/k3`; they are not in the repo,
and the formulas above are enough to redo them.

| setting | T |
|---|---|
| ideal, with Minkowski | 1.79 |
| ideal, with `2a + 2b` | 2.61 |
| float mirror of the planned rigorous bound, 720 cells | 2.57 |
| same, 324 cells | 3.38 |

The 720-cell grid uses steps 0.02 on [0, 4], 0.1 on [4, 20], 0.5 on [20, 100] and 1 on
[100, 300].

Most of the cell loss comes from the sup of `sin²(tL/2)` over wide cells. The s-cells can be
coarse (geometric ratio about 1.03). The TD-cells must be fine.

## 3. Lean plan

Put each step in a new file. Do not edit the existing proofs.

1. **K3a**: closed forms and tails.
   - Compute `L ĉ_k(t)` with `coef_eq` and `integral_exp_mul_complex`. Do the same for
     `q_{σ,k}`, or take it from `CvSMomentV1.trigAtom_moment`.
   - Prove the finite tail bound `Σ_{F, F∩K=∅} 1/(t−hk)² ≤ 140/((70h)² − t²)`.
   - Pass it to Parseval with `hasSum_le_of_sum_le`. This gives the bounds on `A(t)` and `τ_σ`.
2. **K3b**: Cramer, the coefficient conditions, and the partial-fraction step to `Σb = 0` and
   `Σkb = 0`.
3. **K3c**: the second-difference inversion and the atom identity. Use
   `basisFun = Σ_k β_k(iw_k² − 1/4) e^{iw_k x}`, padded to all of K with zero weights, and
   `Finset.sum_comm`.
4. **K3d**: the pointwise `trialDist` bound, and continuity of `cf` in t. For continuity, `ĉ_k(t)`
   is a parametric interval integral, so `continuous_parametric_intervalIntegral_of_continuous'`
   applies. Continuity of `trialDist` then follows from
   `continuous_parametric_integral_of_continuous` on `Icc`, which gives `hR` measurability.
5. **K3e**: per-cell kernel checks (`decide +kernel`, no `native_decide`):
   - `|num|²` corner bounds over the `(cos, sin)` box;
   - the `sin²` sup;
   - `hplus_bounds` at the s-cells.

   Then integrate. `integral_comp_abs` gives `∫ F(|t|) = 2∫_{t>0} F`. Every term
   `1_j(|t|)·trialDist(t)` is at most `1_j(|t|)·TDup_j`, so no disjointness argument is needed.
6. **K3f**: assembly into `window_of_actual_rows_moment`.

## 4. Do not rebuild these

| Need | Existing lemma |
|---|---|
| h₊ bounds on r² intervals | `CvSDiagL12V1.hplus_bounds` (`hpLo`, `hpHi`, `logOk`) |
| h₊ monotone; half-line; `ScertM 3` lower bound | `CvSHplusBoundsV1` |
| sin(πu) on a rational interval | `CvSTauPrimeL12V1.sinPi_bounds` |
| π, e^{−3/5}, log 2, log 3, w₂, w₃ enclosures; rounding | `CvSTauL12V1.pi_bounds`, `e35_bounds`, `rdn_le`, `le_rup`; `CvSTauPrimeL12V1.log2_bounds`, `log3_bounds`, `w2_bounds`, `w3_bounds` |
| log of a rational | `CvSDiagL12V1.log_bounds` |
| Parseval, Pythagoras, pairing on [0, L] | `CvSFourierIntervalV1.hasSum_coef`, `norm_sub_trigPoly`, `integral_mul_conj_trigPoly`, `coef_eq` |
| ∫ trigAtom · e^{sx} | `CvSMomentV1.trigAtom_moment`, `trigPoly_moment`. The krein-ring job does not build an olean for it yet, so add an `-o` line before you import it. |
| trialDist, Cauchy–Schwarz | `CvSTraceV1.trialDist`, `cauchy_schwarz` |
| atoms and moment functions | `CvSMomentBasisV1.momentAtom`, `basisFun`; `CvSMomentTraceV1.momentFunction`, `augment` |
| rational interval arithmetic | `row_budget_bridge/CvSRationalIntervalV1`, `CvSIntervalMatrixProductV1`, `CvSIntervalDivideV1` |

## 5. Not the goal, and not a shortcut

- The `UNTRUSTED_KREIN_*` LP witnesses use H and d. They are numerical only.
- `HFIN_FEASIBILITY.md` §3–5 are validated numerics, not Lean.
- `CvSKreinScalarUniformV1` (`m ≥ 31/16`, `T ≤ 6`) is a sufficient scalar range. The slack-only
  route uses m = 3/2 and checks `hk` directly.

## 6. Traps

- **Hang.** The repo has `autoImplicit` on. Together with `set_option maxHeartbeats 0`, an unknown
  identifier in a signature becomes an auto-bound variable and elaboration does not terminate.
  Open every namespace you use. This was the cause of the 80-minute cancellation, fixed by
  `57bc5add`.
- **Pushing.**
  - Use the MCP owner `tarikskalic33`.
  - Fetch the branch head before every push, because several agents push here.
  - Never force-push.
  - Check the blob SHA after you push.
- **Audits.**
  - No `sorry`, `admit` or `axiom` in pushed files.
  - Every audited name must print `#print axioms` with only
    `propext`, `Classical.choice` and `Quot.sound`.
  - Add the module and its names to the krein-ring job in `rh-feshbach-schur-v1.yml`.
- **Search first.** Before you write any bound, grep `research/rh/feshbach_lean_v1` and
  `research/rh/checkpoints/*` for an existing lemma.

## 7. Scope

Even with everything above done, the result is Weil positivity for test functions with
`2r ≤ 6/5`. RH needs it for all widths. That step is open and is equivalent to RH itself. Not RH.
