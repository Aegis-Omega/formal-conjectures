# RH lab: handoff and operating protocol

Save file for the next session. Read it first; update §5 at the end of every session.
Historical handoff updated for source activity through 2026-11-05. Live HEAD must be read from PR #92; this file is not an immutable-current-head receipt.

## 1. Where things are

* PR #92 (draft, never merge) on Aegis-Omega/formal-conjectures (MCP owner `tarikskalic33`,
  repo `formal-conjectures`), branch `fix/rh-live-evidence-provenance-20261024`.
* `research/rh/aegis_math/`: `AegisMathCoreV1.lean` (aliases; compiled and axiom-audited in
  `rh-cvs-window-l65-source.yml`), `CATALOG.json` (22 entries, one evidence kind each),
  `INDEX.tsv` (203 kernel-checked theorems), `catalog.py` (verifies both; run from the repo root).
* `research/rh/checkpoints/20261101_lambda_lab_s1/`: the λ_a lab (`qwhp.py`, `hpscan.py`, `s2.py`,
  `certify.py`, `CERTIFIED.txt`, README with all tables).
* Windows: `research/rh/checkpoints/20261031_window_l118/`; build DAG in
  `research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source/` (`plan.py`, `build.py`, `audit.py`).
* Historical all-green checkpoint: `777d7d88` (windows run 41362109721). Later source commits exist and have their own CI runs; historical GREEN must never be projected onto a newer SHA.
* Latest source head checked before this handoff update: `e017d2aa916ecfd0db112a3a40bdc6200edb881c` (PR #92). The current live HEAD may differ after any subsequent commit. This head adds the conditional `rh_iff_remaining_windows_actual_sharp_signed_budget` to the existing stronger `RHWindowL118ActualFineGramJoinV1.lean` without asserting universal RH. Source blob at that head: `240fc3927bfa0a7fad540427843b3454d39add02`; source-graph run `42048897477` SUCCESS, moment-killer run `42048897294` SUCCESS; CvS full source run `42048897448` was PENDING at inspection. No exact-head kernel PASS for the new theorem has been observed.

## 2. Mathematics

* Kernel-checked: `AegisMath.Windows.rh_iff_windows_above_eleven_sixteenths`
  (RH ⇔ ∀ L > 11/16, `WindowArithmeticNonpositiveV1 L`); every window L ≤ 11/16 is proved.
  Obstructions: no common positive width; the uniform fine mixed budget is unsatisfiable; an extra
  Mellin zero blocks translate approximation; von Mangoldt weights do not give operator positivity.
  Moment-killer: every two-moment-zero packet is (1/4 − ∂²)ψ.
* Certified (arb): λ0_a ≤ 7.7e-10, 1.9e-18, 5.0e-23, 4.2e-26 at a = 3/4, 1, 5/4, 3/2.
* Numerical: λ_a ≈ exp(−4π e^{2a}); the lowest eigenvalue is simple and even for a ≤ 11/16.
* Consequence: a family budget constant must decay like λ0_a in the spread (≤ 8.45e-26 at a = 3/2),
  and each further window costs about 4π e^{2a}/ln 10 digits. The window/budget route needs a new
  idea; more computation alone does not close it.

## 3. Routes with a verifier (ranked)

1. Certified simple-even (the CCM hypothesis, arXiv 2511.22755): rigorous lower bounds for the
   second eigenvalue (Temple or Lehmann–Goerisch) on the even and odd blocks in arb, for a up to
   11/16 and beyond. Verifier: arb. Bounded.
2. Lean proof of the localization criterion (Yoshida; Suzuki arXiv 2606.09096, Thm 1.3):
   RH ⇔ λ_a ≥ 0 for all a, as a blueprint of small lemmas joined to `Criterion.final_sign_iff_rh`.
   Verifier: Lean kernel. Large; split into lemmas.
3. Replay external claims before cataloging them: the Codex sinc transfer through
   `CvSAtomInversionV1.atom_sum`, its Lévy-decomposition domain remark, the inputs of the historical
   Coq globalization chain, the paid resonance at log 5. Until replayed they are `external_claim`.

None of these is known to close RH. Each one ends in checked artifacts or recorded dead ends.

## 4. Operating protocol

Fused from Anthropic's practice for long-running agents (progress file, one item per session, git
checkpoints, verify before claiming, subagents only for isolated work), OpenAI's ExecPlans and
AGENTS.md (a living plan in the repo) and the Erdős lesson (search the literature before claiming
novelty), DeepMind's AlphaProof and AlphaEvolve (search only against an automatic verifier), and Lean
blueprints (Buzzard, Tao; the Equational Theories Project: many small verified tasks).

1. One cycle = one queue item, one verifier (Lean kernel, arb, or a reproducible script), one token
   budget. It ends with a kernel-checked file, a certified number, or a dead end recorded in
   `CATALOG.json`. No report without an artifact.
2. Literature check (alphaXiv, arXiv) before calling anything new.
3. Evidence kinds are never promoted (the catalog rule).
4. Agents only when the user asks, one per independent verifiable item. Stop after two cycles
   without an artifact.
5. The weekly limit is the binding constraint: a new session per item, short replies, no polling,
   no scheduled check-ins unless asked.

## 5. Queue

* Q0: ensure `.github/workflows/rh-cvs-window-l65-source.yml` compiles the existing `RHWindowL118ActualFineGramJoinV1` root and `audit.py` REQUIRES its `rh_iff_remaining_windows_actual_sharp_signed_budget` `#print axioms` result. The workflow must compare the checked-out Git HEAD with the triggering PR head SHA and preserve the actual source hashes in the receipt. A queued, pending or running workflow is not a source-level PASS.
* Q1: inspect fresh exact-head CI jobs and the first failing compile log if any. Fix only the actual failed import/type/check while retaining the old passing checkpoints and without weakening any proposition or audit.
* Q2: search actual existing source/archives for a producer of the remaining-window signed Gram certificate (or an independent sufficient RH route) before adding any theorem. The stronger existing L118 full-signed-Gram join must not be duplicated.
* Q3: when Codex pushes, inspect only its diff and classify candidate-only claims until source-bound replay. The spectral simple-even lower-bound experiment at a=0.3 remains a separate bounded research track.
* Blocked on the user: Pages; stale red branches (tag, then delete); the Claude GitHub App;
  the leftover branch `ops/archive-red-branches-20261101`; approval of the #95 bot run.

* Q4 (2026-11-05 Gate-II exact check): source `research/rh/checkpoints/20261103_signed_schur_reuse/exact_signed_counterexample.py` at commit `0390796a74e1814b4e34306777ad1ce13cbedba6`, blob `5fdecf5e1bc3b6d9093c5be75183cf67a8a819d7`, was executed locally with Python/Fraction and had matching Git blob. Four alpha cases PASS for whole-matrix Schur congruence, 3 source-basis changes per case, positive lower reserve, and a deliberate double-debit negative control. Scope: standalone rational signed Gram, NOT actual Weil operator or a Lean kernel proof. No additional GitHub Actions run was spawned ([skip ci]).
* Q5 (external review, not promoted): Desogus `The Three Gates` arXiv:2609.20367v3/V4 claims the physical odd Weil operator Gate-II induction. rStation post 21 (2026-10-18) presents an un-replayed certified theta trial at k=7, conditional on identifying its true physical collar ground. Independently checked only the elementary physical polar versus odd-constant overlap (L2 distance ~0.0207382), the published e_w versus constant overlap (~0.0192702), and the conditional scalar inequality 2.30*(1.90-2.37/4)^2=3.931979375>2.16. These are NUMERICAL/EXTERNAL_CLAIM, not a verified counterexample. The next high-value proof is the exact physical identification of the collar source ground and independent replay of the theta energy certificate; do not import an external RH claim as an axiom.

* Q6 (2026-11-05 exhaustive PR #1..#95 FILE DIFF inventory): GitHub /pulls?state=all&per_page=100 returned 95 PRs numbered exactly 1 through 95 (75 closed, 20 open; 12 merged); the file-level patch sets of all 95 PRs were reviewed, including closed drafts, not only titles. This is a *PR-diff inventory*, NOT a proof-term or all-historical-Git-object census. Source candidates, exact SHA and independently checked workflow results:
  * PR #7 `e9c3bff76e3babe21363fe9b5062dadd55b373b3` `AegisRH/fixed_window_true_matrix_arb.py`: REAL finite Weil matrix interval certificates at R=pi and R=2pi; GitHub Actions `35850758202` SUCCESS, job `107147603801`. Receipt `all_shifted_certificates_pass=true`, `all_unshifted_interval_ldlt_pass=false`; finite N only and `all_N_certified=false`, `rh_proven=false`. `FormalConjecturesUtil/FixedWindowLimitBridge.lean` proves conditional cofinal limits and pi-window quantifier transport, NOT all-N positivity.
  * PR #12 `069400c0593d1577a420beb55f68b231713f2961` `RHSmallWindowProducerV1.windowArithmeticNonpositive_one_over_64_v1`: source-actual Weil sign for L=1/64 (and L=1/128); dedicated run `37718269813`, job `113119727068`, SUCCESS with standard-axiom `#print axioms`.
  * PR #54 `df9a1e51e99ea953c100c932e37ea3e4894ebb21` `RHKreinM8FiniteWindowV1.correctionSymbol_eighth_le_finiteWindow`: interval derivative majorant, NOT Weil-form sign; run `37677757783`, job `112985538244`, SUCCESS.
  * PR #78 `bc6db2d931a5df23889393abe825f6bbc9b0d534`: archived L105 conditional global-window criterion `L<21/40`; current-head consolidated run `38122837704` FAILED. Do NOT promote this PR-head to exact-head kernel PASS from source-only statements or earlier receipts; recover stronger archived source cert and the first actual failure if needed.
  * PR #86 `96c361c18b9f5a4c20d04e31cf7a04b04029cc8e`: actual finite Weil Gram decomposition, `RHFiniteActualGramJoinV1`, cofinal replay `38602296215` SUCCESS. The theorem retains all actual off-diagonal Gram entries; no universal sign.
  * PR #88 `aacdd511877e3e725dbee05b1167ee38b681ab31`: fine partition, actual sign/Schur and 183 historical PR721 source intake; exact-head cofinal run `38799949777` SUCCESS, 311 sources; `UNIVERSAL_CLOSURE_NOT_ACHIEVED`.
  * PR #92 active branch (read live head before any further mutation): `RHWindowL118ExhaustionV1.window_le_eleven_sixteenths` states `WindowArithmeticNonpositiveV1 L` for ALL `L<=11/16`, from CvS L=11/8; `RHWindowL118ActualFineGramJoinV1` consumes it to certify the exact full signed Gram on that window. Earlier cofinal run `42051019025` at `1dc607c64c35075c69c39ea0e179c1b58153115e` succeeded but official RH root `RiemannHypothesis.riemannHypothesis` retains `sorryAx`. Do NOT project previous success to a newer `[skip ci]` SHA. Current L118 standalone source compilation/audit remains unverified until the corresponding CvS run completes successfully.
  * Scope/order: local physical Weil sign for all packets with L<=11/16 is stronger than earlier L<=21/40 and L<=1/64, but PR #7's finite-N certificates at R=pi,2pi are a DIFFERENT numerical statement, not proof of infinite-dimensional sign there. PR #54's M8 bound is also different. No source-bound unconditional producer for `∀ L>11/16`, `GlobalPrimeArchDomination`, or `UniversalActualCvSCofinalApproximation` was identified by this PR-diff inventory. It must not be inferred nonexistent elsewhere or replaced by a restated RH equivalence.
  * Next mathematical execution: independently replay the PR #7 unshifted versus shifted finite certificates and check whether its explicit truncation error plus certified eigenvalue gap yields a valid cofinal same-packet convergence theorem. If not, turn to source-exact cross-window signed Gram/Mellin/Schur producers, preserving the existing L118 theorem and no-go obstructions. Require Lean kernel & `#print axioms` for any claimed universal transfer.

## 6. Standing constraints

Reply in BHS, briefly. No sorry, axioms, fake modules or duplicates; change existing proofs only
minimally. Never touch `gate.py`, `dna.py`, `router.py`, `.env` files, secrets, `main`, #698 or the
official `FormalConjectures/Millennium/RiemannHypothesis.lean`. No merge, no force-push, no model ids
in commits; use the session's own commit trailers. Check the branch head before every push, push
through MCP, verify blobs, use `[skip ci]` for data. Do not retry Pages enabling or branch deletion
through GITHUB_TOKEN. Never declare RH proved.

## 7. Claude settings (inspected 2026-11-02; changes are the user's to apply)

AEGIS-OMEGA `.claude/settings.json` on `main`:

* `"model": "claude-opus-4-8"` is pinned for the project. Proposal: drop the pin; use Opus for
  mathematics and Sonnet for CI and housekeeping (`/model`).
* `scripts/claude-authority-guard.py` denies every shell `git push`, so each push re-emits whole
  files through MCP (a 38 KB push costs 38 KB of output). Proposal: allow `git push origin <branch>`
  when the branch is explicit and not `main`/`master`, with no `-f`, `--force*`, `--mirror`, `--all`,
  `--delete`, `:` or `+` refspecs; keep everything else denied.
* `.claude/settings.json` and `.claude/hooks/**` are deny-listed for Claude: keep that; the user
  edits them.
* Ultracode (a session option) turns every substantive task into a multi-agent workflow: keep it off
  and keep the workflow size small.
* The hooks add one short context line per prompt: fine.

New conditions (limits, plans, models, policies) are recorded here first.
