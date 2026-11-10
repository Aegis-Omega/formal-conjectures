# RH lab handoff addendum, 2026-11-10

Read `HANDOFF.md` first. This file records what was verified on 2026-11-10 and what to do next.
Branch `fix/rh-live-evidence-provenance-20261024` (PR #92). RH status: OPEN.

## 1. Verified on 2026-11-10

- Commit 22c6925, eleven-window closure: all 186 modules compiled from source at `--trust=0`,
  no `sorry`, three standard axioms, `leanchecker` exit 0. Receipt:
  `research/rh/checkpoints/20261110_independent_eleven_analytic_closure_v1/INDEPENDENT_REPLAY_RECEIPT_20261110.md`.
- PR #97: its red checks come from the fail-closed target gate (`TARGET_SOURCE_INVALID`, because
  `FormalConjectures/Millennium/RiemannHypothesis.lean` has `sorry` at 61:8 and 83:8). The job log
  has no Lean compile error.
- The approximation hypotheses are restatements of the sign claim (section 2). Files:
  `research/rh/checkpoints/20261110_hrepresentation_equivalence_v1/`.

## 2. Frontier map

The lab has the full zero-side quadratic of a packet `g`:

    Z g = (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

Read from source on 2026-11-10 (not replayed in this session):

- `window_L118` (`research/rh/checkpoints/20261031_window_l118/CvSWindowL118V1.lean`):
  `0 ≤ Z g` for every moment-zero `g` with `HalfWidthAt g r a` and `2 * r ≤ 11 / 8`.
- `rh_iff_windows_above_eleven_sixteenths`
  (`research/rh/checkpoints/20261031_window_l118/RHWindowL118ExhaustionV1.lean`):
  `RiemannHypothesis ↔ ∀ L, 11 / 16 < L → WindowArithmeticNonpositiveV1 L`.

So the open statement is the window sign for every half-width above 11/16. Nothing else.

The mechanism that works is `window_of_certificate_gram_moment`
(`research/rh/checkpoints/20261020_row_budget_bridge/CvSActualMomentWindowJoinV1.lean`). It takes a
prime cutoff `M`, a window `LT` with `LT < Real.log (M + 1)`, a trace certificate, atoms, a row
budget `Brow` and the low-block inequality `hlow`, and concludes `0 ≤ Z g` for every moment-zero
`g` with `2 * r ≤ LT`. There the finite certificate is bound to `g` through the window, and it
covers the whole infinite-dimensional window space. `window_L118` is the instance `M = 3`,
`LT = 11 / 8`, 139 atoms.

Three other hypotheses are offered as routes to the universal sign:

- `hrepresentation` (`AEGIS_RH_CvS_UniversalSignKernelV1.lean`),
- `UniversalActualCvSCofinalApproximation`,
- `UniversalActualCvSLowBlockApproximation` (both in `AEGIS_RH_CvS_Cofinal_ActualWeil_JoinV1.lean`).

Each says: there are cutoffs `M j` and vectors `v j : Fin 139 → ℂ` with
`projectedQ (M j) (v j) → Z g` (the last two also ask `M j → ∞`). None of them relates `v j` to `g`.
The form is nonnegative and, by the strict certificate margin, positive on every nonzero vector at
every cutoff `M ≥ 3`. So for any `t ≥ 0` and any cutoff there is a vector on which the form equals
`t`. Each hypothesis is therefore equivalent to `∀ g, 0 ≤ Z g`. The certificate does no work inside
them. Their docstrings call them "strictly stronger"; they are not. Do not spend effort on
producers for them.

Kernel-checked (Mathlib only): `representation_iff_nonneg` and `cofinal_representation_iff_nonneg`
in the checkpoint directory of section 1. The instantiation to `projectedQ` is read from source and
not compiled locally (section 3 says why).

`hresidual` (`AEGISOverlay/RHPrimeFreeRecompositionJoinV1.lean`) is different: it binds the pieces
to `g` (`g = packetSum 1 gs`) and implies RH. Whether it can hold is not assessed. One unverified
count: with pieces of width 1/128, a piece inside a support longer than about 2.2 has roughly 197
log-free neighbours, a fixed cost near 2.03 against the row budget 57430/65536 ≈ 0.876, so the
remaining residuals of that row must sum below about −1.16. Check this against the definition of
`WidthOneOneTwentyEightAt` and on one explicit `g` before any formal work.

## 3. Local replay recipe

- `export PATH="$HOME/.elan/bin:$PATH"`; inside the repo, `elan which lean` gives the toolchain.
  Put the toolchain `bin` first on `PATH` (`leanchecker` spawns `lean`).
- `LEAN_PATH` = output lib, then `<toolchain>/lib/lean`, then every
  `.lake/packages/*/.lake/build/lib/lean`. Mathlib oleans come from `lake exe cache get`.
- One module: `lean --trust=0 --root=<root> -o <lib>/<Module>.olean <file>`; the module name is
  the path relative to `<root>`.
- Top-level modules live in several directories (repo root, `research/rh/feshbach_lean_v1`,
  `research/rh/krein_ring_v1`, `AegisRH/PR606`, checkpoint directories). Some exist only as
  `research/rh/aegis_source_4f93fff/lean/<Module>.lean.src`.
- The CvS chain imports `Lc.*` and `Hadamard.*`. Those come from the `.li` checkout made inside
  `.github/workflows/aegis-pr606-fork-replay-v1.yml`. Without it the chain does not compile locally.
- After the container has been idle, the first `import Mathlib` can take ten minutes.

## 4. Access

- GitHub tools: owner `tarikskalic33`, repo `formal-conjectures`. The `gh` CLI does not work for
  this repository. Push with a multi-file commit to the PR branch, `[skip ci]` for research data,
  then compare blob SHAs with `git hash-object`.
- Job logs: request the log URL, download it, search it locally.

## 5. Next steps, in order

1. Next window. Instantiate `window_of_certificate_gram_moment` with `M = 4` and a window `LT`
   in `(11/8, Real.log 5)`. It needs a new trace certificate, atom set, far-row bound and row
   budget, as in the `20261031_window_l118` checkpoint. Expect a much smaller margin than at 11/8;
   check first whether the 64-bit scale `certQ` still suffices. A proved window moves the frontier
   of `rh_iff_windows_above_eleven_sixteenths`; it is a theorem about one window, not RH.
2. RH needs the window sign for every width. No finite list of windows gives it. Any claimed
   uniform argument must be stated as a theorem over all `LT`, with no free sequence of vectors.
3. Correct the docstrings of the three approximation hypotheses, or retire them.
4. Compile the instantiation of the two equivalences to `projectedQ` where `.li` is available.
5. Decide `hresidual`: definition check, then one explicit numerical test.
6. Standing constraints of `HANDOFF.md` section 6 are unchanged. RH is never declared proved.
