# RH lab handoff addendum, 2026-11-11

Read `HANDOFF.md`, then `HANDOFF_ADDENDUM_20261110.md`, then this. It replaces item 1 of section 5
and the last two bullets of section 3 of the 2026-11-10 addendum. RH status: OPEN.

## 1. What changed

- The trace half of the window `3/2` is kernel-checked: `trace_premises_L32`
  (`research/rh/checkpoints/20261110_window_l32_trace_port_v1/`). It gives the premises `hsm`,
  `hsB`, `hs0`, `hcert`, `hR`, `hT` and `hk` of `window_of_certificate_gram_moment` at `M = 4`,
  `LT = 3/2`, `m = 33/20`, with `T = 3` and `κ = 66`, for every trace family of 299 atoms and the
  two exponentials. Six modules, exit 0, no `sorry`, three standard axioms. Default trust level;
  a `--trust=0` rerun was started on 2026-11-11 and its result is not recorded here.
- No theorem about the window `3/2` exists. The row certificate, `τ` and the diagonal at `M = 4`
  are not ported.
- Another agent announced a source package `AEGIS_RH_L32_K150_TAU14_ALLN_SOURCE_V3_2026-11-10`
  with `CvSTraceM4SlackV1`, `CvSTauFarL32V1` and `CvSTauSmallL32V1`. It is not on this branch. A
  module named `CvSTraceM4SlackV1` is committed in the trace port directory; keep one of the two.

## 2. The lab DAG now compiles locally, without CI

- The Li provider is public: `nicholasbulka/li-criterion-rh-equivalence-lean` at
  `35df682f3b709ffe5fbcfdd452dfa964bd622b87`. Apply the three replacements of the workflows to
  `Hadamard/General/Factorization.lean` and compile the closure of the four workflow targets with
  plain `lean -o` and `-DmaxSynthPendingDepth=3 -DautoImplicit=false` against the Mathlib oleans of
  this repository: 28 modules, about 200 s. No `lake update` is needed.
- Then, from the repo root: `plan.py <roots>` and `build.py PROVIDER_LIB 3`
  (`research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source/`). With the roots
  `CvSTraceIntegralL118V1 CvSTauFarL118V1` the plan has 131 modules and all pass.
- New modules compile against `.lake/ringout`, the provider lib, the toolchain and the package
  libs. The trace certificate at `3/2` needs more than 10 GB of memory and about 42 minutes.
- Sliced copies of lab modules (selected declarations under the original module name) are a smoke
  test only. They cannot be linked with the real DAG and are not evidence for the port.

## 3. Remaining steps of the 3/2 port, in order

1. Independent replay of the six trace modules (`--trust=0`, `leanchecker`, CI).
2. `τ_k` at `M = 4` for `k ≤ NP` with boxes near `5e-13` for `k ≤ 150` and `5e-11` above, the far
   bound `|τ| ≤ 14`, and the diagonal for `n ≤ 150`. The 11/8 modules are `CvSTauL118V1`,
   `CvSTauL118DataV1`, `CvSTauPrimeL118V1`, `CvSTauR1SourceL118V1`, `CvSTauR1PrimeL118V1`,
   `CvSTauFarL118V1` and `CvSDiagL118V1`. The boxes at 11/8 had radius near `1e-8`; whether the
   kernel check reaches `5e-13` with the present number of series terms is not known.
3. The row certificate, 299 by 299, `NP = 900, κ = 60` or `NP = 700, κ = 66`, LDL scale `2^80` or
   more. Both values of `κ` are covered by `hk` with `κ = 66`.
4. `window_L32` from `window_of_certificate_gram_moment 4 2 (3/2) (33/20)`, then the exhaustion
   theorem with the frontier `3/4`.
5. Items 2 to 7 of section 5 of the 2026-11-10 addendum are unchanged.
