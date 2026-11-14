# Trace modules of the window 3/2: port (2026-11-10)

Evidence kind: `lean_kernel` for the six modules listed under "Compiled", including the trace
certificate. This is the trace half of the input of the window theorem. The row certificate, `τ`
and the diagonal at `M = 4` are not ported, so no theorem about the window `3/2` exists yet.
RH status: OPEN.

## What this is

The trace side of `window_of_certificate_gram_moment` at `LT = 3/2`, `M = 4`, 299 atoms,
`m = 33/20`, ported from the 11/8 modules. Parameters come from
`../20261110_window_l32_feasibility_v1/`.

## Files

- `CvSExpL32V1.lean` (new): `e34_bounds`, a rational enclosure of `e^{−3/4}` from
  `Real.exp_bound`, as `CvSTauL118V1.e1116_bounds`.
- `CvSTraceM4SlackV1.lean` (new): `ppw_three : ppw 3 = Real.log 2`, `w4Hi`, `w4_bounds` and
  `scertM_four_ge : hplus t − w2Hi − w3Hi − w4Hi ≤ ScertM 4 t`. This is
  `CvSHplusBoundsV1.scertM_three_ge` with the term of `n = 4`. Another agent has announced a
  module of the same name with `ppw_three`; if it lands, keep one of the two.
- `port_trace_l32.py`: derives three modules from the 11/8 sources by literal substitution
  (`11/8 → 3/2`, `11/16 → 3/4`, `8/11 → 2/3`, `121/64 → 9/4`, `19/8 → 5/2`, `3/8 → 1/2`,
  `70 → 150`, `139 → 299`, `141 → 301`, `69 → 149`, `ScertM 3 → ScertM 4`, the slack with `w4Hi`,
  and `gap_of_T` with `κ = 66`, `T ≤ 3`):
  - `CvSTraceDistK150V1.lean` from `CvSTraceDistV1.lean` (trace family of 299 atoms),
  - `CvSTraceCellL32V1.lean` from `CvSTraceCellL118V1.lean`,
  - `CvSTraceIntegralL32V1.lean` from `CvSTraceIntegralL118V1.lean`.
- `make_gen_cert32.py`: derives `gen_cert32.py` from `../20261031_window_l118/gen_cert118.py`
  (3123 cells on `|t| < 621`, 73 chunks, `Tq = 3`, `κ = 66`). `gen_cert32.py` with
  `cert32_totals.json` writes `CvSTraceCertL32V1.lean`.
- `cert32_totals.json`: the chunk totals printed by the `--eval` file (times `10^5`, rounded up).
- `DERIVED_SHA256.txt`: inputs (git blobs at 21fb824) and SHA-256 of every derived file.
- `TRACE_PORT.log`: what was run and what came back.

The derived Lean files are not committed, as for the generated row certificates of the earlier
windows. Regenerate them with the scripts and compare with `DERIVED_SHA256.txt`.

## Compiled

Against the lab DAG built from source locally (`plan.py CvSTraceIntegralL118V1 CvSTauFarL118V1`,
`build.py`: 131 of 131 modules pass), with the Li provider at the commit pinned by the workflows:

| module | result |
|---|---|
| `CvSExpL32V1` | exit 0, no `sorry` |
| `CvSTraceM4SlackV1` | exit 0, no `sorry` |
| `CvSTraceDistK150V1` | exit 0, no `sorry` |
| `CvSTraceCellL32V1` | exit 0, no `sorry` |
| `CvSTraceIntegralL32V1` | exit 0, no `sorry` |
| `CvSTraceCertL32V1` | exit 0, no `sorry`, 2494 s, 73 chunks by `decide +kernel` |

`#print axioms` of `e34_bounds`, `ppw_three`, `scertM_four_ge`, `trialDist_le`, `cell_sound`,
`premises_of_cells`, `gap_of_T`, `all_ok`, `total_le` and `trace_premises_L32`:
`[propext, Classical.choice, Quot.sound]`. The derived modules compiled without any manual edit.

Limits of this run: default trust level and plain `lean`, as the lab planner does for most
modules; no `--trust=0` run, no `leanchecker` replay and no second machine yet. The certificate
needed more than 10 GB of memory.

## Statements obtained

- `cell_sound`: for `|t|` in a checked cell, `trialDist 0 (3/2) V (cfC h32) t ≤ c.TD k` and
  `m − ScertM 4 t ≤ c.s`, for every trace family `V : Fin 301 → ℝ → ℂ`.
- `gap_of_T`: `66 ≤ (2π)² · (3/2) · (33/20 − T/(2π))` for `T ≤ 3`.
- `trace_premises_L32`: for every trace family `V` of the 299 atoms and the two exponentials,
  with `cells` the 3123 checked cells and `Tq = 3`:

      Measurable (sFun cells) ∧ (∀ t, |sFun cells t| ≤ sMax cells) ∧ (∀ t, 0 ≤ sFun cells t) ∧
      (∀ t, 0 ≤ Wt t * (ScertM 4 t − 33/20) + Wt t * sFun cells t) ∧
      Integrable (fun t => sFun cells t * trialDist 0 (3/2) V (cfC h32) t) ∧
      (∫ t, sFun cells t * trialDist 0 (3/2) V (cfC h32) t) ≤ Tq ∧
      66 ≤ (2π)² · (3/2) · (33/20 − Tq/(2π))

  These are the premises `hsm`, `hsB`, `hs0`, `hcert` (no `H`, no `d`), `hR`, `hT` and `hk` of
  `window_of_certificate_gram_moment` at `M = 4`, `LT = 3/2`, `m = 33/20`.

## Certificate cells

Evaluator first (`gen_cert32.py OUT.lean --eval`): every check `true`, chunk totals summing to
`296053 / 10^5`, so `T = 2.96053 ≤ 3`. By segment: `0.53717 0.31175 0.61100 1.50061`; the Python
mirror `trace_cells_k.py` had given `0.5371 0.3117 0.6109 1.5004`. Then the kernel: the 73 chunk
theorems `c{i}_ok : ch{i}.all (cellOk m0) = true ∧ total K0 ch{i} ≤ tot_i / 100000`, `K0_ok`,
`chain_ok`, `tail_log` and `tail_ok`, all by `decide +kernel`.

## Reproduce

    # provider: nicholasbulka/li-criterion-rh-equivalence-lean at 35df682f, with the three
    # replacements of the workflows in Hadamard/General/Factorization.lean
    python3 research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source/plan.py \
        CvSTraceIntegralL118V1 CvSTauFarL118V1
    python3 research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source/build.py PROVIDER_LIB 3
    python3 port_trace_l32.py REPO OUT
    python3 make_gen_cert32.py ../20261031_window_l118/gen_cert118.py > gen_cert32.py
    python3 gen_cert32.py OUT/CvSTraceCertL32V1.lean cert32_totals.json
    # compile, in this order, with LEAN_PATH = OUT/lib : .lake/ringout : PROVIDER_LIB : toolchain : packages
    #   CvSExpL32V1, CvSTraceM4SlackV1, CvSTraceDistK150V1, CvSTraceCellL32V1,
    #   CvSTraceIntegralL32V1, CvSTraceCertL32V1

## Next

1. Independent replay of the six modules (`--trust=0`, `leanchecker`, a second machine or CI).
2. Port `τ` for `k ≤ NP` at `M = 4`, the far bound `|τ| ≤ 14`, the diagonal and the row
   certificate (`NP = 900, κ = 60` or `NP = 700, κ = 66`; both are below `κ = 66` of `hk`).
3. Then `window_L32` from `window_of_certificate_gram_moment 4 2 (3/2) (33/20)`.
