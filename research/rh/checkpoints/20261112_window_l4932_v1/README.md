# The window 2r ≤ 49/32 and the exhaustion step with frontier 49/64

Date: 2026-11-12. Status: **kernel-checked locally**, default trust and `--trust=0` (70 modules
each). Not run in CI.
**RH remains OPEN.** The windows `L > 49/64` are not proved.

## Result

```lean
theorem AEGIS.CvSWindowL4932V1.window_L4932 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 49 / 32) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

theorem AEGIS.RHWindowL4932ExhaustionV1.window_le_forty_nine_sixty_fourths {L : ℝ} (hL : L ≤ 49 / 64) :
    WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL4932ExhaustionV1.final_sign_iff_windows_above_forty_nine_sixty_fourths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 49 / 64 < L → WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL4932ExhaustionV1.rh_iff_windows_above_forty_nine_sixty_fourths :
    RiemannHypothesis ↔ ∀ L : ℝ, 49 / 64 < L → WindowArithmeticNonpositiveV1 L
```

`RiemannHypothesis` is Mathlib's, through `V13Scratch.final_sign_iff_rh_v13`. The last theorem is a
reduction, not RH: it moves the open part from the windows `L > 3/4`
(`../20261112_window_l32_v1/`, `rh_iff_windows_above_three_quarters`) to the windows `L > 49/64`.
The parameters come from `../20261112_window_beyond_l32_feasibility_v1/` (49/32 passes the mirrors,
8/5 fails).

## How

`window_L4932` is `CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment` with `M = 4`,
`L = 2`, `LT = 49/32`, `m = 33/20`, no correction terms, `ε = 7/5`, and these inputs:

| premise | source (this checkpoint) |
|---|---|
| `49/32 < log 5` | `log_five_gt` (`e^49 < 5^32` from `Real.exp_one_lt_d9`) |
| trace family of the 311 atoms and the two exponentials | `augment_family`, `augment_cont` |
| slack, trace bound `T = 3`, `66 ≤ (2π)²·(49/32)·(33/20 − T/(2π))` | `CvSTraceCertL4932V1.trace_premises_L4932` (`K = 156`) |
| `τ_k` boxes for `1 ≤ k ≤ 2000`, every `M ≥ 4` | `CvSTauL4932AllV1.tau_mem_all` (40 data modules, kernel `decide`) |
| `cvsEntry M (49/32) n n` boxes, `n ≤ 156` | `CvSDiagL4932V1` (`K = 300` series terms) |
| atoms `ctr i = i − 155`, `\|ctr i\| ≤ 155 < 157` | `CvSRelRowFormL4932V1.ctr` |
| `\|τ_n\| ≤ 15` for `\|n\| ≥ 2001` | `CvSTauFarL4932V1.tau_abs_le_far` |
| rows `NP = 2000`, `Brow 4 ≤ 66 Q_CvS 4`, `0 ≤ Q_CvS 4` | `CvSRelRowHBL4932V1.hB`, `Q_nonneg` |

The relative row certificate: scaled `λ_min 2.14177·10⁻⁹` (`Pscale 544 → 520` by `rescale_pkl.py`),
LDL at `q = 80`: `eps = 1294618032617024`, `eta = 121258873061257 < eps`.
`RHWindowL4932ExhaustionV1` is `RHWindowL32ExhaustionV1` with `window_L4932` and `49/64`.

## Kernel memory (statements unchanged)

At `KK = 156`, `NP = 2000` five kernel checks of the straight port ran out of memory (15 GB machine);
each was split without changing a statement used downstream:

1. `boxes_ok`, `S_ok*`, `T_ok*`, `V_ok*`: chunks of 8–51 indices (`chunk_data4932.py`, `all_of_chunks`).
2. `CvSRelRowDataAL4932V1` split into a chain A0 → A1 → A in one namespace (`split_dataA4932.py`).
3. `Sraw 1/2`, `Traw 1/2` walked `tLit` linearly: `tget` reads `tLit` in rows of 50, kernel-checked
   against `tLit`; `Sraw_eq`/`Traw_eq` transfer it (`fast_tq4932.py`).
4. `h_ok` (2157 steps) in 44 chunks (`chunk_h4932.py`); in `Check` the columns read `hLit` through
   the same row lookup `hget`, with `colF_eq`, `cols313F_eq` (`fast_hq4932.py`; one line in `Psd`).
5. `maxima_ok` (range 2001) in the 40 chunks `chunks2001` (`chunk_box4932.py`).

Two port fixes: the Tail indentation (`250 → 2000` moves a tactic column; rule in
`port_rules4932.json`) and `ε := 7/5` in the window (`make_window4932.py`).

## Files

* `regen.sh REPO OUT` regenerates the 69 generated modules, the 8 derived scripts and the diagonal
  data and checks them against `generated.sha256` (78 files; checked 2026-11-12, 48 s, all match).
  The modules (1.94 MB) are not committed. `CvSExpL4932V1.lean` is hand-written.
* Scripts: `make_gen_cert4932.py`, `make_diag_ports4932.py`, `make_tau_gen4932.py` (derive the
  generators from the 11/8 and 3/2 ones), `port_trace_l4932.py`, `port_tau_l4932.py`,
  `make_node4932.py`, `make_taufast4932.py`, `make_taufar4932.py`, `make_window4932.py`,
  `cert4932_totals.json`; `rr/`: `make_emit_rr4932.py`, `gen_rr4932.py`, `boxes4932.py`, the five
  memory scripts above, `port_mod4932.py` + `port_rules4932.json`, `make_rr4932_check.py`.
* `build_order.txt`: the 70 modules in dependency order.

The row-certificate pickles are untrusted inputs and are not committed (the kernel recomputes every
table and the LDL check). `boxes4932.py` reads the τ and diagonal box modules
(`CvSTauL4932K*V1.lean`, `CvSDiagL4932V1.lean`) from the parent of `rr/`, so run this in a copy of
`rr/` placed next to the regenerated modules (`CK = REPO/research/rh/checkpoints`):

```
python3 gen_rr4932.py 49/32 2000 7/5 66 0 0 0 156 15 13                  # rr43_data.pkl
python3 $CK/20261110_window_l32_feasibility_v1/rescale_pkl.py             # in place, Pscale 544 -> 520
python3 $REPO/research/rh/feshbach_lean_v1/tools/cert43.py 80             # cert43_80.pkl (98 s)
python3 $CK/20261110_window_l32_feasibility_v1/check_cert_pkl.py cert43_80.pkl   # exit 0
```

sha256 of the files used: `rr43_data.pkl` before rescaling
`a19b40dcea67bd7793d7d20c4c259530db5a6d38478fe8225486b7efdbae0ef9`, after
`b1546d7eb58c2dfa803e7e40d0ada128cf68925cb0f4e66fc4868ba7f414faf1`; `cert43_80.pkl`
`7ac54108797550c6c308a5b7dd412797176c77a91e7dced84ee6cad89089cf0e`.

## Replay

Lab closure as in `../20261112_window_l32_v1/` (1019 modules). Lab and 3/2 modules imported here:
`CvSTraceM4SlackV1` (`../20261110_window_l32_trace_port_v1/`), `CvSHplusK300V1`
(`../20261111_window_l32_diagonal_v1/port_hplus.py`), `FastKronV1`, `CvSRelRowHarmV1`,
`CvSRelRowAlgebraV1`, `CvSSchurClosureFromBoundsV1`, `CvSGramTailV1`, `CvSPackedGramV1`
(`../20261112_window_l32_rowcert_v1/build_list.txt`). Then `lean` on the modules of
`build_order.txt` in that order.

## Receipt (local, 2026-11-12; Lean 4.33.1, Mathlib `0df444a`)

Default trust and `--trust=0` (`build_order.txt` order): 70 / 70 modules exit 0 in each run, 0 errors,
0 `sorry`; 20003 s and 20213 s in total.

| module | default (s) | `--trust=0` (s) |
|---|---:|---:|
| `CvSTraceCertL4932V1` | 2674 | 3043 |
| `CvSTraceCellL4932V1`, `DistK156`, `Integral`, `CvSExpL4932V1` | 18, 6, 6, 6 | 19, 7, 7, 5 |
| `CvSTauL4932K{1,…,1951}V1` (40) | 6528 in total, at most 273 each | 6296 in total, at most 275 each |
| `CvSTauL4932AllV1`, `CvSTauL4932V1`, `CvSTauFastL4932V1`, `CvSNodeL4932V1` | 19, 11, 11, 6 | 18, 11, 13, 8 |
| `CvSDiagL4932V1` | 2244 | 2389 |
| `CvSRelRowCertL4932V1` | 617 | 596 |
| `CvSRelRowDataA0L4932V1`, `A1`, `A` | 331, 2095, 1934 | 334, 1998, 1981 |
| `CvSRelRowDataL4932V1` | 729 | 672 |
| `CvSRelRowCheckL4932V1` (16 chunks, about 133 s each) | 2329 | 2298 |
| `CvSRelRowBoxL4932V1` | 253 | 251 |
| `Psd`, `Q`, `Tail`, `In`, `Err`, `Out`, `Kt`, `Form`, `HB`, `Inv` | 29, 21, 20, 16, 15, 13, 9, 7, 7, 6 | 65, 22, 17, 17, 13, 12, 9, 9, 7, 6 |
| `CvSTauFarL4932V1` | 13 | 9 |
| `CvSWindowL4932V1`, `RHWindowL4932ExhaustionV1` | 23, 7 | 75, 6 |

Peak memory about 12.7 GB (`CvSRelRowCheckL4932V1`). In both runs all 152 `#print axioms` reports
list a subset of `[propext, Classical.choice, Quot.sound]`:

```
'AEGIS.CvSWindowL4932V1.augment_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSWindowL4932V1.window_L4932' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL4932ExhaustionV1.window_le_forty_nine_sixty_fourths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL4932ExhaustionV1.final_sign_iff_windows_above_forty_nine_sixty_fourths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL4932ExhaustionV1.rh_iff_windows_above_forty_nine_sixty_fourths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence kind: `lean_kernel` (local).

## Remaining

The windows `L > 49/64`. Not RH.
