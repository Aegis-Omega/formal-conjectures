# The window 2r ≤ 8/5 and the exhaustion step with frontier 4/5

Date: 2026-11-13. Status: **kernel-checked locally** at default trust and with `--trust=0`, 111 modules
(receipt below, 2026-11-21). Not run in CI.
**RH remains OPEN.** The windows `L > 4/5` are not proved.

## Result

```lean
theorem AEGIS.CvSWindowL85V1.window_L85 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 8 / 5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

theorem AEGIS.RHWindowL85ExhaustionV1.window_le_four_fifths {L : ℝ} (hL : L ≤ 4 / 5) :
    WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL85ExhaustionV1.final_sign_iff_windows_above_four_fifths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 4 / 5 < L → WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL85ExhaustionV1.rh_iff_windows_above_four_fifths :
    RiemannHypothesis ↔ ∀ L : ℝ, 4 / 5 < L → WindowArithmeticNonpositiveV1 L
```

The last theorem is a reduction, not RH: it moves the open part from the windows `L > 39/50`
(`../20261113_window_l3925_v1/`) to the windows `L > 4/5`.

`8/5` is close to the end of the `M = 4` construction: the prime powers in the window are `2, 3, 4`
while `LT < log 5 ≈ 1.6094`, so this family of certificates cannot pass `L = log 5 / 2 ≈ 0.8047`; beyond
it the prime `5` enters (`M = 5`, new atoms).

## How

The 39/25 construction with `LT = 8/5` and four changed parameters:

| | 39/25 | 8/5 | why |
|---|---|---|---|
| rows `NP` (`|τ_n| ≤ 15` for `|n| > NP`) | 2000 | 4000 | the row matrix at `NP = 2000` is not positive (`FEASIBILITY_85.log`) |
| slack `m` | 33/20 | 8/5 | with `m = 33/20` the slack reaches `t* = 613.9`, past the atom range `2π·156/LT = 612.6` |
| diagonal series terms `K` | 300 | 600 | box widths `3.9·10⁻¹³` (`6.2·10⁻¹²` at `K = 300`); the row matrix needs `≲ 6·10⁻¹³` |
| LDL scale `q` | 80 | 88 | `q = 80, 84` fail on the rescaled pickle |

`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 8/5`, `m = 8/5`, `ε = 7/5`, 311 atoms,
`κ = 66`, trace bound `T = 3` (`K = 156`). Changed premises:

| premise | source (this checkpoint) |
|---|---|
| `8/5 < log 5` | `CvSWindowL85V1.log_five_gt` (`e^8 < 5^5`) |
| prime powers `j + 1 ≥ 5` at the window end | `CvSNodeL85V1.node_big`, new proof from `e^8 < 5^5` (the bound `log 5 ≥ 1/5 + 2 log 2 ≈ 1.586` of the earlier windows is below `8/5`) |
| `e^{−4/5}` enclosure | `CvSExpL85V1.e45_bounds` (`Real.exp_bound`, 24 terms) |
| `66 ≤ (2π)²·(8/5)·(8/5 − T/(2π))` (about 70.9 at `T = 3`) | `CvSTraceIntegralL85V1.gap_of_T`, `CvSTraceCertL85V1.trace_premises_L85` (3060 cells on `|t| < 600`) |
| `τ_k` boxes, `1 ≤ k ≤ 4000` | 80 data modules; widths `1.0·10⁻¹²` for `k ≤ 156`, at most `1.0·10⁻⁹` above (about `7·10⁻¹¹` near `k = 4000`, where the head sums are long) |
| `cvsEntry M (8/5) n n`, `n ≤ 156` | `CvSDiagL85V1` with `CvSHplusK600V1` (`K = 600`, 40 chunks of 4 rows, widths `3.9·10⁻¹³`) |
| `|τ_n| ≤ 15` for `|n| ≥ 4001` | `CvSTauFarL85V1` |

The relative row certificate from the generated boxes: scaled `λ_min 4.46647·10⁻¹¹` (`Pscale 524 → 508`
by `rescale_pkl.py`, shift 8), LDL at `q = 88`: `eps = 6911523514429976`, `eta = 1846315636526107 < eps`,
entries of 45 bits. `Cu = 81058/10⁶ ≥ 8/(10π²) ≈ 0.0810569`. The trace chunk totals (`cert85_totals.json`)
sum to `2.89286 ≤ 3` (mirror `T = 2.8925`). `RHWindowL85ExhaustionV1` is `RHWindowL3925ExhaustionV1` with
`window_L85` and `4/5`.

## Files

* `make_port85.py L4932_DIR D1` is `../20261113_window_l3925_v1/make_port3925.py` at `p, q = 8, 5`
  (`SHIFT = 8`, `PS = 508`; `2/LT`, `4/LT`, `1/LT` written with their own denominators; the `log 5`
  assertion of `node_big` dropped).
* `make_np85.py D1 OUT` is the second layer: every `NP`-derived number by one token pass
  (`NP`, `NP + 1`, `NP − 49`, `NP − 156`, `2NP + 1`, `NP + 156`, `NP + 157`, `NP + 158`, the rounding
  counts `2(NP − 156)`, `4(NP − 156)`, `4(NP − 156) + 1`, the harmonic errors `4(NP + 156)` and
  `4(NP + 156) + 76`, `5(NP + 1)`, the `K`-table error `3500000 ≥ 225(4(NP − 156) + 1) + 2`, and
  `hupN 4156`), the 80 tau modules in `build_order.txt`, the outside-row checks in chunks of 4 rows,
  `m = 8/5` with the trace layout `TOP = 600`, `K = 600` for the diagonal (`CvSHplusK600V1` by
  `port_hplus.py`, 40 chunks of 4 rows, and `maxRecDepth 100000` for `D_bounds`, whose box arithmetic at
  `K = 600` passes the default depth), `maxHeartbeats 2000000` for `tau_mem_all` (its `if_neg` simp work
  over 80 blocks passes the default 200000), `q = 88`, and `node_big`.
  The two together write the 23 derived files of this window into `OUT`.
* `rr/set_rules85.py` sets the nine data constants of `rr/port_rules85.json` from `rr43_data.pkl`;
  `rr/port_rules85.json` here is its output.
* `generated.sha256`: the 119 generated files (110 modules, 8 derived scripts, the diagonal data).
* `CvSExpL85V1.lean` is hand-written, not generated (`make_np85.py` skips it); copy it into the module
  directory before the build. With the 110 generated modules it makes the 111 of `order.txt`.
* `cert85_totals.json`: the trace chunk totals. `FEASIBILITY_85.log`: the mirror runs.

Replay (`CK = REPO/research/rh/checkpoints`):

```
python3 make_port85.py $CK/20261112_window_l4932_v1 D1
python3 make_np85.py D1 OUT
cp rr/set_rules85.py rr/port_rules85.json OUT/rr/
cp generated.sha256 cert85_totals.json OUT/
cd OUT && bash regen.sh REPO MODS      # with rr/rr43_data.pkl and rr/cert43_88.pkl in OUT/rr/
```

Checked 2026-11-15 from a clean export of this branch at `30cf77cc`: `regen: all 119 files match`
(about 2 min; `scripts/emit_rr85.py` with its `2^44` doc line, as in `CvSRelRowCertL85V1`); these 119 files
are the sources of the build below. The row-certificate pickles are untrusted
inputs and are not committed; in a copy of `OUT/rr/` next to the regenerated modules:

```
python3 gen_rr85.py 8/5 4000 7/5 66 0 0 0 156 15 13                      # rr43_data.pkl
python3 $CK/20261110_window_l32_feasibility_v1/rescale_pkl.py             # in place, Pscale 524 -> 508
python3 $REPO/research/rh/feshbach_lean_v1/tools/cert43.py 88             # cert43_88.pkl
python3 $CK/20261110_window_l32_feasibility_v1/check_cert_pkl.py cert43_88.pkl   # exit 0
python3 set_rules85.py                                                    # port_rules85.json
```

sha256: `rr43_data.pkl` before rescaling
`2248f93e34ff83608a600e2ec1e881aaea1301a641362b185ca7cbe3372c19b0`, after
`f4356aec1ae9ba7909accccee701f450b0a81704c11958dcda09f5b3e5f96906`; `cert43_88.pkl`
`227c459136fbc8e667c1270cb4c8e84eed1e683370b22787e87a45e0e010cdb1`.

The trace totals: `python3 OUT/scripts/gen_cert85.py EVAL.lean --eval`, with the two list `#eval`s
printed through `IO.println (toString …)`; compiling `EVAL.lean` prints `cert85_totals.json`.

## Receipt (local, 2026-11-21; Lean 4.33.1, Mathlib `0df444a`)

The 110 generated modules that were built match `generated.sha256` (110 / 110); `CvSExpL85V1.lean` is the file
in this folder.

Default trust and `--trust=0` (`order.txt` order): 111 / 111 modules exit 0 in each run, 0 errors,
0 `sorry`; 47460 s and 48037 s in total (the default build resumed after three container
restarts; each module was rebuilt from its sources, never from a partial `.olean`).

| module | default (s) | `--trust=0` (s) |
|---|---:|---:|
| `CvSRelRowDataA1L85V1` | 6696 | 6665 |
| `CvSRelRowDataAL85V1` | 5455 | 5733 |
| `CvSDiagL85V1` | 4202 | 3416 |
| `CvSRelRowCheckL85V1` | 3170 | 2917 |
| `CvSTraceCertL85V1` | 2545 | 2358 |
| `CvSRelRowDataL85V1` | 1368 | 1558 |
| `CvSRelRowDataA0L85V1` | 1237 | 1407 |
| `CvSRelRowBoxL85V1` | 1332 | 957 |
| the other 103 modules | 21455 in total | 23026 in total |

Default run: `CvSRelRowCertL85V1`, `CvSTauL85K101V1` finished with an `.olean` and 0 errors but no logged exit code or time (excluded from the default total); their `--trust=0` runs are logged in full.

Peak memory about 13.1 GB default (`CvSRelRowCheckL85V1`) and 14.8 GB at `--trust=0` (`CvSRelRowDataA0L85V1`).
In both runs all 386 `#print axioms` reports (193 default, 193 `--trust=0`) list a subset of
`[propext, Classical.choice, Quot.sound]`:

```
'AEGIS.CvSWindowL85V1.augment_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSWindowL85V1.window_L85' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL85ExhaustionV1.window_le_four_fifths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL85ExhaustionV1.final_sign_iff_windows_above_four_fifths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL85ExhaustionV1.rh_iff_windows_above_four_fifths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence kind: `lean_kernel` (local).

## Remaining

The windows `L > 4/5`. Not RH. The next window past `log 5 / 2` does not close with the parameters of
this family: at `LT = 13/8` the prime `5` moves the trace slack to `t* ≥ 1366`, which needs at least 721 atoms
(`K = 360`, `κ ≤ 36.9`), and with those the row mirror stays negative (`−4.97·10⁻⁹`, `−3.14·10⁻⁹`, `−2.41·10⁻⁹` at
`NP = 4000, 8000, 16000`; `gen_rr_k5.py`, `FEASIBILITY_85.log`). Larger `κ` needs 901 to 1321 atoms.
That is with the Krein slot empty (no hats, no boundary terms) and every prime cosine at its worst case. With four
even boundary terms the 13/8 trace allows `κ ≈ 63–69` at 721 atoms, and the row mirror at `κ = 63`, `NP = 8000` with
tighter boxes is positive (its exact LDL passes at `q = 92`): `../20261114_window_l138_feasibility_v1/`.
