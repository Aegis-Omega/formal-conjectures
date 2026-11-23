# The window 2r ≤ 39/25 and the exhaustion step with frontier 39/50

Date: 2026-11-13. Status: **kernel-checked locally**, default trust (70 modules). The `--trust=0` replay
is running (receipt below to be completed). Not run in CI.
**RH remains OPEN.** The windows `L > 39/50` are not proved.

## Result

```lean
theorem AEGIS.CvSWindowL3925V1.window_L3925 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 39 / 25) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

theorem AEGIS.RHWindowL3925ExhaustionV1.window_le_thirty_nine_fiftieths {L : ℝ} (hL : L ≤ 39 / 50) :
    WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL3925ExhaustionV1.final_sign_iff_windows_above_thirty_nine_fiftieths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 39 / 50 < L → WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL3925ExhaustionV1.rh_iff_windows_above_thirty_nine_fiftieths :
    RiemannHypothesis ↔ ∀ L : ℝ, 39 / 50 < L → WindowArithmeticNonpositiveV1 L
```

`RiemannHypothesis` is Mathlib's, through `V13Scratch.final_sign_iff_rh_v13`. The last theorem is a
reduction, not RH: it moves the open part from the windows `L > 31/40`
(`../20261112_window_l3120_v1/`, `rh_iff_windows_above_thirty_one_fortieths`) to the windows
`L > 39/50 = 0.78`.

## How

The 31/20 construction with `LT = 39/25`: `CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment`
with `M = 4`, `L = 2`, `LT = 39/25`, `m = 33/20`, no correction terms, `ε = 7/5`, 311 atoms, rows
`NP = 2000`, `κ = 66`, `|τ_n| ≤ 15` for `|n| ≥ 2001`, trace bound `T = 3` (`K = 156`). Changed premises:

| premise | source (this checkpoint) |
|---|---|
| `39/25 < log 5` | `CvSWindowL3925V1.log_five_gt` (`e^39 < 5^25`) |
| `e^{−39/50}` enclosure | `CvSExpL3925V1.e3950_bounds` (`Real.exp_bound`, 24 terms) |
| `66 ≤ (2π)²·(39/25)·(33/20 − T/(2π))` (about 72.21 at `T = 3`) | `CvSTraceCertL3925V1.trace_premises_L3925` |
| `τ_k` boxes, `1 ≤ k ≤ 2000` | 40 data modules; widths `1.0·10⁻¹²` for `k ≤ 156` (`10⁻¹¹` at 31/20), `10⁻⁹` above |
| `cvsEntry M (39/25) n n`, `n ≤ 156` | `CvSDiagL3925V1` (`K = 300`, widths `6·10⁻¹²`) |

The mirrors (`FEASIBILITY_3925.log`): with low radius `5·10⁻¹²` the scaled row `λ_min` is
`1.31·10⁻¹⁰`, with `5·10⁻¹³` it is `2.24·10⁻¹⁰` and the LDL passes at `q = 80`; the trace mirror gives
`T = 2.978`, and the kernel chunk totals (`cert3925_totals.json`) sum to `2.97842 ≤ 3`.

The relative row certificate from the kernel-checked boxes: scaled `λ_min 2.40071·10⁻¹⁰`
(`Pscale 540 → 518` by `rescale_pkl.py`, shift 11), LDL at `q = 80`: `eps = 145113810260410`,
`eta = 115239628596952 < eps`. `Cu = 79032/10⁶ ≥ 39/(50π²) ≈ 0.0790305`.
`RHWindowL3925ExhaustionV1` is `RHWindowL3120ExhaustionV1` with `window_L3925` and `39/50`.

## Files

* `make_port3925.py L4932_DIR OUT` is the general form of `../20261112_window_l3120_v1/make_port3120.py`
  (`p, q = 39, 25`, `SHIFT = 11`, `PS = 488 + 4(bitlen(p²) + 2) − 2·SHIFT = 518`, low `τ` target
  `3·10⁻¹²`, with the three fixes of the 31/20 port built in). Run on `../20261112_window_l4932_v1/` it
  writes the 23 derived files of this window (`CvSExpL3925V1.lean`, `build_order.txt`, `regen.sh`, the
  `make_*` and `port_*` scripts and eleven `rr/` scripts), byte-identical to the ones the build used
  (checked 2026-11-13); they are not committed again. Its `rr/port_rules3925.json` has the 49/32 data
  constants.
* `rr/set_rules3925.py` sets the nine data constants of `rr/port_rules3925.json` from `rr43_data.pkl`;
  `rr/port_rules3925.json` here is its output.
* `generated.sha256`: the 78 generated files (69 modules, 8 derived scripts, the diagonal data).
* `cert3925_totals.json`: the trace chunk totals. `FEASIBILITY_3925.log`: the mirror runs.

Replay (`CK = REPO/research/rh/checkpoints`):

```
python3 make_port3925.py $CK/20261112_window_l4932_v1 OUT
cp rr/set_rules3925.py rr/port_rules3925.json OUT/rr/
cp generated.sha256 cert3925_totals.json OUT/
cd OUT && bash regen.sh REPO MODS      # with rr/rr43_data.pkl and rr/cert43_80.pkl in OUT/rr/
```

Checked 2026-11-13 from a clean export of this branch at `165ebcbb` (`research/rh/checkpoints`,
`feshbach_lean_v1`, `aegis_math`, `moment_killer_v1`): `regen: all 78 files match` (49 s), and the
built tree matches `generated.sha256` as well. Then build as `../20261112_window_l3120_v1/` with the
`3925` names. The row-certificate pickles are untrusted inputs and are not committed; in a copy of
`OUT/rr/` next to the regenerated modules:

```
python3 gen_rr3925.py 39/25 2000 7/5 66 0 0 0 156 15 13                  # rr43_data.pkl
python3 $CK/20261110_window_l32_feasibility_v1/rescale_pkl.py             # in place, Pscale 540 -> 518
python3 $REPO/research/rh/feshbach_lean_v1/tools/cert43.py 80             # cert43_80.pkl
python3 $CK/20261110_window_l32_feasibility_v1/check_cert_pkl.py cert43_80.pkl   # exit 0
python3 set_rules3925.py                                                  # port_rules3925.json
```

sha256: `rr43_data.pkl` before rescaling
`fee5eebd1635d723006797a02c1ac2a2e7319e8e2c4f096946f48261d848c42d`, after
`671764f420bde187376170ac4c50055f06b7a3b12526b54c88c6d6e6d68f3520`; `cert43_80.pkl`
`1e0bc4d9ed0c9310d094a5678d7f7af7ea3742a6ecc00e04063eff719e3d01d0`.

## Receipt (local, 2026-11-13; Lean 4.33.1, Mathlib `0df444a`)

Default trust (`build_order.txt` order): 70 / 70 modules exit 0, 0 errors, 0 `sorry`; 21587 s in total
(other jobs shared the machine).

| module | default (s) |
|---|---:|
| `CvSTraceCertL3925V1` | 3036 |
| `CvSTraceCellL3925V1`, `DistK156`, `Integral`, `CvSExpL3925V1` | 20, 8, 7, 6 |
| `CvSTauL3925K{1,…,1951}V1` (40) | 6742 in total, at most 596 each (`K101`) |
| `CvSTauL3925AllV1`, `CvSTauL3925V1`, `CvSTauFastL3925V1`, `CvSNodeL3925V1` | 16, 10, 11, 5 |
| `CvSDiagL3925V1` | 2902 |
| `CvSRelRowCertL3925V1` | 520 |
| `CvSRelRowDataA0L3925V1`, `A1`, `A` | 299, 1963, 2000 |
| `CvSRelRowDataL3925V1` | 675 |
| `CvSRelRowCheckL3925V1` (16 chunks) | 2657 |
| `CvSRelRowBoxL3925V1` | 246 |
| `Psd`, `Q`, `Tail`, `In`, `Err`, `Out`, `Kt`, `Form`, `HB`, `Inv` | 233, 20, 18, 17, 13, 13, 10, 9, 7, 6 |
| `CvSTauFarL3925V1` | 9 |
| `CvSWindowL3925V1`, `RHWindowL3925ExhaustionV1` | 102, 7 |

Peak memory about 13.2 GB (`CvSRelRowCheckL3925V1`, sampled every 5 s). All 152 `#print axioms` reports
list a subset of `[propext, Classical.choice, Quot.sound]`:

```
'AEGIS.CvSWindowL3925V1.augment_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSWindowL3925V1.window_L3925' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3925ExhaustionV1.window_le_thirty_nine_fiftieths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3925ExhaustionV1.final_sign_iff_windows_above_thirty_nine_fiftieths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3925ExhaustionV1.rh_iff_windows_above_thirty_nine_fiftieths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`--trust=0`: running (`build_order.txt` order); to be recorded here.

Evidence kind: `lean_kernel` (local).

## Remaining

The windows `L > 39/50`. Not RH.
