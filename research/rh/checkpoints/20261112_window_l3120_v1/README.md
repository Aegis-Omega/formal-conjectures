# The window 2r ≤ 31/20 and the exhaustion step with frontier 31/40

Date: 2026-11-12. Status: **kernel-checked locally**, default trust and `--trust=0` (70 modules
each). Not run in CI.
**RH remains OPEN.** The windows `L > 31/40` are not proved.

## Result

```lean
theorem AEGIS.CvSWindowL3120V1.window_L3120 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 31 / 20) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re

theorem AEGIS.RHWindowL3120ExhaustionV1.window_le_thirty_one_fortieths {L : ℝ} (hL : L ≤ 31 / 40) :
    WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL3120ExhaustionV1.final_sign_iff_windows_above_thirty_one_fortieths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 31 / 40 < L → WindowArithmeticNonpositiveV1 L
theorem AEGIS.RHWindowL3120ExhaustionV1.rh_iff_windows_above_thirty_one_fortieths :
    RiemannHypothesis ↔ ∀ L : ℝ, 31 / 40 < L → WindowArithmeticNonpositiveV1 L
```

`RiemannHypothesis` is Mathlib's, through `V13Scratch.final_sign_iff_rh_v13`. The last theorem is a
reduction, not RH: it moves the open part from the windows `L > 49/64`
(`../20261112_window_l4932_v1/`, `rh_iff_windows_above_forty_nine_sixty_fourths`) to the windows
`L > 31/40 = 0.775`.

## How

The 49/32 construction with `LT = 31/20`: `CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment`
with `M = 4`, `L = 2`, `LT = 31/20`, `m = 33/20`, no correction terms, `ε = 7/5`, 311 atoms
(`ctr i = i − 155`), rows `NP = 2000`, `κ = 66`, `|τ_n| ≤ 15` for `|n| ≥ 2001`, trace bound `T = 3`
(`K = 156`). Changed premises:

| premise | source (this checkpoint) |
|---|---|
| `31/20 < log 5` | `log_five_gt` (`e^31 < 5^20` from `Real.exp_one_lt_d9`) |
| `e^{−31/40}` enclosure | `CvSExpL3120V1.e3140_bounds` (`Real.exp_bound`, 24 terms) |
| `66 ≤ (2π)²·(31/20)·(33/20 − T/(2π))` (about 71.75 at `T = 3`) | `CvSTraceCertL3120V1.trace_premises_L3120` |
| `τ_k` boxes, `1 ≤ k ≤ 2000` | 40 data modules; widths `1.0·10⁻¹¹` for `k ≤ 156` (`10⁻¹⁰` at 49/32), `10⁻⁹` above |
| `cvsEntry M (31/20) n n`, `n ≤ 156` | `CvSDiagL3120V1` (`K = 300`, widths `6.0·10⁻¹²`) |

Why the low boxes are tighter (`FEASIBILITY_3120.log`, the lab's row and trace mirrors): with the
49/32 radii (`5·10⁻¹¹` for `k ≤ 156`, `5·10⁻¹⁰` above, diagonal `3·10⁻¹²`) the row check fails at
`31/20` (scaled `λ_min −2.48·10⁻¹⁰` at `NP = 2000`, `−8.2·10⁻¹¹` at 2500). The low radius is what
matters: `5·10⁻¹²` gives `+5.73·10⁻¹⁰`, while the high radius and `κ = 70` move it by under
`2·10⁻¹¹`. The `τ` mirror needs about 2.2 times as many terms for `k ≤ 156`. The trace mirror gives
`T = 2.940` at `31/20` (`2.874` at 49/32); the kernel chunk totals sum to `2.94056 ≤ 3`.

The relative row certificate from the kernel-checked boxes: scaled `λ_min 5.87004·10⁻¹⁰`
(`Pscale 536 → 516` by `rescale_pkl.py`), LDL at `q = 80`: `eps = 354821902183103`,
`eta = 109375911459632 < eps`.
`RHWindowL3120ExhaustionV1` is `RHWindowL32ExhaustionV1` with `window_L3120` and `31/40`.

The next steps on this route are short: `25/16` needs `NP = 2500` and low radii `5·10⁻¹³`
(`+3.84·10⁻¹⁰` in the mirror), probably beyond the kernel memory of this layout on a 15 GB machine
(the row check `CvSRelRowCheckL3120V1` peaked at about 14.7 GB at `NP = 2000`);
`8/5` needs `NP = 4000` (`../20261112_window_beyond_l32_feasibility_v1/`). With `M = 4` the route
stops below `log 5 / 2 ≈ 0.805`.

## Files

* `make_port3120.py L4932_DIR OUT` derives every script of this checkpoint and `CvSExpL3120V1.lean`
  from `../20261112_window_l4932_v1/` by counted substitution (`LT`, `2/LT`, `4/LT`, `LT/2`, `LT²`,
  `LT ± 1`, `e^{−LT/2}`, `log 5 > LT`, `LT/2001`, the low `τ` target `3·10⁻¹⁰ → 3·10⁻¹¹`,
  names).
  The kernel found three places in the first build where the straight substitution is not enough;
  `make_port3120.py` handles them:
  1. `port_diag` replaced the token `40` (the `K` of the 11/8 diagonal) after its `2/LT` rule, and
     `2/LT = 40/31` contains that token (`CvSDiagL3120V1` failed on `300 * n * x / 31`); the
     derived `port_diag_l3120.py` substitutes `K` and `N` first (with that order the 49/32
     diagonal module is byte-identical, checked).
  2. `make_taufast` writes `Dk = 49·10²⁰` as a numeral; now `31·10²⁰` (`CvSTauFastL3120V1` failed
     on `om_cast`).
  3. `make_rr_check` fixes the check-matrix scale `PS = 520` of 49/32; here
     `Pscale = 488 + 4(bitlen(31²) + 2) − 2·10 = 516` (every `rowsOk` chunk of
     `CvSRelRowCheckL3120V1` failed at 520), interval shift `440 → 436`.
  A scan of the 70 modules for lines left as at 49/32 that contain `49`, `64`, `128`, `2401`,
  `4096` or `1024` finds only indices, the scales `2^49`, `2^128` and chunk names.
* `rr/set_rules3120.py` sets the nine data constants of `rr/port_rules3120.json` (box maxima,
  `A0lit`, `A1lit`, `Cu = 78525/10⁶ ≥ 31/(40π²)`) from `rr43_data.pkl`.
* `regen.sh REPO OUT` regenerates the 69 generated modules, the 8 derived scripts and the diagonal
  data and checks them against `generated.sha256` (78 files; checked 2026-11-12, 46 s, all match).
  The generated modules are not committed; `CvSExpL3120V1.lean` is (the hand-written 49/32 module
  with the constants of `e^{−31/40}`, from `Real.exp_bound` with 24 terms).
* `cert3120_totals.json`: the chunk totals of the trace certificate (`gen_cert3120.py --eval`, as at
  49/32; the kernel re-checks every bound).
* `build_order.txt`: the 70 modules in dependency order. `FEASIBILITY_3120.log`: the mirror runs.

The row-certificate pickles are untrusted inputs and are not committed. As at 49/32, run in a copy
of `rr/` placed next to the regenerated modules (`CK = REPO/research/rh/checkpoints`):

```
python3 gen_rr3120.py 31/20 2000 7/5 66 0 0 0 156 15 13                  # rr43_data.pkl
python3 $CK/20261110_window_l32_feasibility_v1/rescale_pkl.py             # in place, Pscale 536 -> 516
python3 $REPO/research/rh/feshbach_lean_v1/tools/cert43.py 80             # cert43_80.pkl (104 s)
python3 $CK/20261110_window_l32_feasibility_v1/check_cert_pkl.py cert43_80.pkl   # exit 0
python3 set_rules3120.py                                                  # port_rules3120.json
```

sha256: `rr43_data.pkl` before rescaling
`c48c2e2cdf04f2323df092a5f781f5dd67f3dcfa55f5eecedb9ee726e008c7be`, after
`f6e57cb1faab3b070d1159328eff2bd1966eb5c955868ac9151c727b5a832daf`; `cert43_80.pkl`
`3e9cf01ea5acace2e7e5cd8ccb0e27059667a794a027ed9fded4cb9e801b2543`.

## Replay

As `../20261112_window_l4932_v1/` (same lab and 3/2 modules), then `lean` on the modules of
`build_order.txt` in that order.

## Receipt (local, 2026-11-12/13; Lean 4.33.1, Mathlib `0df444a`)

Default trust (`build_order.txt` order, after the three fixes above) and `--trust=0` (same order): 70 / 70
modules exit 0 in each run, 0 errors, 0 `sorry`; 20840 s and 19225 s in total.

| module | default (s) | `--trust=0` (s) |
|---|---:|---:|
| `CvSTraceCertL3120V1` | 2772 | 2517 |
| `CvSTraceCellL3120V1`, `DistK156`, `Integral`, `CvSExpL3120V1` | 23, 8, 8, 7 | 18, 7, 6, 6 |
| `CvSTauL3120K{1,…,1951}V1` (40) | 6777 in total, at most 313 each (`K1`) | 6664 in total, at most 687 each (`K1751`) |
| `CvSTauL3120AllV1`, `CvSTauL3120V1`, `CvSTauFastL3120V1`, `CvSNodeL3120V1` | 17, 11, 13, 8 | 18, 10, 11, 6 |
| `CvSDiagL3120V1` | 2924 | 2634 |
| `CvSRelRowCertL3120V1` | 602 | 558 |
| `CvSRelRowDataA0L3120V1`, `A1`, `A` | 311, 1980, 1941 | 278, 1861, 1807 |
| `CvSRelRowDataL3120V1` | 657 | 607 |
| `CvSRelRowCheckL3120V1` (16 chunks) | 2357 | 1876 |
| `CvSRelRowBoxL3120V1` | 227 | 198 |
| `Psd`, `Q`, `Tail`, `In`, `Err`, `Out`, `Kt`, `Form`, `HB`, `Inv` | 38, 21, 16, 17, 14, 12, 8, 7, 6, 5 | 14, 14, 14, 15, 12, 12, 8, 6, 6, 5 |
| `CvSTauFarL3120V1` | 8 | 7 |
| `CvSWindowL3120V1`, `RHWindowL3120ExhaustionV1` | 39, 6 | 23, 7 |

The `--trust=0` run was interrupted by a machine restart and resumed (modules already written were kept);
the times are per module as logged. Peak memory about 14.7 GB at default trust and about 13.5 GB at
`--trust=0` (`CvSRelRowCheckL3120V1`, sampled every 5 s). In both runs all 152 `#print axioms` reports list a
subset of `[propext, Classical.choice, Quot.sound]`:

```
'AEGIS.CvSWindowL3120V1.augment_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSWindowL3120V1.window_L3120' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3120ExhaustionV1.window_le_thirty_one_fortieths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3120ExhaustionV1.final_sign_iff_windows_above_thirty_one_fortieths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.RHWindowL3120ExhaustionV1.rh_iff_windows_above_thirty_one_fortieths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence kind: `lean_kernel` (local).

## Remaining

The windows `L > 31/40`. Not RH.
