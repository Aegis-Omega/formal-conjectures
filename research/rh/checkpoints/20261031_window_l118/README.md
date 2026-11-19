# The window 2r ≤ 11/8 (Lean 2026-10-31)

`CvSWindowL118V1.window_L118` closes the window 2r ≤ 11/8, and
`RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths` reduces RH to the log windows
L > 11/16. The previous frontier was 2/3 (`RHWindowL43ExhaustionV1`). The windows L > 11/16 are
not proved. This is one window. Not RH.

The route and the module structure are the same as at 4/3 (`../20261026_window_l43/README.md`).
11/8 = 1.375 < log 4 ≈ 1.3863, so no new prime power enters the symbol, and `ScertM 3` and the
slack-only Krein certificate keep their form. What changes is the trial space, the trace bound and
the row budget.

## Parameters

| premise | value at LT = 11/8 |
|---|---|
| trace and Krein (`trace_premises_L118`) | 2205 cells on \|t\| < 315 (51 kernel chunks), m = 33/20, T = 7/2 |
| `hk` | (2π)²·(11/8)·(33/20 − T/(2π)) ≈ 59.33 ≥ κ = 58 |
| row budget (`hB`) | `Brow ≤ 58 Q_CvS` at NP = 250, T_τ = 13, ε = 7/10 |
| constants (`K_ok`) | K' = 58 ε_Q + ε_in + ε_out + ε_T ≈ 1.2961e-6 ≤ Kq/2^64 ≈ 1.2974e-6 |
| check matrix | 139 × 139, scaled λ_min ≈ 4.99e-7 (`cert43.py 64`) |

The parameters were chosen with `gen_rr_lt.py` (`FEASIBILITY_118.log`). At NP = 200 the check
needs κ ≥ 62, above what the trace allows; NP = 250 with ε = 7/10 passes at κ = 58. The row
certificate needs 360 rows outside the low block.

## Modules

In `feshbach_lean_v1` (ports of the 4/3 modules, with L = 11/8, e^{−11/16} and ω_k = 16πk/11):
- τ_k for 1 ≤ k ≤ 250 and every prime cutoff M ≥ 3: `CvSTauL118V1`, `CvSTauL118DataV1` (k ≤ 70,
  14 kernel batches), `CvSTauPrimeL118V1`, `CvSTauR1SourceL118V1`, `CvSTauR1PrimeL118V1`
  (71 ≤ k ≤ 250);
- |τ_n| ≤ 13 for |n| ≥ 71: `CvSTauFarL118V1`;
- the diagonal, n ≤ 70: `CvSDiagL118V1`;
- trace: `CvSTraceCellL118V1`, `CvSTraceIntegralL118V1`, `CvSTraceCertL118V1`;
- the relative row certificate: `CvSRelRowDataL118V1` and `CvSRelRowCertL118V1` (generated, see
  below), `CvSRelRowCheckL118V1`, `CvSRelRowPsdL118V1`, `CvSRelRowFormL118V1`,
  `CvSRelRowBoxL118V1`, `CvSRelRowErrL118V1`, `CvSRelRowQL118V1`, `CvSRelRowKtL118V1`,
  `CvSRelRowOutL118V1`, `CvSRelRowTailL118V1`, `CvSRelRowInvL118V1`, `CvSRelRowInL118V1`,
  `CvSRelRowHBL118V1` (`hB`, `K_ok`, `Q_nonneg`).

In this directory:
- `CvSWindowL118V1`: `window_L118`, from `window_of_certificate_gram_moment` with M = 3, L = 2,
  LT = 11/8, m = 33/20, `trace_premises_L118` and `hB`;
- `RHWindowL118ExhaustionV1`: `window_le_eleven_sixteenths`,
  `final_sign_iff_windows_above_eleven_sixteenths`, `rh_iff_windows_above_eleven_sixteenths`.

## Data pipeline (untrusted; the kernel rechecks every value)

- τ and diagonal boxes: `tools/gen_tau118.py`, `gen_tau_prime118.py`, `gen_tau_r1_118.py 250`,
  `gen_diag118.py` (ports of the 4/3 generators).
- Trace cells: `gen_cert118.py` here, with `cert118_totals.json` (the chunk totals printed by its
  `--eval` output).
- Row certificate: `tools/gen_rr118.py` (reads the committed boxes through `tools/boxes118.py`),
  `tools/cert43.py 64`, `tools/emit_rr118.py OUTDIR`. The outputs `CvSRelRowDataL118V1.lean`
  (82 KB) and `CvSRelRowCertL118V1.lean` (132 KB) are not committed: `rh-cvs-window-l65-source.yml`
  generates them, checks their sha256 against the local run that produced the proofs, compiles the
  DAG of all three windows from source and audits the axioms of every module.

Not RH.
