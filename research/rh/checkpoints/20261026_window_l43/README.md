# The next window, 2r ≤ 4/3 (numerics 2026-10-26, Lean 2026-10-28)

Status: proved in Lean. `CvSWindowL43V1.window_L43` closes the window 2r ≤ 4/3 and
`RHWindowL43ExhaustionV1.rh_iff_windows_above_two_thirds` reduces RH to the log windows L > 2/3
(see "Lean port status"). The windows L > 2/3 are not proved. One window only. Not RH.

`RHWindowL65ExhaustionV1.rh_iff_windows_above_three_fifths` reduces RH to the log windows
L > 3/5. The next window of the same route is the trial window LT = 4/3 (2r ≤ 4/3, frontier 2/3).
Below log 4 ≈ 1.386 no new prime power enters the symbol, so `ScertM 3` and the slack-only
Krein certificate keep their form; only the trial space, the row budget κ and the trace T change.

## Verdict

Both premises of `window_of_actual_rows_moment`, moved from 6/5 to 4/3, pass:

| premise | check | result at LT = 4/3 |
|---|---|---|
| relative row budget κ·Q_CvS − B ⪰ 0 (`hB`, rows `hfin`) | `validate_rows_gram_lt.py 4/3 400 1/2 44 0.0000003` | PASS, κ = 44, NP = 400; needs gap ≥ 0.8359 |
| trace bound and Krein gap (`hT`, `hk`) | `gen_lt.py 4/3 8/5 2` | T ≤ 3.3846 (1430 cells, m = 8/5), gap 1.0613 |

The gap 1.0613 exceeds the needed 0.8359, so `hk` holds with κ = 44:
(2π)²·(4/3)·(8/5 − T/(2π)) = 55.87 ≥ 44. With T rounded up to 17/5 it is 55.74.

LT = 13/10 also passes the row check (needs gap ≥ 0.8573; trace gives 1.0778 at m = 8/5).
LT = 11/8 is tighter: the float κ is 48.6 against an allowed 56.4, and the smallest eigenvalue
of Q_CvS drops to 8e-5.

## Controls at LT = 6/5

Each script reproduces the existing certificate before it is used at 4/3:
- `validate_rows_gram_lt.py 6/5 150 1 40 0.0000003` gives PASS, needs gap ≥ 0.844343, as
  `validate_rows_gram_l12.py` does with the certified boxes.
- `gen_lt.py 6/5 3/2 1` gives the 687-cell layout of `CvSTraceCertL65V1` and
  T = 3.6177128424…, below the 3625/1000 that certificate proves. Lean computes its own cells
  with `mkCell` and `hpLo`, so only the layout and the bound are compared.
- `kappa.py 6 5` matches the certified τ boxes for k ≤ 70 and the diagonal boxes to 3.4e-9.

## Scripts

- `kappa.py LT_num LT_den [NP] [TF]`: float model of κ(LT) (rows plus the exact Gram tail with
  |τ| ≤ TF beyond NP). It generalizes `tools/hfin_tail_l12.py`; the diagonal uses
  D(ω) = Re ψ′(1/4 + iω/2)/4 − Σ_k e^{−c_k LT} Re (c_k + iω)^{−2}, because `mp.nsum` misjudges
  the sign-changing series near c_k ≈ ω.
- `validate_rows_gram_lt.py LT NP eps kappa [dG]`: port of `tools/validate_rows_gram_l12.py`.
  τ_k and the diagonal come from mpmath at 40 digits (box radius 1e-25) instead of the Lean boxes;
  matrices are exact integers at scale 2^100 and the LDLᵀ runs at 80 digits.
- `gen_lt.py L m grid`: the generator of the K3e cell data (not in the repo) with L as a
  parameter (e^{−L/2} at 128 bits, h = 2π/L, 1 + L and L − 1 in place of 11/5 and 1/5).
  Exact rationals with outward rounding, the same Lipschitz sine enclosure as
  `CvSTauPrimeL12V1.sinPi_bounds`, cells refined by `grid`. The slack s uses the mpmath h₊
  plus 1e-6; a Lean certificate recomputes it from `hpLo`.
- `trace_cells.py`: the float version of the same bound, used for the sweep.

## Sweep (float and exact)

| LT | κ (NP = 400, eps = 1/2) | gap needed | trace T (m = 8/5, ×2 cells) | gap available |
|---|---|---|---|---|
| 6/5 | 36.8 at NP = 150 (certified 40) | 0.844 | 3.618 at m = 3/2, ×1 | 0.924 |
| 13/10 | 38.7 | 0.857 (validated, κ = 44) | 3.281 | 1.078 |
| 4/3 | 40.1 | 0.836 (validated, κ = 44) | 3.385 | 1.061 |
| 11/8 | 48.6 (float) | 0.895 | 3.524 | 1.039 |

## Row parameters for the Lean port: NP = 200, κ = 52

With the certified trace bound T = 7/2 of `CvSTraceCertL43V1`, `hk` allows
κ ≤ (2π)²·(4/3)·(8/5 − 7/(4π)) ≈ 54.9. NP = 150, the value used at 6/5, does not reach that
(float κ ≈ 57 at the best eps). NP = 200 does: `validate_rows_gram_lt.py 4/3 200 7/10 52 0.0000003`
gives PASS, robust to |dG| ≤ 3e-7, and needs a gap ≥ 0.9879. κ = 48 passes only without the
robustness margin. This needs 260 rows outside the low block (160 at 6/5, 660 at NP = 400). The
log is `VALIDATION_ROWS_NP200.log`.

## Lean port status

Kernel-checked, every listed name audited to `propext`, `Classical.choice`, `Quot.sound`
(`feshbach_lean_v1/tools/krein_trace_modules.json`, krein-ring job):
- trace and Krein premises: `CvSTraceCellL43V1`, `CvSTraceIntegralL43V1`, `CvSTraceCertL43V1`
  (1430 cells, m = 8/5, T = 7/2, `hk` with κ = 52);
- τ_k for 1 ≤ k ≤ 200 and every prime cutoff M ≥ 3: `CvSTauL43V1` (the source check, e^{−2/3}),
  `CvSTauL43DataV1` (k ≤ 70), `CvSTauPrimeL43V1` (prime part, `tau_mem`),
  `CvSTauR1SourceL43V1` and `CvSTauR1PrimeL43V1` (71 ≤ k ≤ 200, `tau_mem_R1`);
- |τ_n| ≤ 13 for |n| ≥ 71: `CvSTauFarL43V1`;
- the diagonal `cvsEntry M (4/3) n n`, n ≤ 70: `CvSDiagL43V1`.
The data come from `tools/gen_tau43.py`, `gen_tau_prime43.py`, `gen_tau_r1_43.py` and
`gen_diag43.py`. Each is a port of the 6/5 generator; at 6/5 the originals reproduce the committed
data exactly. Every 4/3 box was also compared with mpmath at 30 digits.

The row side, the window and the exhaustion join (2026-10-28). The relative row certificate is
built directly in the 139 atom coordinates against `Q_CvS`, so the projected low block, the full
row table and the actual inputs of the 6/5 route are not needed (`Q_CvS ≥ 0` follows from
`Brow ≤ 52 Q_CvS` and `Brow ≥ 0`). Modules in `feshbach_lean_v1`:
- `CvSRelRowAlgebraV1`, `CvSRelRowHarmV1`: Cauchy–Schwarz and Schur tests, row sums of
  1/|x − m| through the integer harmonic table `hupN`, `Int./` rounding;
- `CvSRelRowDataL43V1` (generated, every table recomputed by the kernel), `CvSRelRowCertL43V1`
  (generated packed factor), `CvSRelRowCheckL43V1`, `CvSRelRowPsdL43V1`, `CvSRelRowFormL43V1`:
  the 139 × 139 integer check matrix (scale 2^-488) is positive (`Pm_psd`, seven kernel chunks),
  which gives `midpoint_ge` for the midpoint kernel `Zt` minus the rank-two part;
- `CvSRelRowBoxL43V1`, `CvSRelRowErrL43V1`, `CvSRelRowQL43V1`: τ and diagonal boxes as real
  bounds, `|E − Et/2^128|` row sums ≤ `RE`, and `Q_CvS ≥ Re⟨â, Ê â⟩ − ε_Q |â|²`;
- `CvSRelRowKtL43V1`, `CvSRelRowOutL43V1`: the rows 70 < |m| ≤ 200 through the kernel
  `K̂ = Σ_m ŵ ŵ'` (partial fractions, `Kt_err`);
- `CvSRelRowTailL43V1`: the Gram tail with `gramUp 200` positive on F (`G_psd`, `psd_split`);
- `CvSRelRowInvL43V1`, `CvSRelRowInL43V1`: the rows |m| ≤ 70; the atom coefficients `lam` invert
  the second differences, and the residual is the rank-two vector α₀ g̃₀ + α₁ g̃₁;
- `CvSRelRowHBL43V1`: `hB`, `Brow M c ≤ 52 Q_CvS M (4/3) c` for M ≥ 3, NP = 200, T = 13,
  ε = 7/10, with `K' = 52 ε_Q + ε_in + ε_out + ε_T ≈ 7.2164e-6 ≤ Kq/2^64 ≈ 7.2357e-6` (`K_ok`).

In this directory:
- `CvSWindowL43V1`: `window_L43`, from `window_of_certificate_gram_moment` with M = 3, L = 2,
  LT = 4/3, m = 8/5, `trace_premises_L43` and `hB`;
- `RHWindowL43ExhaustionV1`: `window_le_two_thirds`,
  `final_sign_iff_windows_above_two_thirds`, `rh_iff_windows_above_two_thirds`.

Data pipeline (untrusted; the kernel rechecks every table): `tools/gen_rr43.py` (reads the
committed τ and diagonal boxes through `tools/boxes43.py`), `tools/cert43.py 64`,
`tools/emit_rr43.py OUTDIR`. Its two outputs, `CvSRelRowDataL43V1.lean` (79 KB) and
`CvSRelRowCertL43V1.lean` (132 KB), are not committed: `rh-cvs-window-l65-source.yml` generates
them with mpmath 1.3.0, checks their sha256 against the local run that produced the proofs,
compiles the whole DAG of both windows from source and audits the axioms.

Not RH.
