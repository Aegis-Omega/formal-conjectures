# The next window, 2r ≤ 4/3: numerical feasibility (2026-10-26)

Status: numerics validated in Python; the trace side and the τ and diagonal boxes are in Lean
(see "Lean port status"), the row certificates are not. One window only. Not RH.

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

Not built yet:
- the projected low block at 4/3: the packed 139 × 139 certificate (`certR`, `certL`, `certI`,
  regenerated), the projected entries and their fast replay, the basis and low coercivity;
- the relative row certificate with κ = 52, NP = 200, and the Gram tail at 4/3;
- the full row table and the actual inputs;
- the join, the window theorem at 4/3, `window_le_two_thirds` and RH ↔ windows L > 2/3.
At 6/5 the packed and relative certificates are generated Lean files of 1–2 MB each and the
actual-input sources a 28 MB archive, so at 4/3 they have to be generated in CI from committed
generators.

Not RH.
