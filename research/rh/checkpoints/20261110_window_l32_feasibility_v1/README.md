# Feasibility of the window 2r ≤ 3/2 (2026-11-10)

Evidence kind: `numerical`. The row side uses the lab's exact mirror (untrusted Python, exact
rational arithmetic). The trace side uses a float mirror of the lab's cell bound, calibrated on
the proved window. No theorem. RH status: OPEN.

Both sides close in these mirrors at `LT = 3/2` with `M = 4` and 299 atoms.

## Question

`window_L118` proves the window `2r ≤ 11/8`, just below `log 4`. Can
`window_of_certificate_gram_moment` be instantiated beyond `log 4`, where the prime power 4 enters
(`M = 4`, `LT < Real.log 5`)? `ScertM`, `tau` and `cvsEntry` are already defined for every `M`.
The theorem needs `m − T/(2π) ≥ κ / ((2π)² LT)`, where `κ` comes from the row certificate and `T`
from the trace certificate.

## Row certificate: exact mirror (`CERT_FEASIBILITY_32.log`)

`make_gen_rr_k.py` derives `gen_rr_k.py` from `../20261031_window_l118/gen_rr_lt.py`: the atom
count (frequencies `|k| ≤ KK`), the far bound `T_τ` and the fixed slack of `epsIn` become
parameters, and the prime power 4 (weight `log 2`) enters for `LT ≥ log 4`. With `KK = 70` at
`LT = 11/8` it reproduces the log line of the 11/8 port exactly (`K' 1.2892e-06`, scaled
`λ_min 4.98641e-7`).

At `LT = 3/2`, `KK = 150` (299 atoms), `T_τ = 14`, boxes `5e-13 / 5e-11 / 4e-13` unless noted:

| NP | ε | κ | scaled λ_min of the check matrix |
|---|---|---|---|
| 500 | 1/2 | 56 (boxes 5e-11 / 5e-10 / 4e-11) | −4.43e-8 |
| 500 | 1/2 | 56, 60, 64 | −4.24e-8, −3.96e-8, −3.72e-8 |
| 500 | 7/10 | 60 | −2.72e-8 |
| 500 | 1 | 60 | −1.89e-8 |
| 700 | 7/10 | 60 | +1.84e-10 |
| 700 | 1 | 66 | +4.21e-9 |
| 800 | 1 | 66 | +7.58e-9 |
| 900 | 1 | 60 | +1.02e-8 |
| 900 | 1 | 66 | +9.64e-9 |
| 1000 | 1 | 62 | +9.96e-9 |
| 1000 | 7/5 | 62 | +1.06e-8 |

- Tightening the boxes does not help at `NP = 500`; the tail does. The check passes from
  `NP = 700` and the margin settles near `1e-8` from `NP = 900`.
- With boxes near `5e-13` the error budget is `K' ≈ 7e-11`, well below the margin.
- The LDL certificate of `tools/cert43.py` closes on the matrix `NP = 1000, ε = 7/5, κ = 62` at
  scales `2^80` and `2^88` (`eta < eps`, see `CERT43_NOTES.md`). The scale `2^64` of the 11/8 port
  is not enough here.

## Trace certificate: mirror of the cell bound (`trace_cells_k.py`, `TRACE_FEASIBILITY_32.log`)

`trace_cells_k.py` evaluates the cell bound of `CvSTraceCellL118V1` and the total of
`CvSTraceIntegralL118V1` in floats, with the window, the atom range and the prime powers as
parameters:

    TD = (1 + eps) Aup + (1 + 1/eps) G2 (tb0 + tb1),   T = ∑ 2 (b − a) s TD,
    s = max(0, m + W − h₊(a)),   Aup = (2 − 2 cl) / LT · tail,

with the Lipschitz enclosure of `sinPiLo` / `sinPiHi` (value at the left end, plus or minus the
angular width of the cell). The constants `19/8` and `3/8` of the 11/8 module are `1 + LT` and
`LT − 1`; the 4/3 module has `7/3` and `1/3`.

Calibration: on the 2205 cells of the 11/8 port the mirror gives the segment sums
`0.9537 0.5286 0.9067 0.9580`, total `3.3471`. The kernel-checked chunk totals of
`cert118_totals.json` give `0.9538 0.5287 0.9068 0.9581`, total `3.3473`.

At `LT = 3/2`, `M = 4` (`W = 2.9420`), `m = 33/20`:

| atoms (K) | cells | T | m − T/(2π) | largest κ allowed |
|---|---|---|---|---|
| 139 (70) at 11/8, proved | 2205, lab layout | 3.347 | 1.117 | 60.7 (the port uses 58) |
| 299 (150) | 3123, lab layout | 2.960 | 1.179 | 69.8 |
| 299 (150) | 8292, widths 1/12 above t = 20 | 2.512 | 1.250 | 74.0 |
| 349 (175) | 8292, widths 1/12 above t = 20 | 2.028 | 1.327 | 78.6 |

The row check needs `κ = 60` (or 66 with fewer rows). With 299 atoms and the lab layout the trace
allows `69.8`, about 16 percent of room; the window 11/8 had about 4.5 percent. The slack must
cover `|t| < 2π · exp(m + W) ≈ 620` and the cell bound needs `b < 2π K / LT ≈ 628`, which is why
`K = 150` is the smallest convenient atom range at `m = 33/20`.

The mirror has no outward rounding and is not a certificate. The Lean trace modules have the
constants of 11/8 written in and have to be ported.

## Proposed parameters for a port

`M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`, atoms centred at `−149, …, 149`, `T_τ = 14`.

- Rows: `NP = 900`, `ε = 1`, `κ = 60` (margin `1.0e-8`), or `NP = 700`, `ε = 1`, `κ = 66`
  (margin `4.2e-9`, fewer `τ` boxes). Boxes near `5e-13` for `τ_k` with `k ≤ 150` and for the
  diagonal, near `5e-11` for the rows above. LDL scale `2^80` or more.
- Trace: 3123 cells of the lab layout on `|t| < 621`, slack with the weight of `n = 4` added,
  `T = 3` (`2.960` in the mirror), which gives `(2π)² · (3/2) · (33/20 − 3/(2π)) ≈ 69.4`.

The module list is that of the 11/8 port (`../20261031_window_l118/README.md`). Compared with
11/8: about twice the atoms, three to four times the rows, 1.4 times the trace cells, boxes about
20,000 times tighter, and a row margin about 50 times smaller.

## What changed during the day

The first version proposed `NP = 500` and `κ` near 53 to 56 from the float row model of `feas.py`
(the model of `kappa.py` with the atom count as a parameter). The exact mirror refutes those
values. The same gap between the float row model and the exact mirror is already visible at 11/8
for `ε = 1/2` in `../20261031_window_l118/FEASIBILITY_118.log`. Use the exact mirror for row
parameters. The first trace estimate (`feas.py`, about 5 percent of room) was too pessimistic;
`trace_cells_k.py` replaces it. `feas.py` remains useful for the size of the low-block minimum
eigenvalue (3.3e-7, 1.8e-9, 1.4e-11 at 11/8, 3/2, 8/5).

## Why this route does not exhaust the windows

The slack cutoff is `t* = 2π · exp(m + W(LT))` with `W(LT) = ∑_{n < e^LT} 2Λ(n)/√n`, and the
atom count is about `t* · LT / π`. For `LT = 2` (`n ≤ 7`, `W ≈ 5.85`) that is about 7,200 atoms.
`W` grows like `4 e^{LT/2}`, so the atom count grows doubly exponentially in `LT`, while the
low-block minimum eigenvalue falls. A proved window moves the frontier of
`rh_iff_windows_above_eleven_sixteenths`. No finite list of windows gives RH.

## Reproduce

    python3 -m venv venv && ./venv/bin/pip install mpmath numpy
    ./venv/bin/python make_gen_rr_k.py ../20261031_window_l118/gen_rr_lt.py > gen_rr_k.py
    ./venv/bin/python gen_rr_k.py 3/2 900 1 60 5e-13 5e-11 4e-13 150 14 15
    ./venv/bin/python rescale_pkl.py
    ./venv/bin/python ../../feshbach_lean_v1/tools/cert43.py 80
    ./venv/bin/python check_cert_pkl.py cert43_80.pkl
    ./venv/bin/python trace_cells_k.py 11/8 70 1.65 315
    ./venv/bin/python trace_cells_k.py 3/2 150 1.65

`gen_rr_k.py` arguments: `LT NP EPS KAPPA RHO_LOW RHO_HIGH RHO_DIAG KK [TF] [SLACK_EXP]`. A run at
`KK = 150` takes about a minute, `cert43.py` about a minute and a half, `trace_cells_k.py` a few
seconds.
