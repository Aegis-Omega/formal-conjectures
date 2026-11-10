# Feasibility of the window 2r ≤ 3/2 (2026-11-10)

Evidence kind: `numerical`. The row side uses the lab's exact mirror (untrusted Python, exact
rational arithmetic); the trace side is a float model. No theorem. RH status: OPEN.

This README replaces the first version of the same day, whose row parameters came from a float
model and were too optimistic (see "What changed").

## Question

`window_L118` proves the window `2r ≤ 11/8`, just below `log 4`. Can
`window_of_certificate_gram_moment` be instantiated beyond `log 4`, where the prime power 4 enters
(`M = 4`, `LT < Real.log 5`)? `ScertM`, `tau` and `cvsEntry` are already defined for every `M`.

## Row certificate: exact mirror (`CERT_FEASIBILITY_32.log`)

`make_gen_rr_k.py` derives `gen_rr_k.py` from `../20261031_window_l118/gen_rr_lt.py`: the atom
count (frequencies `|k| ≤ KK`), the far bound `T_τ` and the fixed slack of `epsIn` become
parameters, and the prime power 4 (weight `log 2`) enters for `LT ≥ log 4`. With `KK = 70` at
`LT = 11/8` it reproduces the log line of the 11/8 port exactly (`K' 1.2892e-06`, scaled
`λ_min 4.98641e-7`).

At `LT = 3/2`, `KK = 150` (299 atoms), `T_τ = 14`:

| NP | ε | κ | boxes (low / high / diagonal) | scaled λ_min of the check matrix |
|---|---|---|---|---|
| 500 | 1/2 | 56 | 5e-11 / 5e-10 / 4e-11 | −4.43e-8 |
| 500 | 1/2 | 56, 60, 64 | 5e-13 / 5e-11 / 4e-13 | −4.24e-8, −3.96e-8, −3.72e-8 |
| 500 | 7/10 | 60 | same | −2.72e-8 |
| 500 | 1 | 60 | same | −1.89e-8 |
| 700 | 7/10 | 60 | same | +1.84e-10 |
| 900 | 1 | 60 | same | +1.02e-8 |
| 1000 | 1 | 62 | same | +9.96e-9 |
| 1000 | 7/5 | 62 | same | +1.06e-8 |

- Tightening the boxes does not help at `NP = 500`; the tail does. The check passes from about
  `NP = 900`.
- With boxes near `5e-13` the error budget is `K' ≈ 7e-11`, well below the margin `1e-8`.
- The LDL certificate of `tools/cert43.py` closes on the last matrix at scales `2^80` and `2^88`
  (`ok True`). `cert43.py` assumes every diagonal of `P` is at least `1/2` in its units;
  `rescale_pkl.py` multiplies `P` by a power of 4 first. The scale `2^64` of the 11/8 port is not
  enough here.

## Trace side: float model only (`feas.py`, `FEASIBILITY_32.log`)

`T(m) = ∫ s(t) · dist²(e_t, V) dt` with `s(t) = max(0, m + W − h₊(t))`, `W` the worst-case prime
sum (as `mkCell`) and `V` the atoms and `exp(±x/2)`. Calibration at 11/8: the model gives
`T = 1.44` at `m = 33/20`, the certificate proves `T ≤ 7/2`, a factor 2.43.

| atoms (K) | model gap at m = 1.65 | gap with T × 2.43 |
|---|---|---|
| 299 (150) | 1.411 | 1.068 |
| 349 (175) | 1.461 | 1.190 |

The window theorem needs `m − T/(2π) ≥ κ / ((2π)² LT)`: 1.013 for `κ = 60`, 1.047 for `κ = 62`.
With 299 atoms that leaves about 5 percent on the calibrated estimate. This is not verified by
any exact computation. With 349 atoms there is more room, but the row check must then be redone
for `KK = 175`.

The slack must cover `|t| < 2π · exp(m + W) ≈ 620` (310 at 11/8), which is why the atoms must
reach `K ≥ 620 · LT / (2π) ≈ 148`.

## Proposed parameters for a port

`M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`, atoms centred at `−149, …, 149`, `NP = 900`, `ε = 1`,
`κ = 60`, `T_τ = 14`, boxes near `5e-13` for `τ_k` with `k ≤ 150` and for the diagonal, near
`5e-11` for `150 < k ≤ 900`, LDL scale `2^80` or more, trace cells on `|t| < 620` with the weight
of `n = 4` added to the slack. The module list is that of the 11/8 port
(`../20261031_window_l118/README.md`). Compared with 11/8: about twice the atoms, 3.6 times the
rows, boxes about 20,000 times tighter, and a margin about 50 times smaller.

## What changed

The first version proposed `NP = 500` and `κ` near 53 to 56 from the float row model of `feas.py`
(the model of `kappa.py` with the atom count as a parameter). The exact mirror refutes those
values. The same gap between the float row model and the exact mirror is already visible at 11/8
for `ε = 1/2` in `../20261031_window_l118/FEASIBILITY_118.log`. Use the exact mirror for row
parameters. `feas.py` remains useful for the trace estimate and for the size of the low-block
minimum eigenvalue (3.3e-7, 1.8e-9, 1.4e-11 at 11/8, 3/2, 8/5).

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
    ./venv/bin/python feas.py 3/2 150 500 14 1.5,1.65

`gen_rr_k.py` arguments: `LT NP EPS KAPPA RHO_LOW RHO_HIGH RHO_DIAG KK [TF] [SLACK_EXP]`. A run at
`KK = 150` takes about a minute, `cert43.py` about a minute and a half.
