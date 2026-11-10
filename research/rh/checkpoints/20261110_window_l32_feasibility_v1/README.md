# Feasibility of the window 2r ≤ 3/2 (float model, 2026-11-10)

Evidence kind: `numerical` (untrusted float model). No theorem. RH status: OPEN.

## Question

`window_L118` proves the window `2r ≤ 11/8`, just below `log 4`. Can
`window_of_certificate_gram_moment` be instantiated beyond `log 4`, where the prime power 4 enters
(`M = 4`, `LT < Real.log 5`)? `ScertM`, `tau` and `cvsEntry` are already defined for every `M`.

## Model (`feas.py`)

- Row side: the model of `../20261026_window_l43/kappa.py`, with the number of atoms as a
  parameter (frequencies `|k| ≤ K`, `2K − 1` atoms) and atom columns scaled to unit norm. Prime
  powers `n < e^LT` enter with weight `2Λ(n)/√n`; `n = 4` has weight `log 2`.
- Trace side: `T(m) = ∫ s(t) · dist²(e_t, V) dt` with `s(t) = max(0, m + W − h₊(t))`, `W` the
  worst-case prime sum (as `mkCell` in the trace certificates) and `V` the atoms and `exp(±x/2)`.
- Feasible when `m − T/(2π) ≥ κ / ((2π)² LT)`.

## Calibration on the proved window 11/8

139 atoms, `NP = 250`: the model gives `κ = 54.14` at `ε = 0.7`, the same value as `kappa.py`;
the proved certificate uses `κ = 58`. The model gives `T = 1.44` at `m = 33/20`; the certificate
proves `T ≤ 7/2`. So the certified `T` is about 2.43 times the model value. The last column below
applies that factor.

## Results (`FEASIBILITY_32.log`)

| LT | atoms (K) | NP | λ_min of Q, unit atoms | gap needed | model gap | gap with T × 2.43 |
|---|---|---|---|---|---|---|
| 11/8 | 139 (70) | 250 | 3.26e-7 | 0.998 | 1.421 (m = 1.65) | 1.093 (proved) |
| 3/2 | 299 (150) | 500 | 1.78e-9 | 0.887 | 1.411 (m = 1.65) | 1.068 |
| 3/2 | 349 (175) | 600 | 1.77e-9 | 0.819 | 1.461 (m = 1.65) | 1.190 |
| 3/2 | 399 (200) | 700 | 1.77e-9 | 0.762 | 1.606 (m = 1.80) | 1.329 |
| 8/5 | 329 (165) | 560 | 1.45e-11 | 1.051 | 1.423 (m = 1.65) | 1.099 |

## Reading

- The window `3/2` looks feasible with about 299 atoms: gap needed 0.887 against about 1.07 after
  the calibration factor. That is more room than the window 11/8 had.
- The slack must cover `|t| < 2π · exp(m + W) ≈ 620` (it was 310 at 11/8), so the atoms must reach
  `K ≥ 620 · LT / (2π) ≈ 148`. With too few atoms the trace term explodes: see `m = 1.80` at 11/8
  in the log, where the slack passes the atom range and `T` jumps from 1.4 to 7.6.
- The minimum eigenvalue of the unit-atom low block drops from 3.3e-7 to 1.8e-9, about 180 times,
  and does not improve with more atoms. Boxes for `τ` and the diagonal and the fixed-point scale
  must tighten by about that factor. At 11/8 the scale `2^64` passes with `K' ≈ 1.2961e-6` against
  `1.2974e-6`, so expect a scale near `2^72` or more and box radii near `5e-11`.
- `max |τ_k|` beyond the low block is 13.35 in the model; the far bound `|τ| ≤ 13` used at 11/8
  has to become 14.
- The window `8/5` is marginal (1.05 needed against about 1.10) with `λ_min ≈ 1.4e-11`. It is not
  a first target.

## Proposed parameters for a port

`M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`, atoms centred at `−149, …, 149`, `NP = 500`,
`T_τ = 14`, `ε = 1/2`, `κ` near 53 to 56, trace cells on `|t| < 620` with the weight of `n = 4`
added to the slack. The module list is that of the 11/8 port
(`../20261031_window_l118/README.md`).

## Why this route does not exhaust the windows

The slack cutoff is `t* = 2π · exp(m + W(LT))` with `W(LT) = ∑_{n < e^LT} 2Λ(n)/√n`, and the
atom count is about `t* · LT / π`. For `LT = 2` (`n ≤ 7`, `W ≈ 5.85`) that is about 7,200 atoms.
`W` grows like `4 e^{LT/2}`, so the atom count grows doubly exponentially in `LT`, while the
low-block minimum eigenvalue falls (3.3e-7, 1.8e-9, 1.4e-11 at 11/8, 3/2, 8/5). A proved window
moves the frontier of `rh_iff_windows_above_eleven_sixteenths`. No finite list of windows gives RH.

## Reproduce

    python3 -m venv venv && ./venv/bin/pip install mpmath numpy
    ./venv/bin/python feas.py 3/2 150 500 14 1.5,1.65

Arguments: `LT K NP TF m1,m2,...`. Each run takes under a minute.
