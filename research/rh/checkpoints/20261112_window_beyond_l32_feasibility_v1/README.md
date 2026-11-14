# Beyond the window 3/2: feasibility of 8/5, 25/16, 31/20 and 49/32 (2026-11-12)

Evidence kind: `numerical`. The row side uses the lab's exact mirror (`gen_rr_k.py`, untrusted
Python, exact rational arithmetic). The trace side uses the float mirror of the cell bound
(`trace_cells_k.py`). No theorem. RH status: OPEN.

The window `2r ≤ 3/2` is proved (`../20261112_window_l32_v1/`), so RH is equivalent to the sign on
the windows `L > 3/4`. These runs ask how far the same route goes with `M = 4`, that is
`LT < log 5 ≈ 1.6094`.

## Tools

Both from `../20261110_window_l32_feasibility_v1/`, unchanged:
`python3 make_gen_rr_k.py ../20261031_window_l118/gen_rr_lt.py > gen_rr_k.py`
(sha256 `258027887a4797980f4419ed915ffdaaaf88388c5eafe848f774139d91a25c07`) and `trace_cells_k.py`.
Recalibration: `gen_rr_k.py 3/2 700 1 66 5e-13 5e-11 4e-13 150 14 15` gives scaled `λ_min`
`4.20532e-9`, as in `CERT_FEASIBILITY_32.log`; `trace_cells_k.py 3/2 150 1.65 0 150,30,6,3` gives
`T = 2.9602`, as in `TRACE_FEASIBILITY_32.log`.

## Row check (`ROW_FEASIBILITY_85.log`)

Scaled `λ_min` of the check matrix; positive means the check passes. `T_τ = 15`, slack `10⁻¹⁵`
and boxes `5e-13 / 5e-11 / 4e-13` unless noted.

| LT | atoms (KK) | NP | ε | κ | scaled λ_min |
|---|---|---|---|---|---|
| 3/2 | 311 (156) | 900 | 1 | 66 | +8.88e-9 |
| 49/32 | 311 (156) | 900 | 1 | 66 | −1.83e-9 |
| 49/32 | 311 (156) | 1200 | 1 | 66 | +1.39e-9 |
| 49/32 | 311 (156) | 1200 | 7/5 | 66 | +1.74e-9 |
| 49/32 | 311 (156) | 1200 | 7/5 | 70 | +2.01e-9 |
| 49/32 | 311 (156) | 1500 | 7/5 | 66 | +2.75e-9 |
| 31/20 | 311 (156) | 900 | 1 | 66 | −3.14e-9 |
| 31/20 | 311 (156) | 1200 | 7/5 | 66 | −5.14e-10 |
| 31/20 | 311 (156) | 2000 | 7/5 | 66 | +6.82e-10 |
| 25/16 | 311 (156) | 900 | 1 | 66 | −4.97e-9 |
| 8/5 | 319 (160) | 900 | 1 | 60 / 66 / 72 | −1.43e-8 / −8.55e-9 / −6.31e-9 |
| 8/5 | 319 (160) | 1500 | 1 | 72 | −1.29e-9 |
| 8/5 | 319 (160) | 2000 | 7/5 | 72 | −4.09e-10 (`T_τ = 14`: −3.46e-10) |
| 8/5 | 319 (160) | 3000 | 7/5 | 72 | −4.81e-11 |
| 8/5 | 319 (160) | 4000 | 7/5 | 72 | +4.01e-11 |
| 8/5 | 349 (175) | 2000 | 7/5 | 72 | −4.07e-10 |

With the box radii of the 3/2 port (`5e-11 / 5e-10 / 4e-11`, slack `10⁻¹³`) at `49/32`:

| NP | ε | κ | K' | scaled λ_min |
|---|---|---|---|---|
| 1200 | 7/5 | 70 | 8.92e-9 | +1.26e-10 |
| 1500 | 7/5 | 66 | 8.41e-9 | +9.74e-10 |
| 2000 | 7/5 | 66 | 8.41e-9 | +1.60e-9 |
| 2000 | 7/5 | 70 | 8.92e-9 | +1.75e-9 |

Reading:

- The margin falls fast with `LT`: `+8.9e-9` at `3/2` and `−1.8e-9` at `49/32`, both at `NP = 900`.
- Rows outside the low block are what helps; `κ`, `ε`, more atoms (`KK = 175`) and a smaller far
  bound (`T_τ = 14`) move the margin little.
- `8/5` is positive only at `NP = 4000`, with `4e-11`, below the error budget of realistic boxes.
  It is not a practical next window on this route.
- `49/32` passes from `NP = 1200`, and with realistic boxes from `NP = 1500`; `NP = 2000` gives
  `1.6e-9`.

## Trace (`TRACE_FEASIBILITY_85.log`)

| LT | atoms (K) | layout | m | T | largest κ |
|---|---|---|---|---|---|
| 49/32 | 311 (156) | lab, 3123 cells | 1.65 | 2.874 | 72.1 |
| 49/32 | 319 (160) | lab, 3123 cells | 1.65 | 2.762 | 73.2 |
| 8/5 | 319 (160) | lab, 3123 cells | 1.65 | 2.992 | 74.2 |
| 8/5 | 349 (175) | lab, 3123 cells | 1.65 | 2.607 | 78.0 |

At `49/32` with `T = 3` written in (as at `3/2`): `(2π)² · (49/32) · (33/20 − 3/(2π)) ≈ 70.88`, so
`κ = 66` leaves room and `κ = 70` is tight. The slack covers `|t| < 620.1` and the cell bound needs
`b < 2πK/LT`, which is `640.1` at `K = 156`.

## Proposed next window

`2r ≤ 49/32`, frontier `49/64 = 0.765625`: `M = 4`, `LT = 49/32`, `m = 33/20`, 311 atoms
(`−155, …, 155`), `NP = 2000`, `ε = 7/5`, `κ = 66`, `T_τ = 15`, `T = 3`. The `τ` boxes are
needed for `k ≤ 2000` (900 at `3/2`), and the outside-row tables are about 2.5 times larger.
Not RH.
