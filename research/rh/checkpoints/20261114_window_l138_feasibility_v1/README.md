# The window 13/8 past log 5: the Krein boundary slot closes it in the mirrors

Date: 2026-11-14. Evidence kind: `float_mirror` (untrusted) plus one exact rational LDL on a synthetic-box
matrix. Nothing here is a Lean proof and nothing is promoted. **RH remains OPEN.**

## What was missing

Every window theorem so far (`CvSWindowL*V1.window_L*`, up to `8/5` in `../20261112_window_l85_v1/`) calls
`window_of_certificate_gram_moment` with `n := 0` (no hats `H`) and `k := 0` (no boundary terms `d`). Its slack
also uses `ScertM M t ≥ h₊(t) − Σ_q w_q⁺` (`CvSHplusBoundsV1.scertM_three_ge`, `CvSTraceM4SlackV1`), which puts
every prime cosine at its worst case. The slack is then `s = max(0, m + W − h₊)` up to `t* = 2π e^{m+W}`, and
`trace_cells_k.py` reproduces the Lean totals with exactly this slack (8/5: mirror `T = 2.8925`, Lean `2.89286`).
The prime `5` raises `W` from `2.942` to `4.382`, so past `log 5` that slack cannot work. That is why
`../20261112_window_l85_v1/` stops at `8/5` (`κ ≤ 36.9` at 13/8 with 721 atoms, row mirror `−4.97·10⁻⁹`).

The theorem already allows both slots (`CvSTraceV1.complement_bound`, `CvSKreinRoughV1.krein_slack_rough`). The
boundary terms `2 Re(d (it)^j e^{itL})` pair to zero with `|𝓕χ|²` for every `χ` supported in an interval shorter
than `L`. The theorem supplies such a `χ` through the factorization `G = χ'' − χ/4`, so any `j` is allowed.

## The trace with boundary terms (`krein_trace_lp.py`, `LP_RUNS.log`)

The LP minimizes the trace `T = Σ 2 dt s(t) TD(t)` itself, where `TD` is the `trace_cells_k.py` cell bound of
`dist²(e_t, atoms)`. Its variables are the slack `s ≥ 0` on a grid and four real boundary coefficients:

  `Wt(t)(S(t) − m) + 2(x₀ cos tL + x₁ t sin tL + x₂ t² cos tL + x₃ t³ sin tL) + Wt(t) s(t) ≥ 0`.

Here `S` is the exact symbol `h₊(t) − Σ_q a_q cos(t log q)`, `Wt = (t² + 1/4)²` and `L = LT + 1/100`. The boundary
part is even in `t`, as `S` and `Wt` are. In `d` form this is `d₀ = x₀, d₁ = −x₁, d₂ = −x₂, d₃ = x₃`, all real. No
hats are needed: 200 hats with `|a| ≤ 30` and no boundary terms reach about the same `κ` (96.3 at 8/5).
`κ = (2π)² LT (m − T/2π)` is the factor the row certificate multiplies the low form by (8/5 chain: 66).

| window | atoms | m | κ before (Lean slack) | κ, boundary terms (cell max on a 50× finer grid) |
|---|---|---|---|---|
| 8/5 | 311 | 1.6 | 66 (Lean cells) | 97.8 |
| 13/8 | 599 | 1.0 | — | 62.7 |
| 13/8 | 721 | 1.0 / 1.1 / 1.2 | 36.9 at m = 1.0 (`FEASIBILITY_85.log`) | 63.0 / 69.3 / 70.9 |
| 9/5 | 639 / 799 | 1.0 | — | 69.3 / 69.7 |

The coefficients stay small (`|x_j| ≤ 16`; 73 at 13/8, `m = 1.2`). The worst-case tail ratio
`Wt(h₊ − W − m) / Σ 2|x_j| t^j` past `t = 2400` is at least 478 (14.8 at 13/8, `m = 1.2`). With 311 atoms (`K = 156`) or 499
atoms, 13/8 is infeasible: `S < m` up to `t ≈ 1070` at `m = 1`, which is past the atom range `2πK/LT`.

## The rows (`ROW_RUNS.log`, `gen_rr_k5.py` of `../20261112_window_l85_v1/`)

| window | atoms | NP | κ | boxes (τ low / τ high / diag) | scaled λ_min |
|---|---|---|---|---|---|
| 13/8 | 721 | 4000 | 36 | 5e-13 / 5e-10 / 3e-13 | −4.97·10⁻⁹ |
| 13/8 | 721 | 4000 | 63 | same | −1.53·10⁻¹⁰ |
| 13/8 | 721 | 4000 | 69 | same | −1.51·10⁻¹⁰ |
| 13/8 | 721 | 4000 | 63 | 5e-14 / 5e-10 / 3e-14 | −1.24·10⁻¹⁰ |
| 13/8 | 721 | 8000 | 63 | 5e-13 / 5e-10 / 3e-13 | −4.05·10⁻¹² |
| 13/8 | 721 | 8000 | 69 | same | −1.99·10⁻¹² |
| 13/8 | 721 | 8000 | 63 | 5e-14 / 5e-10 / 3e-14 | **+2.53·10⁻¹¹** |
| 9/5 | 639 | 4000 | 70 | 5e-13 / 5e-10 / 3e-13 | −8.67·10⁻¹⁰ |
| 9/5 | 799 | 4000 | 70 | same | −8.72·10⁻¹⁰ |
| 9/5 | 639 | 8000 | 70 | same | −2.17·10⁻¹⁰ |

At `NP = 4000` the bottom mode is a row-tail mode: `κ` does not move it, and `NP` does. On the positive 13/8
matrix the exact LDL of `cert43.py` passes (shift 8 by `rescale_pkl.py`):
`q = 92`, `eps = 62713203237708276 > eta = 17188844928736694`, entries of 47 bits; `q = 96` also passes.
At 9/5 the deficit shrinks by about 4× per doubling of `NP`. Arb at `L = 1.8` used rows up to 16000
(`aegis_source_0c1477f/research/feshbach_arb_v2/README.md`), so 9/5 needs `NP ≥ 16000` here too.

## What a Lean port of 13/8 needs

The result would be the window `2r ≤ 13/8`, i.e. `L₀ = 13/16`, past `log 5 / 2 ≈ 0.8047`. None of it is built.

* **Trace.** Cells with the exact cosines, `cos(t log q) ≤ sinPiHi(…)` on `u = t log q / π` intervals. Rational
  bounds for `log 2` and `log 3` exist; `log 5` is new, and `log 4 = 2 log 2`. The cells also carry the four
  boundary terms, with `cos/sin(tL)` by `sinPi_bounds`. Add a tail lemma for `|t| ≥ TOP` via `hplus_ge_of_sq`,
  `L = 13/8 + 1/100`, `M = 5` (`13/8 < log 6`) and `m = 11/10`.
* **Rows.** `κ = 63`, `NP = 8000`, 721 atoms (`K = 360`). The τ boxes need width `≤ 10⁻¹³` for `k ≤ 360` and
  `10⁻⁹` above. The diagonal needs width `≤ 6·10⁻¹⁴` for `n ≤ 360`, which takes about `K = 1000` series terms
  (the 8/5 widths go as `K⁻⁴`). `|τ_n| ≤ 19` beyond `NP`, and the LDL runs at `q = 92` on 719 dimensions.
* **Cost.** `CvSTauFastL85V1.srcCheck` sums `J ≈ 7.85 k` head terms, because `CvSArctanTailV1.tail_bracket` has
  width `(ω/3)(c₀ − 1)⁻³`. So τ to 8000 at the present tail costs about 20 h of modules (8/5 to 4000: about
  6.5 h). A higher-order tail still needs `c₀ ≥ ω/√3`, about 7× fewer terms. A constant cost per `τ_k` needs a
  Stirling-type tail for `Im ψ`.

## Files

* `krein_trace_lp.py`: the LP mirror (scipy HiGHS, float, untrusted).
  `usage: krein_trace_lp.py LT K m1,m2,.. XMAX DT [NH] [HW] [|a| bound] [JD] [|x| bound]`.
* `LP_RUNS.log`: the runs in the first table.
* `ROW_RUNS.log`: the runs in the second table and the LDL.

The pickles are local and untrusted, and are not committed.
`../20261112_window_l85_v1/` (the 8/5 window, with `gen_rr_k5.py` and `FEASIBILITY_85.log`) is pushed when its
kernel build completes.
