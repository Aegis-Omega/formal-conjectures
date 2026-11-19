# A second-order tail for the `τ_k` source sums: the head length no longer grows with `k`

Date: 2026-11-14. Evidence kind: `lean_kernel` (local) for the three modules here and the two generated data modules. Nothing is promoted.
**RH remains OPEN.**

## What was slow

Every `τ_k` check (`CvSTauL*V1.tauCheck`, `CvSTauFastL*V1.tauF`) encloses the source sum
`Σ_j 2ω(1 − e^{−c_j L})/(c_j² + ω²)` (`c_j = 2j + 1/2`, `ω = 2πk/L`) by a head `j < J` and
`CvSArctanTailV1.tail_bracket`. That bracket telescopes `arctan(ω/(c−1)) − arctan(ω/(c+1))`. It loses
`(ω/3)(c_J − 1)⁻³` below and needs `c_J² ≥ ω²/3 + 3` above, so `J` grows with `k`. At `L = 8/5`
(`gen_tau85f.pickJ`) the head has `J = 37 307 … 42 564` terms for `k = 101 … 150` and about `31 400` at
`k = 4000`. The 79 logged `τ` modules of the 8/5 build took 5.85 h. The 13/8 feasibility checkpoint
(`../20261114_window_l138_feasibility_v1/`) put `τ` to `NP = 8000` at about 20 h.

## The second-order tail (`CvSArctanTail2V1`)

The telescoped function carries the Euler–Maclaurin term `f′/12`:

  `phi2 ω c = arctan(ω/c) − cω/(3(c² + ω²)²)`.

* `step2_bounds`: `|phi2 ω (c−1) − phi2 ω (c+1) − 2ω/(c²+ω²)| ≤ 8ω/(c²+ω²)³` for `c ≥ 2`, `ω ≥ 1`.
  With `v = 2ω/(c²+ω²−1)`, `v − v³/3 ≤ arctan v ≤ v − v³/3 + v⁵/5`. The rational rest is
  `−2ω N(c², ω²)/(3 R E³ P²)` (`step_rational_eq`, `N` of degree 5 in `X = c²`, `Y = ω²`). Both sides
  of the bound, multiplied out, are polynomials in `X − 4`, `Y − 1` with nonnegative integer coefficients:
  `loQ` has 36 terms and `hiQ` has 55. `positivity` proves them after lifting `X − 4`, `Y − 1` to `ℝ≥0`.
  The constant 8 is the first of `14/3, 5, 6, 8` for which every coefficient is nonnegative
  (`step_error_ktest.py`). Numerically the ratio `|δ|(c²+ω²)³/ω` stays below `14/3`, reached for `c ≫ ω`
  (`step_error_symbolic.py`).
* `inv_sq_le_step`: `ω/(c²+ω²) ≤ (5/8)(arctan(ω/(c−1)) − arctan(ω/(c+1)))` for `c ≥ 2`, `ω ≥ 1`.
* `tail2_bracket`: the step errors telescope against that majorant,

  `|Σ' j, 2ω/(c_j²+ω²) − phi2 ω (c₀−1)| ≤ 5 arctan(ω/(c₀−1)) / (c₀²+ω²)²`,

  for `c_j = c₀ + 2j`, `c₀ ≥ 2` and `ω ≥ 1`. **There is no condition between `c₀` and `ω`.**

`CvSTauSource2V1.source_bracket2` puts this into the source integral:
`H + P − ε − 2e^{−c_J L}A ≤ (∫ h₊ S_k)/π ≤ H + P + ε`, where `P = phi2 ω (c_J − 1)`,
`A = arctan(ω/(c_J − 1))` and `ε = 5A/(c_J² + ω²)²`. The same module evaluates the arctan of a rational on
either side of `1` (`atLo`, `atHi`, `at_bounds`, with `arctan x = π/2 − arctan(1/x)` for `x > 1`).
`CvSTauFast2L85V1.tauF2` is the kernel check at `L = 8/5`. It keeps the integer head and the prime part of
`CvSTauFastL85V1` and gives outward rational bounds for the `phi2` correction and for `ε`. `tauF2_sound`
encloses `τ_k` for every prime cutoff `M ≥ 4`.

## Test at `L = 8/5`

`gen_tau2_85.py` is an exact untrusted mirror of `tauF2`. It picks `J` from `5(π/2)/(c_J² + ω²)² ≤ tgt/4`
and keeps `ω/(c_J − 1)` outside `[0.6, 5/3]`. Every box is compared with an mpmath value of `τ_k`
(`Im ψ(1/4 + iω/2)` minus the exponential part, plus the prime part). The targets `tgt` are those of
`gen_tau85f.tgt_of`.

| `k` | `J` before | `J` now | width before | width now | kernel time before | now |
|---|---|---|---|---|---|---|
| 101 … 150 | 37 307 … 42 564 | 850 … 878 | ≤ 1.013·10⁻¹² | ≤ 1.002·10⁻¹² | `K101` unlogged; `K51` 537 s, `K151` 165 s | 26 s |
| 3951 … 4000 | about 31 400 | 12 | target 3·10⁻⁹ | ≤ 3.2·10⁻¹⁴ | 588 s | 18 s |

Above `k ≈ 160` the head is 12 terms and the boxes come out near `3·10⁻¹⁴`, far inside the target.

## What it changes for 13/8 and 9/5

The τ part of `13/8` at `NP = 8000` (about 160 modules) or `9/5` at `NP = 16000` now costs about 20 s per
50 values of `k`, so under an hour, where it used to be about 20 h or about 80 h. It also gives tight high-`k`
boxes for free. The 13/8 row mirror runs with all τ boxes at `5·10⁻¹⁴` are recorded below
(`gen_rr_k5.py` of `../20261112_window_l85_v1/`). The rest of 13/8 is a separate port: the trace cells with
the exact cosines and the boundary terms, `M = 5`, the diagonal and the rows.

## The 13/8 rows with tight τ boxes everywhere (`ROW_RUNS_TIGHT.log`)

`gen_rr_k5.py 13/8 NP 7/5 63 ρ_low ρ_high ρ_diag 360 19 13`, the first two rows from
`../20261114_window_l138_feasibility_v1/ROW_RUNS.log`:

| `NP` | τ boxes `k ≤ 360` / above / diagonal | scaled `λ_min` |
|---|---|---|
| 4000 | `5·10⁻¹⁴` / `5·10⁻¹⁰` / `3·10⁻¹⁴` | `−1.24·10⁻¹⁰` |
| 4000 | `5·10⁻¹⁴` / `5·10⁻¹⁴` / `3·10⁻¹⁴` | `−1.2265·10⁻¹⁰` |
| 8000 | `5·10⁻¹⁴` / `5·10⁻¹⁰` / `3·10⁻¹⁴` | `+2.53·10⁻¹¹` |
| 8000 | `5·10⁻¹⁴` / `5·10⁻¹⁴` / `3·10⁻¹⁴` | **`+2.673·10⁻¹¹`** |

The high boxes do not limit `NP = 4000`: the bottom mode there is the row tail, as the feasibility
checkpoint found. `NP = 8000` stays. With this tail its τ boxes are tight at no extra cost.

## Receipt (local; Lean 4.33.1, Mathlib `0df444a`)

The imports are `CvSArctanTailV1` and `CvSTauSourceV1` from `research/rh/feshbach_lean_v1/` and
`CvSTauFastL85V1` with its own imports, regenerated from `../20261112_window_l85_v1/`. Each of the
five modules compiles with default trust and with `--trust=0`: exit 0, no errors, no warnings, no
`sorry`. Every printed theorem reports `[propext, Classical.choice, Quot.sound]` (`AXIOMS_default.txt`,
`AXIOMS_trust0.txt`). The `--trust=0` times are 18 s, 13 s, 13 s, 27 s and 19 s.

| file | sha256 |
|---|---|
| `CvSArctanTail2V1.lean` | `3d0c0989cef9975d180b468aff8fe16edd7dd3b565d383372b2b614c570e8e32` |
| `CvSTau2L85K101V1.lean` | `01e596e11c830b61cef3798fa638402d96571b9bce0148acf9a1439a77b01fca` |
| `CvSTau2L85K3951V1.lean` | `e69b0076a3cc9d43c77693b0f3498a1781c572ab74e5b8e8eb82e8f1ed5be481` |
| `CvSTauFast2L85V1.lean` | `aa31c2077f8ed4b72817a27d969ff34c60105c8007cb36b7fba6d722e6915c3e` |
| `CvSTauSource2V1.lean` | `1c31f7f2f6ac05cbabd36c8b0219ae438ae9fd09aa4f61426dac33c16d951475` |
| `gen_tau2_85.py` | `5a77a39e30644e842d5c794af40157087b413e3b736fa2ef991240dc213a423c` |
| `step_error_ktest.py` | `30ae924679b48e52e285dc59296ca9c10a036ee87231bb84b3dda791c8c356ab` |
| `step_error_polys.py` | `936b8971e29a9152497029c313716d8bf71ff3f7e8f718e941beb9d3751ac686` |
| `step_error_symbolic.py` | `640b53ee698d2cf451617017407f41dfe5516ca00e9bc41c6d1d4e909f574496` |

## Files

* `CvSArctanTail2V1.lean`: `phi2`, `step2_bounds`, `inv_sq_le_step` and `tail2_bracket`. It is generic and
  imports only Mathlib and `CvSArctanTailV1`.
* `CvSTauSource2V1.lean`: `source_bracket2`, generic in `L`, and `atLo`, `atHi`, `at_bounds`.
* `CvSTauFast2L85V1.lean`: `srcCheck2`, `tauF2` and their soundness at `L = 8/5`.
* `CvSTau2L85K101V1.lean`, `CvSTau2L85K3951V1.lean` (`tau_mem`) are not committed: `gen_tau2_85.py 101 150
  module` and `gen_tau2_85.py 3951 4000 module` write them byte for byte (sha256 in the table, checked by a
  second run).
* `gen_tau2_85.py`: the mirror and module writer. It imports `gen_tau85f.py` from the regenerated
  `scripts/` of `../20261112_window_l85_v1/` (sha256 `c9328868…`), so run it with that directory on
  `PYTHONPATH`.
* `ROW_RUNS_TIGHT.log`: the two row mirror runs above.
* `step_error_symbolic.py`: sympy derivation of `N`, a check of the identity and a numeric scan of
  `|δ|(c²+ω²)³/ω`.
* `step_error_ktest.py`: the identity check and the coefficient-sign test for `K ∈ {14/3, 5, 6, 8, …}`.
* `step_error_polys.py`: the Lean text of `loQ` and `hiQ` at `K = 8` and a random numeric check of
  `step2_bounds` (worst ratio 0.583 of the bound).
