# Window 3/2 port — the diagonal `cvsEntry M (3/2) n n`, `n = 0, …, 150`

Date: 2026-11-11. Status: **kernel-checked locally**, default trust and `--trust=0` (see Receipt).
Not run in CI. **RH remains OPEN**; `window_L32` is not proved.

## Result

```lean
theorem AEGIS.CvSDiagL32V1.diag_mem {M : ℕ} (hM : 4 ≤ M) {n : ℕ} (hn : n ≤ 150) :
    ((diagLo.getD n 0 : ℚ) : ℝ) ≤ cvsEntry M (3 / 2) n n ∧
      cvsEntry M (3 / 2) n n ≤ ((diagHi.getD n 0 : ℚ) : ℝ)
theorem AEGIS.CvSDiagL32V1.cvsEntry_diag_neg {M : ℕ} (hM : 4 ≤ M) (n : ℤ) :
    cvsEntry M (3 / 2) (-n) (-n) = cvsEntry M (3 / 2) n n
```

Every box has width at most `5.82·10⁻¹²` (radius `2.91·10⁻¹²`). The row check
(`../20261110_window_l32_feasibility_v1/ROW_BOXES_20261111.md`) passes with diagonal radius
`4·10⁻¹¹`, so these boxes are about 14 times tighter than required.

## What is new compared with the `11/8` diagonal

1. **Third prime power.** `log 4 = 2 log 2 ≈ 1.386 < 3/2`, so the prime power `4 = 2²` lies inside the
   window. `cvsEntry_diag_eq` (for `M ≥ 4`) has the extra term
   `− L · ppw 3 · (1 − 2 log 2 / L) · cos(ω · 2 log 2)` with `ppw 3 = log 2`
   (`CvSTraceM4SlackV1.ppw_three`). Nodes: `CvSNodeL32V1.node_three`, and `node_big` for `j + 1 ≥ 5`
   from `log 5 ≥ log(9/2) = 2 log 3 − log 2 > 3/2`.
2. **Precision.** The lab enclosure of `h₊` uses `K = 40` series terms (tail `1/(4 aK⁴) ≈ 6·10⁻⁹`),
   far too coarse for this window. `CvSHplusK300V1` re-runs the same proof with `K = 300`
   (`aK = 1199/2`, tail `≈ 1.9·10⁻¹²`).
3. **Memory.** One `decide +kernel` over all 151 entries exceeded 11 GB; the check is split into
   19 chunks of 8 (`diag_c0 … diag_c18`), assembled by `diag_ok`. Same statement, same data.

## Files

| File | Origin |
|---|---|
| `port_hplus.py` | derives `CvSHplusK300V1.lean` from lab `CvSDiagL12V1.lean` (`40 → 300`, `159/2 → 1199/2`), proofs unchanged |
| `port_tau_l32.py` | derives `CvSTauL32V1.lean` from lab `CvSTauL118V1.lean` (`11/8 → 3/2`), using `CvSExpL32V1.e34_bounds` |
| `CvSNodeL32V1.lean` | hand-written: `node_zero/one/two/three`, `node_big` at `L = 3/2` |
| `make_gen_diag32.py` | derives the untrusted exact-rational mirror `gen_diag32.py` from lab `tools/gen_diag118.py`; the mirror emits E tables and boxes and cross-checks five entries against mpmath (40 digits) |
| `port_diag_l32.py` | builds `CvSDiagL32V1.lean` from lab `CvSDiagL118V1.lean` + the hand-written third-term block (`cf4_bounds`, `cos4_eq_sin`, `P4_bounds`, `cvsEntry_diag_eq`) + the mirror's data |

The generated files are deterministic functions of the lab sources on this branch and of these
scripts; they are not committed here (about 70 kB of data), their SHA-256 are:

```
c4129b2fa4cabaec275d8408ae64ff9769fc3c8d1e04b595c81f46af6570eca9  CvSHplusK300V1.lean
ad084f37d73bfcfea827676ec1c98213bc38e90a6100d779ce530309e07b6edb  CvSTauL32V1.lean
008c8922b5471eb63d9a1ccfe5b7d52416d472f36686888c8930a33e61d65e9e  CvSNodeL32V1.lean
7e11315c729c3da40e9f031e733138b9216fe3f05b9659660894c351890b3be5  CvSDiagL32V1.lean
f9d86817f57f603dd32b74e9a9c27c973e2e795e560cb18c3be55d0c685ce625  gen_diag32.py
2f3cb2af606b7518758b5502592488bbef9a7dc736800c372d4bdc93ebeb6ba0  diag32_data.txt
```

Dependencies outside this directory: lab modules on this branch, and `CvSExpL32V1`,
`CvSTraceM4SlackV1` from `../20261110_window_l32_trace_port_v1/`.

## Replay

```
python3 port_hplus.py REPO . 300
python3 port_tau_l32.py REPO .
python3 make_gen_diag32.py REPO . && python3 gen_diag32.py 300 151 > diag32_data.txt
python3 port_diag_l32.py REPO . diag32_data.txt 300 151 8
lean CvSHplusK300V1.lean; lean CvSTauL32V1.lean; lean CvSNodeL32V1.lean; lean CvSDiagL32V1.lean
```
(with `LEAN_PATH` pointing at Mathlib and the compiled lab modules; Lean 4.33.1, Mathlib `0df444a`).

## Receipt (local, 2026-11-11)

| Module | default trust | `--trust=0` |
|---|---|---|
| `CvSHplusK300V1` | exit 0, 0 errors, 0 sorry (526 s, cold cache) | exit 0, 0 errors, 0 sorry (24 s) |
| `CvSTauL32V1` | exit 0, 0 errors, 0 sorry | exit 0, 0 errors, 0 sorry (20 s) |
| `CvSNodeL32V1` | exit 0, 0 errors, 0 sorry | exit 0, 0 errors, 0 sorry (7 s) |
| `CvSDiagL32V1` (all 151 entries) | exit 0, 0 errors, 0 sorry (2162 s, peak 6.3 GB) | exit 0, 0 errors, 0 sorry (2497 s) |

```
'AEGIS.CvSDiagL32V1.D_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.cvsEntry_diag_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.Pd_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.P4_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.diagCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.diagAll_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.diag_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSDiagL32V1.cvsEntry_diag_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`hplus_bounds`, `head_bounds`, `tauCheck_sound`, `node_three`, `node_big`: same three axioms.
The `--trust=0` replay covers these four modules; the lab modules they import were compiled at
default trust. Untrusted mirror: worst box width `5.819·10⁻¹²`; mpmath cross-check passes at
`n = 0, 1, 2, 75, 150`.

Evidence kind of `diag_mem`: `lean_kernel` (local build).

## Remaining for `window_L32`

The `τ_k` boxes are in `../20261111_window_l32_tau_v1/`. Still open: the 299×299 row certificate
(`NP = 900`, `ε = 1`, `κ = 60`, LDL scale `2^80` or more), the window theorem and the exhaustion
step.
