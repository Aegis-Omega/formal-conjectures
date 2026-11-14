# Window 3/2 port — `τ_k`, `k = 1, …, 900`, for every prime cutoff `M ≥ 4`

Date: 2026-11-11. Status: **kernel-checked locally**, default trust and `--trust=0`. Not run in CI.
**RH remains OPEN**; `window_L32` is not proved.

## Result

```lean
theorem AEGIS.CvSTauL32AllV1.tau_mem_all {M : ℕ} (hM : 4 ≤ M) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 900) :
    ((tLoAll k : ℚ) : ℝ) ≤ tau M (3 / 2) (k : ℤ) ∧ tau M (3 / 2) (k : ℤ) ≤ ((tHiAll k : ℚ) : ℝ)
```

Box widths: at most `9.998·10⁻¹¹` for `k ≤ 150` and `9.997·10⁻¹⁰` for `150 < k ≤ 900`, i.e.
radius `5·10⁻¹¹` and `5·10⁻¹⁰`: the budget with which the exact row mirror passes at
`NP = 900`, `ε = 1`, `κ = 60` (scaled `λ_min 8.17·10⁻⁹`,
`../20261110_window_l32_feasibility_v1/ROW_BOXES_20261111.md`).

## How

`CvSTauFastL32V1.lean` (hand-written):

- **Integer head.** `CvSTauL32V1.tauCheck` sums the head `Σ_{j<J} 2ω(1 − e^{−c_j L})/(c_j² + ω²)` in
  rationals, about 3.5 ms per term in the kernel; this window needs `J` up to `9371`. Here the same
  head is summed in natural numbers: with `ω ∈ [a/D, b/D]` (`a = 4·⌊π⌋₂₀·k`, `D = 3·10²⁰`), term `j`
  is `⌊8 a N_j D / ((4j+1)² D² + 4 b²)⌋ / 2⁶⁴` with `N_j/2⁶⁴ ≤ 1 − e^{−c_j L}` (lower) and
  `(⌊8 b N'_j D / ((4j+1)² D² + 4 a²)⌋ + 1) / 2⁶⁴` with `1 − e^{−c_j L} ≤ N'_j/2⁶⁴` (upper).
  `NE_bounds` (one kernel check of 13 table entries against `CvSTauL32V1.E_bounds`), `h_bounds`
  (induction, `term_lo`/`term_hi` of `CvSTauL12V1`). About 15 times faster.
- **Source.** `srcCheck_sound` is the argument of `CvSTauL32V1.tauCheck_sound` with this head; the
  source bracket, the arctan tail and the `e^{−c_J L}` term are unchanged.
- **Prime part.** `primeSum_eq` (`M ≥ 4`): at `L = 3/2` the prime powers `2, 3, 4` contribute, with
  `ppw 3 = log 2`; `prime_bounds` via `CvSTauPrimeL12V1.sinPi_bounds`; `tau_eq`.
- **Check.** `tauF k J K lo hi` and `tauF_sound`: a passing check gives `lo ≤ τ_k ≤ hi` for every
  `M ≥ 4`.

Data: `build_tau32.py` writes `CvSTauL32K{1, 51, …, 851}V1.lean` (50 values of `k` each, batches
of five, `decide +kernel`) from the untrusted exact mirror `gen_tau32f.py`; `assemble_tau32.py`
writes `CvSTauL32AllV1.lean`. The mirror cross-checks `τ_k` against mpmath through
`Σ_j 2ω/(c_j² + ω²) = Im ψ(1/4 + iω/2)` (inside the box at `k = 1, 2, 150, 151, 900`). The
generated modules (137 kB) are not committed; `generated.sha256` lists them.

## Replay

```
for s in $(seq 1 50 851); do python3 build_tau32.py $s $((s + 49)) .; done
python3 assemble_tau32.py .
lean CvSTauFastL32V1.lean; lean CvSTauL32K1V1.lean; …; lean CvSTauL32AllV1.lean
```
`build_tau32.py` reads the license header from `../20261111_window_l32_diagonal_v1/CvSNodeL32V1.lean`
(copy it next to the scripts). Dependencies: lab modules on this branch, `CvSExpL32V1`,
`CvSTraceM4SlackV1` (trace port checkpoint), `CvSTauL32V1`, `CvSNodeL32V1` (diagonal checkpoint).

## Receipt (local, 2026-11-11; Lean 4.33.1, Mathlib `0df444a`)

| Module | default trust | `--trust=0` |
|---|---|---|
| `CvSTauFastL32V1` | exit 0, 0 errors, 0 sorry | exit 0, 0 errors, 0 sorry (14 s) |
| `CvSTauL32K1V1` … `CvSTauL32K851V1` (18) | all exit 0, 0 errors, 0 sorry (79–153 s each) | all exit 0, 0 errors, 0 sorry (78–138 s each) |
| `CvSTauL32AllV1` | exit 0, 0 errors, 0 sorry | exit 0, 0 errors, 0 sorry (13 s) |

```
'AEGIS.CvSTauFastL32V1.NE_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFastL32V1.h_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFastL32V1.srcCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFastL32V1.primeSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFastL32V1.prime_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFastL32V1.tauF_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauL32AllV1.tau_mem_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Each data module's `tau_mem` reports the same three axioms. Evidence kind: `lean_kernel` (local).

## Remaining for `window_L32`

The 299×299 row certificate (`NP = 900`, `ε = 1`, `κ = 60`; LDL scale `2^80` or more, and the
check `eta < eps` on its output), the window theorem `window_L32`, and the exhaustion step with
frontier `3/4`. Negative `k` follow from `CvSTauPrimeL12V1.tau_neg`.
