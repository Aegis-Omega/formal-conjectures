# PRs #1–#97: what they compute, and the fixed-window Arb run of PR #7 at full precision

Date: 2026-11-13. Evidence kinds as marked; nothing is promoted. **RH remains OPEN.**

## Inventory

The 96 PR heads `#1–#95, #97` were fetched (`refs/pull/*/head`) and diffed against `main`
(`#92` and `#97` share no history with `main` and are taken whole). Their added or modified files
are 1455 distinct blobs; 1177 of them also occur at the head of `#92`. Of the other 278, 99 are
CI workflows and most of the rest are older versions of files that `#92` carries in a later form.
Leaving out workflows and tests, 49 paths are absent from `#92` altogether.

| lane | PRs | what is computed | kind | in `#92` |
|---|---|---|---|---|
| windows (`2r ≤ c`) | #12, #14, #17, #97 | `1/128` local sign, `6/5`, `4/3`, `11/8` (CvS row chain) | `lean_kernel` (replays of AEGIS-OMEGA commits) | later windows up to `31/20` |
| Krein window `2r < 21/20` | #53–#65 | 399-hat LP certificate, 1744 Taylor-model cells, `decide +kernel` | `lean_kernel` (local) | yes (`krein_L105_v1`) |
| translated packets | #18–#35, #42–#62, #83–#93 | nine/ten/eleven translates of one `1/128` packet, gap-9/10 prime bounds (`p = 673, 677, 1399`), fine diagonal `5671/3200`, mixed-defect bounds | `lean_kernel`, finite-dimensional or conditional on `hbudget` | yes (later versions) |
| Li criterion | #37, #39, #40 | reduction of the target to the paired Li sums | `lean_kernel`, reduction | no |
| Hardy point / critical line | #53 (archive), #53/#55/#76 | `Z(60) ∈ [38466, 38467]·2⁻¹⁶`, nine zeros | `certified_numerical` | critical line yes |
| fixed-window Galerkin | #7 | Formula 15 Weil matrix at `R = π, 2π`, Arb LDL | `certified_numerical` | no (this note) |
| CI, imports, snapshots | #49–#50, #63–#75, #77–#82, #94, #95 | — | — | partly |

`#43` (`RH_GLOBALIZATION_OBSTRUCTION_V1.md`, `RHCertifiedApproximationTrivialityV1.lean`) already
records why the translated-packet lane cannot close: the form `Σ z_i² − r(Σ z_i)²` is positive for
every coefficient vector iff `r·n ≤ 1`, so the admissible width shrinks as the family grows, and a
value-only approximation obligation is equivalent to the target itself.

## The exact Gram tail in the lab's Feshbach certificates

`../../aegis_source_0c1477f/research/feshbach_arb_v2/` bounds the rows `|n| > NP` by an order-`K` expansion of
`1/(n − m)` with weighted Cauchy–Schwarz; its remainder `Eco ~ (Amax + K2)² N^{2K}/(NP − N)^{2K+1}` is why the receipts
use `NP = 16000`. Those rows are `(Qv)_n = pole_n(v) + (τ_n Y_n − X_n)/π` with `Y_n = Σ v_m/(n − m)`,
`X_n = Σ τ_m v_m/(n − m)`, `|τ_n| ≤ K2`, and `Σ_{|n|>NP} |Y_n|²` is exactly the Hermitian form of
`Gup(m, m') = Σ_{|n|>NP} 1/((n − m)(n − m'))` (digamma and trigamma values; the kernel that `gramUp` of
`../../feshbach_lean_v1/CvSGramTailV1.lean` bounds and `gram_tail_le` uses, already kernel-checked there).
`make_exact_tail.py` derives that variant of `feshbach_blocks_arb.py` (four-term weighted Cauchy–Schwarz, no
remainder; the rest of the pipeline is unchanged). At `L = 1.6`, `N = 200` (Krein step and `trace_arb.json`
byte-identical to the receipt; `c_∞ = 1.32327472166`):

| tail | `NP` | `C_B` on the bottom Ritz vector | Schur (Arb) |
|---|---|---|---|
| order 4 (receipt) | 16000 | — | `μ = 4.5·10⁻¹²` |
| order 4 | 2000 | `3.0·10⁻⁸` (`Eco = 3.0·10⁻⁸`) | fails at `4.5·10⁻¹²` |
| order 4 | 4000 | `3.7·10⁻¹¹` | fails at `4.5·10⁻¹²` |
| exact, mixed weights | 2000 | `4.8·10⁻¹³` | fails at `4.5·10⁻¹²` |
| exact, weights `1/4` | 2000 | `7.2·10⁻¹³` | `μ = 4·10⁻¹²` (fails at `4.5·10⁻¹²`) |
| exact, mixed weights | 3000 | `4.3·10⁻¹³` | `μ = 4.5·10⁻¹²` |
| exact, mixed weights | 4000 | `4.1·10⁻¹³` | `μ = 4.5·10⁻¹²` |

The bottom Ritz value is `5.353·10⁻¹²` in every run, as in the `feshbach_arb_v2` table. Claim of the `NP = 3000` run
(interval arithmetic, not Lean): `Q(G) ≥ 4.5·10⁻¹² ‖G‖²` for every moment-zero `G` in `L²[0, 1.6]`. The receipt's
unformalised steps stand, with its tail bound replaced by the exact Gram form (the bound that `gram_tail_le` proves in
Lean for the pole-free rows of the lab's chain).

At `L = 1.8`, `N = 400` (prime powers 2, 3, 4, 5; Krein step and trace byte-identical to the receipt,
`c_∞ = 0.97991957971`; bottom Ritz value of `A11` `4.752·10⁻¹⁶` in every run):

| tail | `NP` | `C_B` on the bottom Ritz vector | Schur (Arb) |
|---|---|---|---|
| order 8, mixed weights (receipt) | 16000 | `3.34·10⁻¹⁷` | `μ = 4·10⁻¹⁷` (fails at `4.2·10⁻¹⁷`) |
| exact, mixed weights | 4000 | `3.82·10⁻¹⁷` | fails at `3·10⁻¹⁷` |
| exact, weights `1/4` | 4000 | `4.42·10⁻¹⁷` | fails at `2·10⁻¹⁷` |
| exact, weights `1/4` | 8000 | `3.70·10⁻¹⁷` | fails at `2·10⁻¹⁷` |
| exact, mixed weights | 8000 | `3.43·10⁻¹⁷` | `μ = 3·10⁻¹⁷` (fails at `4·10⁻¹⁷`) |

At `1.8` the order-8 remainder is already small at `NP = 16000`, so the exact tail saves half the rows for a quarter of
the margin; at `1.6` it saves about four fifths of them (3000 instead of 16000) at the same margin. Where the Schur
step fails, it fails in directions above the bottom one, and the split of the Cauchy–Schwarz budget decides it
(uniform and mixed weights differ by a factor of more than 1.5 in `μ`).

## PR #7 at full precision

`AegisRH/fixed_window_true_matrix_arb.py` of PR #7 (blob `89f5322c`, head `e9c3bff7`) evaluates the Weil matrix of
equation (15) on the window `R = π` (test functions on an interval of length `2π`, prime powers `m < e^{2π} ≈ 535`), with
the two moment conditions, and certifies `K_N + N⁻⁴ G_N > 0` by interval LDL. Its CI run (2026-09-23, run `35833288890`;
the artifact has expired, the log remains) certified the unshifted `K_N > 0` only up to `N = 10`, because the removable
singularity was cut at `η = 2⁻⁶⁴` and every entry carried a radius of about `10⁻¹⁹`. Rerun locally with the same script
(same pass/fail pattern at the CI parameters) and with more bits:

| `N` | dim | `λ_min(K_N)` (midpoints) | bits, `η` bits | unshifted `K_N > 0` |
|---|---|---|---|---|
| 3, 4, 5, 6 | 1–4 | `8.4·10⁻⁵`, `2.6·10⁻⁵`, `3.3·10⁻⁹`, `2.7·10⁻⁹` | 320, 64 (CI) | yes |
| 8 | 6 | `5.7·10⁻¹⁴` | 320, 64 (CI) | yes |
| 10 | 8 | `5.3·10⁻¹⁸` | 320, 64 (CI) | yes (rational Gershgorin) |
| 12 to 64 (CI) | 10–62 | below the entry radius `≈ 10⁻¹⁸` | 320, 64 (CI) | not decided |
| 12 | 10 | `2.3·10⁻²¹` | 640, 160 | yes |
| 16 | 14 | `6.8·10⁻²⁹` | 640, 160 | yes |
| 20 | 18 | `1.8·10⁻³⁵` | 640, 160 | yes |
| 24 | 22 | `4.4·10⁻⁴²` | 1024, 288 | yes |
| 32 | 30 | `4.1·10⁻⁵⁴` | 1024, 288 | yes |
| 40 | 38 | `7.3·10⁻⁶⁶` | 1600, 416 | yes |
| 48 | 46 | `4.8·10⁻⁷⁷` | 1600, 416 | yes |
| 64 | 62 | `6.5·10⁻⁹⁸` | 2400, 560 | yes |

(tolerance bits `2η` in the higher runs; `N = 64` took 6577 s.) The `R = 2π` part of the CI run (prime powers
`m < e^{4π}`; there the CI decided only `N = 8`), rerun at 1600 bits and `η = 2⁻⁴¹⁶` (997 s): unshifted `K_N > 0`
for `N = 8, 16, 24, 32`, with `λ_min = 1.7·10⁻¹⁷, 6.7·10⁻³⁷, 4.4·10⁻⁵⁵, 2.1·10⁻⁷²`, about `2.3` decades per basis
function.

`eig_fw.py` gives the smallest generalised eigenvalue of the midpoints; `unshifted` is the receipt's own Arb verdict.
The minimum falls between `1.7` (near `N = 10`) and `1.3` (near `N = 56`) decades per basis function, with no
plateau. The spaces are nested, so `K_N + N⁻⁴ G_N > 0` for every `N` is equivalent to the Weil form being nonnegative
on the whole window of half-width `π`; no finite list of `N` gives it, and with a tail bound the low block has to resolve that infimum (Zhu's asymptotic law
puts it near `10⁻³⁰⁵²`; at `0.8` the same law gives `10⁻²⁴·⁵` against the certified `≈ 10⁻¹⁷`, so it is only a rough
guide).

## Files

* `make_exact_tail.py V2/feshbach_blocks_arb.py OUT.py`: the exact-tail variant (checks the input's SHA-256).
  Run as `run_all.sh` does, with `EXW=uniform` or `EXW=mixed`, e.g.
  `EXW=mixed python3 OUT.py 1.6 200 3000` then `python3 schur_arb.py blocks_N200_NP3000.json 1.32327472166 4.5e-12`.
* `eig_fw.py RECEIPT.json`: the table above from the PR #7 receipts
  (`git show e9c3bff7:AegisRH/fixed_window_true_matrix_arb.py`, flags as in the table).

Evidence kinds: `certified_numerical` (Arb) for both sections; nothing here is a Lean proof and nothing is promoted.
**RH remains OPEN.**
