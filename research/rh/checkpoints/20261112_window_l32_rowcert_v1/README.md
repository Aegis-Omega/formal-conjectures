# Window 3/2 port — relative row certificate (299 atoms, `NP = 900`, `κ = 60`)

Date: 2026-11-12. Status: **kernel-checked locally**, default trust and `--trust=0`. Not run in CI.
**RH remains OPEN**; `window_L32` is not proved.

## Result

```lean
theorem AEGIS.CvSRelRowHBL32V1.hB (M : ℕ) (hM : 4 ≤ M) (c : Fin 299 → ℂ) :
    Brow M c ≤ 60 * Q_CvS M (3 / 2) ctr c
theorem AEGIS.CvSRelRowHBL32V1.Q_nonneg (M : ℕ) (hM : 4 ≤ M) (c : Fin 299 → ℂ) :
    0 ≤ Q_CvS M (3 / 2) ctr c
```

`ctr i = i − 149` (atoms `−149, …, 149`), low frequencies `F = [−150, 150]`, outside rows
`150 < |m| ≤ 900`. These are the two premises that `CvSWindowL118V1.window_L118` takes from
`CvSRelRowHBL118V1` (there `hB 3 le_rfl c`, `Q_nonneg 3 le_rfl c`), now at `L = 3/2` for every prime
cutoff `M ≥ 4`.

Also here: `CvSTauFarL32V1.lean` (hand-written, 4.6 kB), the far bound the window theorem needs:

```lean
theorem AEGIS.CvSTauFarL32V1.tau_abs_le_far {M : ℕ} (hM : 4 ≤ M) {n : ℤ} (hn : 151 ≤ |n|) :
    |tau M (3 / 2) n| ≤ 15
```

It combines `CvSTauFarL12V1.source_integral_abs_le_inv` (`|∫ h₊ S_n| ≤ L/|n| + π²/2`) with the prime part
of `CvSTauFastL32V1` (prime powers `2, 3, 4`); the value is about `14.19`.

Error budget (`K_ok`, exact): `Kp = 5.2735049682·10⁻⁹ ≤ Kq/2⁶⁴ = 5.2736411302·10⁻⁹`.

## How

Inputs are the kernel-checked boxes of the two earlier checkpoints: `CvSTauL32AllV1.tau_mem_all`
(`../20261111_window_l32_tau_v1/`) and `CvSDiagL32V1` (`../20261111_window_l32_diagonal_v1/`).

1. `gen_rr32.py 3/2 900 1 60 0 0 0 150 15 13` — untrusted exact mirror (the parametric
   `gen_rr_k.py` of `../20261110_window_l32_feasibility_v1/`), reading the boxes through
   `boxes32.py` and asserting they match the Lean literals. Scaled `λ_min 7.70551·10⁻⁹`,
   `K' 5.2736·10⁻⁹`. Far bound `T_τ = 15` (the lab route gives
   `|τ_n| ≤ L/|n| + π²/2 + π Σ ppw ≈ 14.19` at `L = 3/2`).
2. `rescale_pkl.py` (feasibility checkpoint; `Pscale 512 → 502`), then
   `tools/cert43.py 80` (lab): `eps = 4657693007308357`, `eta = 110079149141299 < eps`; checked
   again by `check_cert_pkl.py cert43_80.pkl` (feasibility checkpoint), exit 0.
3. `make_emit_rr32.py REPO > emit_rr32.py`, `python3 emit_rr32.py out` — derived from the lab's
   `tools/emit_rr118.py`, every substitution counted. Writes `CvSRelRowCertL32V1` and the data module.
4. `chunk_data.py out/CvSRelRowDataL32V1.lean CvSRelRowDataL32V1.lean` — splits the eight big
   kernel checks (`S_ok*`, `T_ok*`, `V_ok*`; one `decide +kernel` over 301 indices runs out of
   memory) into 16 chunks of 20, reassembled by `all_of_chunks` with the original statements; splits
   the module into `CvSRelRowDataAL32V1` (boxes, outside-row tables) and `CvSRelRowDataL32V1`
   (the rest), `maxHeartbeats 0` for the large literals.
5. `make_rr32_check.py REPO .` — `CvSRelRowCheckL32V1` (the packed Gram check in 15 kernel chunks
   of 20 rows, interval shift `422 = 502 − 80`) and `CvSRelRowPsdL32V1`.
6. `port_mod.py REPO . M` for `M ∈ {Form, Box, Err, Q, Kt, Out, Tail, Inv, In, HB}` — ports
   `CvSRelRow<M>L118V1` by whole-number token rules and counted string rules
   (`port_rules.json`), and fails if a listed `11/8` constant is left. Changes beyond the
   constants: `Box` uses `tau_mem_all` (`M ≥ 4`); `Err` tightens `Cu` to `75992/10⁶` so that `K_ok`
   holds; `Kt` proves `HL.Nodup` structurally (the kernel `decide` is quadratic and runs out of
   memory at 1500 elements); `Psd` sets `maxRecDepth`.

Regenerating steps 3–6 from these scripts reproduces all 15 modules byte for byte
(`generated.sha256`; checked 2026-11-12). The modules (1.05 MB) are not committed.
The pickles are untrusted inputs: the kernel recomputes every table and the LDL check.

## Replay

Lab dependencies not in the default build (`build_list.txt`, compile in that order):
`FastKronV1`, `CvSRelRowHarmV1`, `CvSRelRowAlgebraV1`, `CvSSchurClosureFromBoundsV1`,
`CvSGramTailV1`, `RHFixIntervalV1`, `CvSPackedGramV1`. Then

```
lean CvSRelRowCertL32V1.lean; lean CvSRelRowDataAL32V1.lean; lean CvSRelRowDataL32V1.lean
lean CvSRelRowCheckL32V1.lean; lean CvSRelRowPsdL32V1.lean; lean CvSRelRowFormL32V1.lean
lean CvSRelRowBoxL32V1.lean; … ; lean CvSRelRowHBL32V1.lean   (Err Q Kt Out Tail Inv In in between)
```

`CvSTauFarL32V1.lean` imports `CvSTauFarL12V1` (lab) and `CvSTauFastL32V1` (`../20261111_window_l32_tau_v1/`).

`boxes32.py` reads `CvSTauL32K*V1.lean` and `CvSDiagL32V1.lean` from `../l32/` relative to the
script directory.

## Receipt (local, 2026-11-12; Lean 4.33.1, Mathlib `0df444a`)

| module | default (s) | `--trust=0` (s) | errors | `sorry` |
|---|---:|---:|---:|---:|
| `CvSRelRowCertL32V1` | 504 | 462 | 0 | 0 |
| `CvSRelRowDataAL32V1` | 2762 | 2672 | 0 | 0 |
| `CvSRelRowDataL32V1` | 310 | 318 | 0 | 0 |
| `CvSRelRowCheckL32V1` | 1637 | 1766 | 0 | 0 |
| `CvSRelRowPsdL32V1` | 7 | 16 | 0 | 0 |
| `CvSRelRowFormL32V1` | 6 | 7 | 0 | 0 |
| `CvSRelRowBoxL32V1` | 50 | 57 | 0 | 0 |
| `CvSRelRowErrL32V1` | 13 | 13 | 0 | 0 |
| `CvSRelRowQL32V1` | 14 | 15 | 0 | 0 |
| `CvSRelRowKtL32V1` | 7 | 9 | 0 | 0 |
| `CvSRelRowOutL32V1` | 11 | 12 | 0 | 0 |
| `CvSRelRowTailL32V1` | 14 | 15 | 0 | 0 |
| `CvSRelRowInvL32V1` | 6 | 6 | 0 | 0 |
| `CvSRelRowInL32V1` | 15 | 13 | 0 | 0 |
| `CvSRelRowHBL32V1` | 5 | 7 | 0 | 0 |
| `CvSTauFarL32V1` | exit 0 (time not logged) | 8 | 0 | 0 |

The seven lab dependencies of `build_list.txt` also replayed at `--trust=0` (exit 0, 3–7 s each).
Peak memory: `CvSRelRowDataAL32V1` about 7.5 GB at `--trust=0`.

```
'AEGIS.CvSRelRowHBL32V1.K_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSRelRowHBL32V1.hB' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSRelRowHBL32V1.Q_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AEGIS.CvSTauFarL32V1.tau_abs_le_far' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Each `CvSRelRowCheckL32V1.chunk*_ok` and every reported theorem lists only these axioms or a
subset of them (`S_ok*`, `T_ok*`, `V_ok*`: `propext, Quot.sound`; `certL_ok`: `propext`).
Evidence kind: `lean_kernel` (local).

## Remaining for `window_L32`

The window theorem `window_L32` (as `window_L118`, on `CvSActualMomentWindowJoinV1`, with `M = 4`:
`3/2 < log 5`), and the exhaustion step with frontier `3/4`.
