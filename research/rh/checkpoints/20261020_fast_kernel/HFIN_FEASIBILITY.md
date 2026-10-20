# Cross-row budget and Krein gap at L = 6/5: numerical feasibility (2026-10-20)

Status: validated numerics, not a Lean certificate. One window only. Not RH.

## Verdict

All numerical premises of `CvSWindowL12V1.window_L12` pass a validated numerical check (§5):

- `hcert` holds for every t, with the bisection bound on [0, 500] and an envelope bound beyond 500.
- The trace bound gives a gap m − T/(2π) ≥ 1.2199.
- The relative budget `50·Q_CvS − B ⪰ 0` holds with the existing Lean `rowTail`, at NP = 2000.
  It is robust to the widths of the certified boxes, and it needs a gap ≥ 1.0554.

The float exploration below found the route. It needs two conditions:

1. The budget must be measured against `Q_CvS`, using `CvSRelativeBudgetL12V1.hlow_L12_relative`,
   not against `‖c‖²`.
2. The Krein certificate must use the correction terms H and d. A slack-only certificate is not
   enough.

## 1. The low form and the ‖c‖² interface

`tools/hfin_feasibility_l12.py` sets up the model:

- τ_k is the digamma closed form plus the log 2 and log 3 nodes. It lies inside all 70 certified
  `tauFLo`/`tauFHi` boxes.
- Diagonal entries are the midpoints of `diagLo`/`diagHi`.
- `lam` is the projection onto the atom rows.

On the 139 atoms, `Q_CvS` has eigenvalues from 3.0e-2 to 6.6e10, so its condition number is
2.2e12.

The interface `Brow ≤ beta·‖c‖²` with coercivity `δ‖c‖²` needs a Schur gap of at least 2.5e10.
That holds even with the true λ_min, so this interface cannot close at L = 6/5.

## 2. Row budget κ = max Brow / Q_CvS

| rows | tail bound | NP | κ | gap needed = κ / ((2π)²·1.2) |
|---|---|---|---|---|
| exact, NP → ∞ | none | ∞ | ≈ 25.3 | ≈ 0.53 |
| existing `rowTail` (T = `tauBound 3` = 29.5, K = 2) | Lean today | 2000 | 39.1 | 0.83 |
| existing `rowTail` | Lean today | 1000 | 99.6 | 2.10 |
| exact tail Gram, T = 29.5 | new lemma | 400 | 45.3 | 0.96 |
| exact tail Gram, T = 12 | new lemma and a sharper τ bound | 200 | 33.4 | 0.70 |

These numbers come from `tools/hfin_tail_l12.py`.

- **Existing `rowTail` majorant:** it uses (x + Ty)² ≤ (1+ε)x² + (1+1/ε)T²y² and
  (Σ|a_n|)² ≤ 141·Σ|a_n|².
- **"Exact tail Gram":** it bounds Σ_{|m|>NP} |row_m|² by
  (L/π)² a*((1+ε)DGD + (1+1/ε)T²G)a, where G(n,n') = Σ_{|m|>NP} 1/((m−n)(m−n')), which has a
  digamma closed form, and D = diag(τ_n).
- **T = 12** would need a new Lean bound |τ_k| ≤ 12. The proved bound is `tauBound 3` = 29.5;
  the observed values satisfy |τ_k| ≲ 12.

## 3. Krein gap m − T/(2π)

`tools/krein_gap_l12.py` maximizes the gap subject to `hcert` with M = 3:

- **Correction terms:** H is a sum of hat bumps supported in |u| ≥ L, and the d-terms are
  (it)^j e^{itL} for j ≤ 4.
- **Slack:** s ≥ 0, with T = ∫ s·trialDist.
- **trialDist** is the exact distance of e^{ixt} on [0, 6/5] from the atom span.
- **Grid:** t ∈ [0, tmax].
- **Tail t ≥ tmax:** an envelope bound replaces the grid.
- **Safety margin:** MU = 0.05.
- **Check:** the optimum is re-checked on a 5× finer grid up to 2·tmax.

**Slack only (H = d = 0):** the best gap is −2.96. The atoms are moment-zero, so they are
orthogonal to 1 and x. As a result trialDist(t) ≈ 6/5 near t = 0, which is exactly where
ScertM(0) = −7.6.

| L | h | J | tmax | dt | m | T | gap | re-check |
|---|---|---|---|---|---|---|---|---|
| 1.21 | 0.05 | 30 | 300 | 0.02 | 1.54 | 2.74 | 1.10 | 0 points below 0 |
| 1.25 | 0.05 | 30 | 300 | 0.02 | 1.54 | 3.10 | 1.04 | 0 |
| 1.30 | 0.05 | 30 | 300 | 0.02 | 1.54 | 3.54 | 0.97 | 0 |
| 1.25 | 0.05 | 40 | 500 | 0.02 | 1.95 | 3.99 | 1.32 | 0 |
| 1.25 | 0.05 | 40 | 500 | 0.01 | 1.95 | 3.98 | 1.32 | 0 |

## 4. Margins

The best Krein gap is 1.32. Against each row-budget route:

| route | gap needed | margin |
|---|---|---|
| existing Lean lemmas, NP = 2000 | 0.83 | 1.6× |
| new tail-Gram lemma, NP = 400 | 0.96 | 1.4× |
| tail-Gram lemma and \|τ\| ≤ 12, NP = 200 | 0.70 | 1.9× |

## 5. Validated check

These checks are rigorous for their inputs. The node values of ScertM and of τ come from the
mpmath digamma at 30–40 digits. For k ≤ 70 the τ values agree with the certified boxes.

### `tools/validate_krein_l12.py sol.npz`

The input `sol.npz` comes from `krein_gap_l12.py 1.25 0.05 40 500 0.02 0.05 sol.npz`.
F = Wt(S − m + s) + K is the `hcert` integrand.

- **Cells on [0, 500].** On each cell, F ≥ min(F(a), F(b)) − w²/8 · sup|F''|. The supremum is
  bounded with:
  - |K'''| ≤ Σ|a_j|·2h(u_j + h)³ + Σ_j |d_j|·Σ_i C(3,i)·(j)_i·t^{j−i}·L^{3−i}, using the hat
    Fourier representation;
  - |S'| ≤ (4/t² + π/t)/2 + 2.08 for t ≥ 2, and 10.7 otherwise (ζ(2,1/4)/2 + 2.073 = 10.672);
  - |S''| ≤ (16/t³ + 8/t²)/4 + 2.01 for t ≥ 2, and 34.4 otherwise (ζ(3,1/4)/2 + 2.002 = 34.334).

  Cells that fail are bisected.
- **Tail t ≥ 500.** Re ψ(1/4 + it/2) is increasing (Im ψ' < 0), and the H and d terms are bounded
  by explicit envelopes.
- **Trace T.** T is bounded above on a 0.002 grid with trialDist' ≤ 2√(LT⁴/3) < 1.67.

Result: PASS. 27157 cells are verified, with min (lower bound)/Wt = 1.05e-4. The tail margin is
0.05, T ≤ 4.5874, and **m − T/(2π) ≥ 1.2199**.

### `tools/validate_rows_l12.py . 2000 2 3 50 0.0000003`

- **B, the finite rows.** These are the rows |m| ≤ 2000, with lam the rounded projection. Any lam
  is admissible.
- **B, the tail.** The existing `rowTail M (6/5) F a 2 (tauBound 3) 70 2000` is bounded by a
  quadratic majorant, with ε = 3.
- **Arithmetic.** All products are exact integers at scale 2^100. The final LDLᵀ of
  50·Q_CvS − B runs at 80 digits.
- **Robustness.** The check also holds under any error of operator norm ≤ 3e-7, both in the
  low-block entries and in the entries of the outside rows. The certified τ and diagonal boxes
  give at most 2.3e-7 inside (twice λ_max of the box radii) and 2.6e-7 outside (a Frobenius
  bound).

Result: PASS. All 139 pivots are > 0, with minimum 108.29. κ* = 50 needs a gap ≥ 1.0554, and the
Krein gap is 1.2199: a margin of 1.16×.

## What a certificate still needs

- **Row budget:** certify `50·Q_CvS − B ⪰ 0` in Lean (it passes the validated check in §5), a
  139×139 matrix inequality for the packed checker. B also needs τ_k enclosures up to k ≈ NP + 70: up to about 2070 for the
  existing lemma, or about 470 with a tail-Gram lemma.
- **Krein certificate:** prove `hcert` rigorously for all t, either with interval arithmetic in
  t or with a Lipschitz bound between grid points. The LP coefficients reach about 2e7, so the
  rational data must be exact.
- **Trace bound:** prove the trace integral bound for the chosen slack.
- **Scope:** even then the result covers only test functions with 2r ≤ 6/5. Not RH.
