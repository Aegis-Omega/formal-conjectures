# Cross-row budget and Krein gap at L = 6/5: numerical feasibility (2026-10-20)

Status: float numerics, untrusted, no certificate. One window only. Not RH.

## Verdict

`hfin` together with `hlow` is numerically feasible at L = 6/5, with a margin of about 1.4–1.9×.
It needs two conditions:

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

## What a certificate still needs

- **Row budget:** certify `κ·Q_CvS − B ⪰ 0` with κ ≈ 40–45, a 139×139 matrix inequality for the
  packed checker. B also needs τ_k enclosures up to k ≈ NP + 70: up to about 2070 for the
  existing lemma, or about 470 with a tail-Gram lemma.
- **Krein certificate:** prove `hcert` rigorously for all t, either with interval arithmetic in
  t or with a Lipschitz bound between grid points. The LP coefficients reach about 2e7, so the
  rational data must be exact.
- **Trace bound:** prove the trace integral bound for the chosen slack.
- **Scope:** even then the result covers only test functions with 2r ≤ 6/5. Not RH.
