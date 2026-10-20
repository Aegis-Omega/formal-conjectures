# Cross-row budget at L = 6/5: feasibility (2026-10-20)

Status: numerics only, untrusted. Not RH.

## Question

`CvSRowTailV1.window_of_certificate_tail` needs `hfin` (the cross rows bounded by `Brow`) and
`hlow`. `CvSProjectedBasisL12V1.hlow_of_checked_source` closes `hlow` from two inequalities:
`Brow c ≤ beta · ‖c‖²` and `beta ≤ (2π)² · LT · gap · δ`. Here δ is the coercivity constant
and gap = m − T/(2π) is the Schur gap.

How large must the Schur gap be?

## Model

`research/rh/feshbach_lean_v1/tools/hfin_feasibility_l12.py`:

- τ_k is the digamma closed form plus the log 2 and log 3 nodes. It lies inside all 70 certified
  boxes `tauFLo`/`tauFHi`.
- Diagonal entries are the midpoints of `diagLo`/`diagHi`.
- `lam` is chosen optimally, i.e. the projection onto the atom rows.
- Rows `|m| ≤ NP` only. `rowTail` is not included.

## Result

`Q_CvS` restricted to the 139 atoms has eigenvalues from 3.0e-2 to 6.6e10, so its condition
number is 2.2e12.

| NP | beta / ‖c‖² | gap needed via ‖c‖² | κ = max Brow/Q_CvS | gap needed via Q_CvS |
|---|---|---|---|---|
| 100 | 2.97e10 | 2.1e10 | 14.6 | 0.31 |
| 400 | 3.58e10 | 2.5e10 | 21.9 | 0.46 |
| 2000 | 3.70e10 | 2.6e10 | 24.6 | 0.52 |

The "via ‖c‖²" column already uses the true λ_min, 3.0e-2. With the certified
δ = certifiedMu/basisFrobenius ≈ 1.7e-4, the requirement is about 175 times larger again.

## Consequence

- **The ‖c‖² interface cannot close at L = 6/5.** The budget in `hlow_of_checked_source` and
  `CvSLowCoercivityL12V1.hlow_L12` would need a Schur gap of order 10^10 or more.
- **A budget relative to `Q_CvS` needs a gap of about 0.52–0.55.** κ converges slowly in NP.
  `CvSRelativeBudgetL12V1.hlow_L12_relative` closes `hlow` from `Brow c ≤ κ · Q_CvS c` and
  `κ ≤ (2π)² · (6/5) · gap`.
- **Next certificate:** check `κ·Q − B ⪰ 0` as a 139×139 matrix inequality with the packed
  checker. `B` needs `cvsEntry` enclosures for `|m| ≤ NP` (τ_k up to k = NP + 70) and the
  `rowTail` bound.
- **Open:** whether a Krein certificate (`hcert`, trace `T`) reaches m − T/(2π) ≥ 0.55 has
  not been computed.
- Even if it does, the window covers only test functions with 2r ≤ 6/5. Not RH.
