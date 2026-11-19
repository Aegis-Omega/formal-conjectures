# `hresidual` fails on a near-kernel packet (analysis and float check, 2026-11-10)

Evidence kind: `numerical`, with an analytic derivation. Step 1 of the derivation is
kernel-checked (`lean_kernel`, abstract form); steps 2 to 4 and the float check are not.
RH status: OPEN.

## Claim

The hypothesis `hresidual` of `riemannHypothesis_of_canonical_resonance_producer`
(`AEGISOverlay/RHPrimeFreeRecompositionJoinV1.lean`) cannot hold for every moment-zero `g`. It
fails for a near-kernel packet of the proved window `2r ≤ 11/8`.

## Derivation

Notation: `E_a = energy (gs a)`, `B_ab = (B (gs a) (gs b)).re`, `LF` = `FineLogFreeGap` of the
centre gap, `c = 676/65536`, `β = 57430/65536`, `κ = 5671/3200`.

1. Algebra, from the hypothesis alone. Multiply row `a` by `E_a ≥ 0`, sum over `a`, and use the
   symmetry of `residual` and of `LF`, the bound for pairs that are not log-free, and the diagonal
   bound `κ E_a ≤ −B_aa`:

       −Re B(g,g) ≥ (κ − 2β) ∑_a E_a + ∑_{a ≠ b, LF} [c (E_a + E_b) − B_ab]        (N)

   Here `κ − 2β = 8013/409600`, and `641/32768` is a lower bound for it. With the log-free lemma
   the bracket is nonnegative and (N) gives the conclusion of
   `actual_source_gram_coercive_of_resonance_row`. (N) keeps the bracket.

   Kernel-checked in abstract form: `weighted_row_sum` and `hresidual_constants` in
   `RHResonanceRowWeightedSumV1.lean` (Mathlib only; Lean 4.33.1, Mathlib
   `0df444a360eaa60ab8c11dca51a86af692955474`, `lean --trust=0`, exit 0, no `sorry`, axioms
   `[propext, Classical.choice, Quot.sound]`, `leanchecker` exit 0; source SHA-256
   `8778257b04add7d93917da88c5bc1ffa96a8d35a3f7dd3c5738f7615e1b8165d`). The instantiation to the
   lab's `B`, `energy` and `FineLogFreeGap` is not compiled.

2. Grouping. Group the pieces by centre; let `H_i` be the sum of group `i`, `e_i` its energy and
   `k_i` its size. Cauchy–Schwarz gives `∑_{a ∈ i} E_a ≥ e_i / k_i`, and
   `e_i k_j / k_i + e_j k_i / k_j ≥ 2 √(e_i e_j)`, so
   `∑_{LF} c (E_a + E_b) ≥ 2c ∑_{ordered LF group pairs} √(e_i e_j)`. By bilinearity
   `∑_{LF} B_ab = ∑_{LF group pairs} Re B(H_i, H_j)`. Duplicating pieces does not shrink the
   bracket.

3. Size of a log-free interaction. For moment-zero functions with disjoint supports at distance
   at least `d`, with no prime power in range, only the off-diagonal archimedean kernel
   `K(u) = e^{−u/2} / (1 − e^{−2u})` acts, so
   `|Re B(H_i, H_j)| ≤ K(d) ‖H_i‖₁ ‖H_j‖₁ ≤ (K(d)/128) √(e_i e_j)`. For `d ≥ 1/2 − 2/128` this is
   `θ √(e_i e_j)` with `θ = 0.00988 < 2c = 0.02063`.

4. Two intervals. Let `A`, `B` be intervals all of whose mutual gaps lie in `[1/2, 0.675]`. Every
   piece meeting `A` has its centre within `1/256` of `A`, and the same for `B`, so every such pair
   of centres is log-free. Also `∑_{i meets A} √e_i ≥ ‖g 1_A‖₂`, and the same for `B`. Hence

       −Re B(g,g) ≥ 2 (2c − θ) ‖g 1_A‖₂ ‖g 1_B‖₂ ≈ 0.0215 ‖g 1_A‖₂ ‖g 1_B‖₂        (N')

## Float check (`obst.py`, `OBSTRUCTION.log`)

Window `11/8`, 139 atoms, the model of `../20261110_window_l32_feasibility_v1/feas.py`:

- the near-kernel packet has `−B(g,g)/‖g‖² ≈ 1.64e-7`;
- with `A = [0.170, 0.260]`, `B = [0.760, 0.845]`, `‖g 1_A‖ ‖g 1_B‖ / ‖g‖² ≈ 0.0723`;
- (N') would force `−B(g,g)/‖g‖² ≥ 1.55e-3`. It is missed by a factor of about 9,500.

On the window `1` the smallest Rayleigh quotient is `1.2e-2` and (N') is not violated. The
obstruction appears only where the form has a near-kernel.

## Caveats

- Float model. It reproduces `κ` of the 11/8 port; it is not a certificate.
- The packet is a trigonometric polynomial under a `sin²` window, not `C^∞`. A mollified copy is
  needed to lie in `WeilCompactSmoothGV1`. The factor 9,500 leaves room; the mollification is not
  done here.
- Step 3 is read from the classical explicit formula, not derived from the Lean definition of `B`.
  The lab constant is consistent with it: `2c = 0.02063` against `K(34/128)/128 = 0.0166`.
- Energy is taken as the `L²` norm in the log variable. Another weight changes the constants by
  at most `e^{0.7}`.
- Step 2 is a finite-sum argument and can be kernel-checked with Mathlib only. Not done here.

## Consequence

`hresidual` charges every log-free pair the fixed positive allowance `676/65536`. A near-kernel
packet needs those pairs to cancel almost exactly, so the true signed interaction would have to
be used. A row-sum certificate with fixed positive allowances cannot hold on a window whose
smallest eigenvalue is below about `1e-3`; the window `11/8`, proved positive by `window_L118`, is
already such a window. Do not look for a producer of `hresidual`.
