# The converse of the moment killer (HOLON OPTIMUS V2, claim 1)

## Result

`AegisRH/PR606/WeilMomentKillerInverseV1.lean` adds two theorems about
`AEGIS.WeilMomentKillerConstructionV1.momentKiller ψ = ψ' + ψ''`.

- `exists_momentKiller_eq`: every smooth compactly supported `φ : ℝ → ℝ` with `∫ φ = 0` and
  `∫ φ eᵘ = 0` is `momentKiller ψ` for a smooth compactly supported `ψ`. The witness is the potential
  `ψ(t) = ∫_{-A}^{t} (1 − e^{s−t}) φ(s) ds = Φ₀(t) − e^{−t} Φ₁(t)`, for any `A ≥ 0` with
  `tsupport φ ⊆ Ioo (-A) A`.
  - `pot_eq_zero`: beyond `A` the potential equals `∫ φ − e^{−t} ∫ φ eˢ`. It vanishes there exactly
    because both moments vanish.
- `momentKiller_injective`: the preimage is unique.

With `integral_momentKiller` and `integral_momentKiller_mul_exp` of the existing module,
`momentKiller` is a bijection from smooth compactly supported functions onto those with both moments
zero. These are real functions; for a complex test function, apply it to the real and imaginary parts.

The module was built on Lean 4.33.1 against the compiled repository oleans, at default trust and with
`--trust=0`. Both runs exit 0 with no errors or warnings. Both theorems have axioms
`[propext, Classical.choice, Quot.sound]`.
sha256: `60930aa6b6f16e15fa6f7df7029c67a03d11458d600fde0d45d94d7f8c8b779e`

## Independent checks of the V2 claims (`check_v2.py`, sympy)

- **Inverse formula.** `ψ'' + ψ' = φ` holds for the integral formula (Leibniz rule). The formula recovers
  `ψ₀ = (1 − t²)⁵` and `ψ₀ e^{3it}` exactly from `φ = ψ₀'' + ψ₀'`.
  - When a moment is nonzero, the tail beyond the support is `M₀ − e^{−t} M₁`.
- **Energy identity.** `e^{t/2} T(e^{−t/2} h) = h'' − h/4` holds for `T = D² + D`. For compactly supported
  `h`, `‖h'' − h/4‖² = ‖h''‖² + ½‖h'‖² + (1/16)‖h‖²`.
  - Hence `‖h‖ ≤ 4‖F‖`, `‖h'‖ ≤ √2‖F‖` and `‖h''‖ ≤ ‖F‖`. This is the critical-line bound
    `|s² − 1/4| ≥ 1/4`, and it does not depend on the support width.
- **Exact localization.** For a partition of unity `χ_j` on the support, `φ_j = T(χ_j ψ)` has both moments
  zero and `Σ φ_j = φ`.

## Scope

Localization does not extend the positivity reach. Positivity through blocks is scale invariant, so it is
limited by the coupling of the blocks, not by the norms of the pieces.
- With diagonal dominance as in V7, the margin is about `log(1/w) − 3.6` for a cluster of log-width `w`.
  It is positive only for `w ≲ 0.1`.
- Any weighting (Schur or SOS) is at best `λ_min` of the true normalized block Gram matrix. That is what the
  window certificates compute exactly.
- `CvSWindowL138V1.window_L138` already covers every moment-zero test function whose log-support has length
  at most `13/8` (`HalfWidthAt g r a = LogSupportIn g (a − r) (a + r)`, `2r ≤ 13/8`). That includes the whole
  H64 span (width about 0.724).
- The open part is the windows `L > 13/16`.
- The 192-block model of V2 uses hypothetical inter-block entries. Not RH.

## Follow-up: closed-form pivots and Woodbury for the 9/5 Arb blocks

This concerns `aegis_source_0c1477f/research/feshbach_arb_v2/feshbach_blocks_arb.py`, which builds a
moment-zero basis on modes `|m| ≤ N`.
- Construction in the source: the constraints are `Σ_m u_m μ_s(m) = 0` for `s = ±1/2`, and the pivots are
  `[0, 1]`. The matrix `Z` is the identity on the other `k = 2N − 1` modes and has two pivot rows `U`.
- Hence `G11 = ZᴴZ = I + UᴴU`, and the source computes `G11.inv()` inside
  `C_B = Zᴴ(RR + Tail + Ib)Z − A11 G11⁻¹ A11`.

Checks (`check_woodbury.py`, `check_woodbury_arb.py`):
- **Real rational pivots.** The factor `e^{sL} − 1` cancels row-wise, which gives (sympy, exact), with
  `κ = (2π/L)²`:
  - `U₀(m) = (m − 1)(1/4)/(1/4 + κm²)`
  - `U₁(m) = −m(1/4 + κ)/(1/4 + κm²)`

  At `L = 9/5`, `N = 400` the Arb enclosures of the closed forms overlap the source's pivots for all 799
  modes (precision 200).
- **Woodbury.** `G11⁻¹ = I − Uᵀ(I₂ + UUᵀ)⁻¹U` holds; the float residual is `1.9·10⁻¹⁵`.
  - `eig(G11) ∈ [1, 3.333]`, so `‖G11⁻¹‖ ≤ 1` and `I₂ + UUᵀ ⪰ I₂`.
  - In Arb (precision 200), the direct `G11.inv()` takes 13.4 s, against 0.3 s for Woodbury. The enclosures
    overlap, and the Woodbury radii are 3× smaller (`1.0·10⁻⁵⁸` against `3.3·10⁻⁵⁸`).

Scope. Woodbury removes the 799×799 inversion and makes `G11` and `G11⁻¹` explicit, through π only via `κ`.
The dominant costs remain:
- `RᵀR` (32001 × 801);
- `A11 G11⁻¹ A11 = A11² − (A11Uᵀ)(I₂ + UUᵀ)⁻¹(UA11)`, which still contains `A11²`;
- the Schur `LDLᵀ` at `k = 799`.

The full Arb verifier has not been re-run with Woodbury. Not RH.
