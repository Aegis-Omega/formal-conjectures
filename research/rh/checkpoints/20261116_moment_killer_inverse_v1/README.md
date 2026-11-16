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
