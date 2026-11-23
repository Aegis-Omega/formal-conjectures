# Kronecker-packed dot products in the kernel (step 1 of the 9/5 Arb port)

## Result

`KroneckerDotV1.lean` proves `dot_digit`. For lists `a`, `b` of length `n > 0` with entries at most `A`
and `B`, and `2 n A B < 2^w`:

    (pack w a * pack w b.reverse / 2^(w (n − 1))) % 2^w = Σ aᵢ bᵢ,    pack w l = Σ lᵢ 2^(w i).

How the proof goes:
- The packed numbers are evaluations at `2^w` of the polynomials `Σ lᵢ Xⁱ`.
- Coefficient `n − 1` of the product is the dot product (`coeff_mul`, antidiagonal sum, reversal).
- Every coefficient is below `2^w`, so digit `k` of `p(2^w)` is `coeff k` (`digit`, by induction on
  the degree with `divX`).

The kernel evaluates `Nat.mul`, `Nat.div` and `Nat.mod` with GMP, so one dot product becomes one big
multiplication and one digit extraction.

Benchmark (`KroneckerDotBenchV1`, not committed: two literal lists of 800 random 160-bit numbers, seed
20261116, `w = 336`):
- `packed` (`decide +kernel` on the packed digit) and `dot_ab : dot a b = d` are proved;
- the whole module takes 8 s, including the import and the elaboration of the literals.

Next steps (`notes/arb_lean_port.md`):
- signed entries (offset or a split into positive and negative parts);
- the Gram and `LDLᵀ` residual checker over rows;
- the Cauchy-convolution sums for `RᵀR`.

The module was built on Lean 4.33.1 with Mathlib, at default trust and with `--trust=0`. Both runs exit 0
with no errors or warnings. `dot_digit` has axioms `[propext, Classical.choice, Quot.sound]`.
sha256: `3fecee9e98d7704ed37dcb2eb53e783edab5b52761a2d3ef8ac0dee341da7f1a`. Not RH.
