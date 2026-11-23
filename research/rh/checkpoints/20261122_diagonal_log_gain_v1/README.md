# Diagonal log gain at width 1/32: 103/100 → 17/10

## What is new

Two modules:

* `WeilDiagonalLogGainS1V1.lean` imports Mathlib only.
* `WeilDiagonalLogGainV1.lean` imports `WeilWidthArchIntegralV27` (`AegisRH/PR606`) and the module above.

These implement steps 1 and 2 of the "key next step" in `research/rh/atomic_map_v1` (AEGIS-OMEGA PR #835, §4).
That report found that the binding constraint of the fixed-width comb is the diagonal, not the resonances:

* `width_diagonal_103_over_100_v27` gives `103/100`;
* the true moment-free value is about `1.97`.

V26/V27 bound the inner Archimedean window `(0, 1/32]` by a constant, `E·e^{1/64}/2`. That constant majorant throws
away the sign of `E − Re C(u)`.

### `WeilDiagonalLogGainS1V1`: the sub-lemma S1, on a general interval

Let `h : ℝ → ℂ` be continuous and vanish outside `[a, b]`. Write `E = ∫‖h‖²` and `C(s) = ∫ h(x+s)·conj(h x) dx`.

* `log_gain_lintegral`: `ofReal (log 2 · E) ≤ ∫⁻_{(0, b−a]} ofReal ((E − Re C(s))/s)`. There is no extra hypothesis.
* `log_gain_interval` is the Bochner form on `[a, b]`.
* `log_gain` is the Bochner form on `[0, 1]`, which is §4.5 criterion 1.
* Both Bochner forms assume that the right side is integrable.
  * Lean's Bochner integral of a non-integrable function is `0`.
  * For a merely continuous `h`, the right side need not be finite.
  * So the hypothesis cannot be dropped from the Bochner form.
  * The transport below uses the lintegral form, which needs no such hypothesis.

The proof follows the four steps of §4.3:

1. `sq_norm_sub_shift`: `E − Re C(s) = ½∫|h(x+s) − h(x)|²`.
2. `pointwise_lower`: on `{x > b − s}` and on `{x < a}` one of the two terms vanishes.
3. Tonelli (`lintegral_lintegral_swap`) and `lintegral_inv_Ioc` turn the two pieces into the weights
   `log (w/(b−x))` and `log (w/(x−a))`.
4. `two_log_two_le`: their sum is at least `2 log 2`, because `4(b−x)(x−a) ≤ w²`.

### `WeilDiagonalLogGainV1`: transport into the width-1/32 diagonal

The setting is `g : WeilCompactSmoothGV1` with `WidthOneThirtyTwoAt g a`. No moment hypothesis is used.

1. `inner_pointwise` holds on `(0, 1/32]`:
   `e^{−1/32}·(E − Re C(u))/u ≤ E·e^{1/64}/2 − widthArchLogIntegrandV26 g u`.
   The inputs are:
   * `C = logCorrelationV25`;
   * `Re C ≤ ‖C‖ ≤ E` (V25);
   * `sinh u ≤ u·e^{1/32}`;
   * the V26 kernel bound `(e^{u/2} − 1)/sinh u ≤ e^{1/64}/2`.
2. `inner_integral_log_gain` applies S1 to `logLift g.1` on `[a − 1/64, a + 1/64]`:
   `∫_{(0,1/32]} widthArchLogIntegrandV26 g ≤ E·(small − e^{−1/32}·log 2)`.
   It replaces `width_arch_inner_integral_le_v27`, which gives `E·small`.
3. `width_archimedean_budget_log_gain` gives the corresponding V27 budget, with the same tail identity.
4. `diagonal_log_gain_v1`, which is §4.5 criterion 2:

       E · (diagonalTailV24 − diagonalKappaV21 − diagonalSmallV21 + e^{−1/32}·log 2) ≤ −Re B(g, g).

   Here `small = e^{1/64}/64 < 1/63`, so this is at least the constant stated in the criterion.
5. `log_gain_constant_gt` shows that the constant exceeds `17/10`. Its inputs are the V21 floor `32449/31500`,
   `tail ≥ 6 log 2`, `e^{−1/32} ≥ 31/32` and `log 2 > 693/1000`.
6. `width_diagonal_17_over_10`: `(17/10)·E ≤ −Re B(g, g)`. The hypotheses are the same as those of
   `width_diagonal_103_over_100_v27`.

Numerically, the constant is `1.706675`; PR #835 reports `1.70667`.

## Effect, and what is not done

* **The comb theorem is not done.** The five-block fixed-width comb, §4.5 criterion 3, is not proved here.
  * The Perron budget of PR #835 §3 gives margin `1.7 − 1.5216 ≈ 0.178` at five blocks, using the `1/100`
    Archimedean bound.
  * Stating it in Lean needs the V28–V31 cross lemmas for gaps `k = 3, 4`.
* **The second stage is not done.** That is the moment gain of §4.4, about `3.16`.
* This is a diagonal estimate for the width-1/32 packet class only. There is no off-diagonal estimate and no global
  Weil sign, and it is not RH.

## Build

* Lean 4.33.1 + Mathlib (formal-conjectures toolchain), against the `AegisRH/PR606` oleans.
* Both modules were built at default trust and again with `--trust=0`.
* Both runs exit 0, with no errors and no `sorry`.
* Every `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of the built sources:

    8cbe03a0330c7144ba4b8cac7b9e424de8c1d9e64da771ca477b04f24f75b3d6  WeilDiagonalLogGainS1V1.lean
    fc99a0df08ae447b4b29d8c86d5446c03747572f9abeaee180d3e71931b14811  WeilDiagonalLogGainV1.lean
