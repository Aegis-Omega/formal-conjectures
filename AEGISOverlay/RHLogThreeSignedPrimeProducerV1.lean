/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import AEGISOverlay.RHPrimeThreeWindowV1

/-!
# Actual prime-row producer: the exact 2 log 3 gap

The source exact-von-Mangoldt theorem gives a genuine prime mixed entry
for any width-1/256 moment-zero fine packet at logarithmic gap 2 log 3.
This file makes the first explicit SIGNED real prime-row budget usable by
the Arch-29 producer. No assumed prime-cost matrix or surrogate Gram is
used. The result concerns this specified pair, NOT arbitrary translated
packets, unrestricted reconstruction, or unconditional RH.

The weaker coefficient 1/2 is intentionally rational and can be proved
using only exp(log 3) = 3 and the universal inequality 1 + x <= exp x.
-/

open Complex
open AEGIS.RHPrimeThreeWindowV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHDyadicDiagonalV13

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHLogThreeSignedPrimeProducerV1

theorem triadicHalf_two_exact : triadicHalf 2 = (1 / 3 : ℝ) := by
  calc
    triadicHalf 2 = Real.exp (-Real.log 3) := by
      unfold triadicHalf
      congr 1
      ring
    _ = (1 / 3 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_num

theorem log_three_le_two : Real.log (3 : ℝ) ≤ 2 := by
  have h := Real.add_one_le_exp (Real.log (3 : ℝ))
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at h
  linarith

/-- No free prime-row hypothesis: the true signed von Mangoldt sum of the
source pair separated by 2*log 3 has a rational half-energy cost. This
is a non-vacuous instantiated arithmetic producer, not a norm proxy. -/
theorem actual_signed_prime_gap_two_log_three
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256 : ℝ) a) :
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g (2 * Real.log 3)))).re ≤
      (1 / 2 : ℝ) *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g (2 * Real.log 3)).1) := by
  have hp := gap_prime_sum_exact_three
    g (1 / 256 : ℝ) a 2
    (by omega) (by norm_num) (by norm_num) (by norm_num) hw
  have hpReal := congrArg Complex.re hp
  simp only [Complex.ofReal_re] at hpReal
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hlog : Real.log (3 : ℝ) * energy g.1 ≤
      2 * energy g.1 :=
    mul_le_mul_of_nonneg_right log_three_le_two hE
  calc
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g (2 * Real.log 3)))).re =
        Real.log 3 * triadicHalf 2 * energy g.1 := hpReal
    _ = (Real.log 3 / 3) * energy g.1 := by
      rw [triadicHalf_two_exact]
      ring
    _ ≤ (1 / 2 : ℝ) * (energy g.1 + energy g.1) := by
      nlinarith [hlog, hE]
    _ = (1 / 2 : ℝ) *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g (2 * Real.log 3)).1) := by
      rw [translate_energy, translate_energy]

end AEGIS.RHLogThreeSignedPrimeProducerV1

#print axioms AEGIS.RHLogThreeSignedPrimeProducerV1.triadicHalf_two_exact
#print axioms AEGIS.RHLogThreeSignedPrimeProducerV1.log_three_le_two
#print axioms AEGIS.RHLogThreeSignedPrimeProducerV1.actual_signed_prime_gap_two_log_three
