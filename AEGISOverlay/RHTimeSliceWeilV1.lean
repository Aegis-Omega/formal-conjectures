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

import AEGISOverlay.RHBaguaActualWeilV1

/-!
# AEGIS Ω — exact femtosecond time slices as arithmetic Weil translations

This bridge combines exact signed integer femtosecond ticks, a DECLARED
dimensionless logarithmic scale p, the SOURCE Weil Mellin translation
law, and the full genuine 8x8 Hermitian Weil Gram (all 64 mixed entries).

One second is represented by 10^15 ticks; for the chosen normalization
d = (ticks / 10^15) * log p. This is a user-selected parameterization,
NOT an assertion that physical time equals spectral log-time.
The integer tick ledger has no numerical rounding. The real log p
factor is a symbolic analytic real, NOT a Q16.16 approximation.

For every actual zeta zero rho, its slice is the exact factor
exp((rho-1/2)d). Its norm detects the real part of rho at every
nonzero slice. Slices compose exactly, and their actual Weil packet
Gram keeps every cross term. No universal Weil sign is assumed.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHTimeSliceWeilV1

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHBaguaActualWeilV1

/-- Exact (signed) femtosecond ticks mapped into a dimensionless
logarithmic spectral shift by an explicitly declared scale p. -/
def fsLogSlice (p : ℝ) (ticks : ℤ) : ℝ :=
  ((ticks : ℝ) / (1000000000000000 : ℝ)) * Real.log p

/-- There is no per-slice rounding: adding exact time slices
agrees with adding the corresponding logarithmic translations. -/
theorem fsLogSlice_add (p : ℝ) (a b : ℤ) :
    fsLogSlice p (a + b) = fsLogSlice p a + fsLogSlice p b := by
  simp only [fsLogSlice, Int.cast_add]
  ring

theorem fsLogSlice_zero (p : ℝ) : fsLogSlice p 0 = 0 := by
  simp [fsLogSlice]

/-- 10^15 femtoseconds is one second, giving the declared log p shift. -/
theorem fsLogSlice_one_second (p : ℝ) :
    fsLogSlice p 1000000000000000 = Real.log p := by
  norm_num [fsLogSlice]

/-- A particular nonzero sampling step: one femtosecond at log 2. -/
theorem fsLogSlice_two_one_fs_pos : 0 < fsLogSlice 2 1 := by
  unfold fsLogSlice
  have hp : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hq : (0 : ℝ) < (1 : ℝ) / 1000000000000000 := by norm_num
  simpa using mul_pos hq hp

/-- Source-exact spectral sampling factor for an actual nontrivial
zeta zero, not an approximate floating-point phase. -/
def zeroSliceFactor
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) : ℂ :=
  WeilZeroTranslationFactorV11 rho (fsLogSlice p ticks)

theorem zeroSliceFactor_zero
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) :
    zeroSliceFactor rho p 0 = 1 := by
  simp [zeroSliceFactor, WeilZeroTranslationFactorV11, fsLogSlice]

/-- Multiplicative cocycle of actual zeta-zero time slices.
This is the precise sum-to-product law behind temporal layering. -/
theorem zeroSliceFactor_add
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (a b : ℤ) :
    zeroSliceFactor rho p (a + b) =
      zeroSliceFactor rho p a * zeroSliceFactor rho p b := by
  unfold zeroSliceFactor WeilZeroTranslationFactorV11
  rw [fsLogSlice_add]
  have hexp :
      (rho.1 - (1 / 2 : ℂ)) *
          ((fsLogSlice p a + fsLogSlice p b : ℝ) : ℂ) =
        (rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p a : ℂ) +
          (rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p b : ℂ) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]

/-- Actual real-part information carried by each spectral time slice. -/
theorem zeroSliceFactor_norm
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) :
    ‖zeroSliceFactor rho p ticks‖ =
      Real.exp ((rho.1.re - 1 / 2) * fsLogSlice p ticks) := by
  unfold zeroSliceFactor WeilZeroTranslationFactorV11
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  norm_num

/-- For ANY nonzero time slice, unit modulus is equivalent to
this actual zeta zero lying on the critical line. This does not
assert unit modulus without a mathematical argument. -/
theorem zeroSliceFactor_unit_iff_critical
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ)
    (hstep : fsLogSlice p ticks ≠ 0) :
    ‖zeroSliceFactor rho p ticks‖ = 1 ↔ rho.1.re = 1 / 2 := by
  rw [zeroSliceFactor_norm]
  constructor
  · intro hh
    have hzero :
        (rho.1.re - 1 / 2) * fsLogSlice p ticks = 0 := by
      apply Real.exp_injective
      simpa only [Real.exp_zero] using hh
    have hreal : rho.1.re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hstep
    linarith
  · intro hcrit
    simp [hcrit]

/-- In particular, ONE exact femtosecond at the declared log 2
scale already represents the critical-line test for each zero. -/
theorem zeroSliceFactor_two_one_fs_iff_critical
    (rho : RiemannNontrivialZeroIndexV2) :
    ‖zeroSliceFactor rho 2 1‖ = 1 ↔ rho.1.re = 1 / 2 :=
  zeroSliceFactor_unit_iff_critical rho 2 1
    (ne_of_gt fsLogSlice_two_one_fs_pos)

/-- Actual, source-defined smooth Weil packet at a given time slice. -/
def timeSlicePacket
    (g : WeilCompactSmoothGV1) (p : ℝ) (ticks : ℤ) :
    WeilCompactSmoothGV1 :=
  translatePacket g (fsLogSlice p ticks)

/-- Exact Mellin transport on the actual time-sliced Weil packet. -/
theorem timeSlice_mellin
    (g : WeilCompactSmoothGV1) (s : ℂ) (p : ℝ) (ticks : ℤ) :
    mellin (timeSlicePacket g p ticks).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) *
        (fsLogSlice p ticks : ℂ)) * mellin g.1 s := by
  exact mellin_translatePacket_v11 g (fsLogSlice p ticks) s

/-- Both repository moment annihilations survive each actual slice. -/
theorem timeSlice_moments
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (p : ℝ) (ticks : ℤ) :
    WeilMomentConditionsV1 (timeSlicePacket g p ticks) :=
  translate_preserves_moments g (fsLogSlice p ticks) hm

/-- The original L2 energy survives each actual time slice exactly. -/
theorem timeSlice_energy
    (g : WeilCompactSmoothGV1) (p : ℝ) (ticks : ℤ) :
    energy (timeSlicePacket g p ticks).1 = energy g.1 :=
  translate_energy g (fsLogSlice p ticks)

/-- Eight time slices, including nonuniform and repeated integer times. -/
def timeSliceEight
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 8 → ℤ) : Fin 8 → WeilCompactSmoothGV1 :=
  fun i => timeSlicePacket g p (ticks i)

/-- All eight component packets retain the TWO moment annihilations. -/
theorem timeSliceEight_moments
    (g : WeilCompactSmoothGV1) (p : ℝ) (ticks : Fin 8 → ℤ)
    (hm : WeilMomentConditionsV1 g) :
    ∀ i : Fin 8, WeilMomentConditionsV1 (timeSliceEight g p ticks i) := by
  intro i
  exact timeSlice_moments g hm p (ticks i)

/-- ALL 64 genuine B coefficients survive the exact time-slice Gram.
No hypothesis that off-diagonal temporal interference vanishes. -/
theorem timeSliceEight_actual_full_gram
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 8 → ℤ) (z : Fin 8 → ℂ) :
    B (packetSum z (timeSliceEight g p ticks))
        (packetSum z (timeSliceEight g p ticks)) =
      ∑ i : Fin 8, ∑ j : Fin 8,
        z i * star (z j) *
          B (timeSlicePacket g p (ticks i))
            (timeSlicePacket g p (ticks j)) := by
  simpa only [timeSliceEight] using
    (B_packetSum z (timeSliceEight g p ticks))

/-- The original Bagua complement four-sector decomposition now
applies to the actual time-sliced Weil packets: ++, --, +- and -+.
Neither mixed complementary block is silently discarded. -/
theorem timeSliceEight_bagua_four_sector
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 8 → ℤ) (z : Fin 8 → ℂ) :
    B (packetSum z (baguaMode (timeSliceEight g p ticks)))
        (packetSum z (baguaMode (timeSliceEight g p ticks))) =
      baguaGramBilinear (timeSliceEight g p ticks)
          (baguaPlus z) (baguaPlus z) +
      baguaGramBilinear (timeSliceEight g p ticks)
          (baguaMinus z) (baguaMinus z) +
      baguaGramBilinear (timeSliceEight g p ticks)
          (baguaPlus z) (baguaMinus z) +
      baguaGramBilinear (timeSliceEight g p ticks)
          (baguaMinus z) (baguaPlus z) := by
  exact bagua_actual_weil_four_sector_identity
    (timeSliceEight g p ticks) z

end AEGIS.RHTimeSliceWeilV1

#print axioms AEGIS.RHTimeSliceWeilV1.fsLogSlice_add
#print axioms AEGIS.RHTimeSliceWeilV1.fsLogSlice_one_second
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_add
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_norm
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_two_one_fs_iff_critical
#print axioms AEGIS.RHTimeSliceWeilV1.timeSlice_mellin
#print axioms AEGIS.RHTimeSliceWeilV1.timeSlice_moments
#print axioms AEGIS.RHTimeSliceWeilV1.timeSlice_energy
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceEight_actual_full_gram
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceEight_bagua_four_sector
