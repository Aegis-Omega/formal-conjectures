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
import AEGISOverlay.RHFixedPacketDenseShiftV1
import AEGISOverlay.RHNarrowFixedDetectorV1
import AEGISOverlay.RHArchRow29V1

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

open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHTimeSliceWeilV1

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
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


/-! ## Exact angular coordinate of the actual zeta-zero time slice

The spectral angle is Im(rho) times the *declared* real logarithmic shift.
The radius is exp((Re(rho)-1/2)*shift). Both are SOURCE-EXACT and do not
assert that physical time is logarithmic. The phase-angle law alone does
not imply any universal arithmetic sign.
-/

/-- Unwrapped phase, in radians, of an actual zero's spectral time slice. -/
def zeroSliceAngle
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) : ℝ :=
  rho.1.im * fsLogSlice p ticks

/-- Exact phase addition for any two signed integer time intervals. -/
theorem zeroSliceAngle_add
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (a b : ℤ) :
    zeroSliceAngle rho p (a + b) =
      zeroSliceAngle rho p a + zeroSliceAngle rho p b := by
  simp only [zeroSliceAngle, fsLogSlice_add]
  ring

/-- The real component is the precise spiral radius times cos(angle). -/
theorem zeroSliceFactor_re
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) :
    (zeroSliceFactor rho p ticks).re =
      Real.exp ((rho.1.re - 1 / 2) * fsLogSlice p ticks) *
        Real.cos (zeroSliceAngle rho p ticks) := by
  have hre :
      ((rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p ticks : ℂ)).re =
        (rho.1.re - 1 / 2) * fsLogSlice p ticks := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
  have him :
      ((rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p ticks : ℂ)).im =
        rho.1.im * fsLogSlice p ticks := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    norm_num
  unfold zeroSliceFactor WeilZeroTranslationFactorV11
  rw [Complex.exp_re, hre, him]
  rfl

/-- The imaginary component is the precise spiral radius times sin(angle). -/
theorem zeroSliceFactor_im
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) :
    (zeroSliceFactor rho p ticks).im =
      Real.exp ((rho.1.re - 1 / 2) * fsLogSlice p ticks) *
        Real.sin (zeroSliceAngle rho p ticks) := by
  have hre :
      ((rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p ticks : ℂ)).re =
        (rho.1.re - 1 / 2) * fsLogSlice p ticks := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
  have him :
      ((rho.1 - (1 / 2 : ℂ)) * (fsLogSlice p ticks : ℂ)).im =
        rho.1.im * fsLogSlice p ticks := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    norm_num
  unfold zeroSliceFactor WeilZeroTranslationFactorV11
  rw [Complex.exp_im, hre, him]
  rfl

/-- Full polar reconstruction of the source-defined complex time slice. -/
theorem zeroSliceFactor_polar
    (rho : RiemannNontrivialZeroIndexV2) (p : ℝ) (ticks : ℤ) :
    zeroSliceFactor rho p ticks =
      (Real.exp ((rho.1.re - 1 / 2) * fsLogSlice p ticks) : ℂ) *
        ((Real.cos (zeroSliceAngle rho p ticks) : ℂ) +
          (Real.sin (zeroSliceAngle rho p ticks) : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [zeroSliceFactor_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · rw [zeroSliceFactor_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

/-- Mellin transport at any actual zero retains BOTH radius and phase. -/
theorem timeSlice_mellin_at_zero_polar
    (g : WeilCompactSmoothGV1) (rho : RiemannNontrivialZeroIndexV2)
    (p : ℝ) (ticks : ℤ) :
    mellin (timeSlicePacket g p ticks).1 rho.1 =
      (Real.exp ((rho.1.re - 1 / 2) * fsLogSlice p ticks) : ℂ) *
        ((Real.cos (zeroSliceAngle rho p ticks) : ℂ) +
          (Real.sin (zeroSliceAngle rho p ticks) : ℂ) * Complex.I) *
        mellin g.1 rho.1 := by
  calc
    mellin (timeSlicePacket g p ticks).1 rho.1 =
        zeroSliceFactor rho p ticks * mellin g.1 rho.1 := by
          simpa [zeroSliceFactor, WeilZeroTranslationFactorV11] using
            (timeSlice_mellin g rho.1 p ticks)
    _ = _ := by rw [zeroSliceFactor_polar]

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


/-! ## Eight Bagua layers, 64-way branching, and exact Q16.16 arithmetic

Exponentiation is right-associative: 64^(2^3) = 64^8 = 2^48.
The same cardinality equals (2^16)^3 = 65536^3, the denominator
of a product of THREE unrounded Q16.16 rational factors. This is a
finite combinatorial/denominator identity; it is not a proof that
every state carries an admissible actual Weil sign certificate.

The spectral cocycle below applies to ANY FINITE number of slices,
not merely the 64^8-indexed collection. This algebraic universality
must not be confused with universal arithmetic Gram coercivity. -/

/-- 8 layers, each with 64 choices: exactly 2^48 states. -/
theorem bagua_time_64_pow_2_pow_3 :
    (64 : ℕ) ^ (2 ^ 3) = 281474976710656 := by
  norm_num

/-- The 2^48 cardinality is exactly three unrounded Q16.16
denominators, with no floating point or tick truncation. -/
theorem bagua_time_64_pow_2_pow_3_q16 :
    (64 : ℕ) ^ (2 ^ 3) = (65536 : ℕ) ^ 3 := by
  norm_num

/-- Three stages of fixed-point rational factors compose over the
EXACT rational denominator 64^(2^3), not over a rounded Q16.16 result. -/
theorem bagua_time_three_exact_q16_product (a b c : ℤ) :
    ((a : ℚ) / 65536) * ((b : ℚ) / 65536) *
      ((c : ℚ) / 65536) =
      (((a * b * c : ℤ) : ℚ) / ((64 : ℕ) ^ (2 ^ 3) : ℕ)) := by
  norm_num [Int.cast_mul]
  ring

/-- Exact temporal composition for an ARBITRARY finite list of signed
femtosecond intervals. No maximum slice count is assumed. -/
theorem fsLogSlice_list_sum (p : ℝ) (ticks : List ℤ) :
    fsLogSlice p ticks.sum = (ticks.map (fsLogSlice p)).sum := by
  induction ticks with
  | nil => simp [fsLogSlice_zero]
  | cons t ts ih =>
    simp [fsLogSlice_add, ih]

/-- Exact zero-spectrum multiplicative cocycle for an ARBITRARY finite
number of ordered slices, without combining or rounding phase factors.
This has no assumption of RH and implies no global Weil sign. -/
theorem zeroSliceFactor_list_product
    (rho : RiemannNontrivialZeroIndexV2)
    (p : ℝ) (ticks : List ℤ) :
    zeroSliceFactor rho p ticks.sum =
      (ticks.map (zeroSliceFactor rho p)).prod := by
  induction ticks with
  | nil => simp [zeroSliceFactor_zero]
  | cons t ts ih =>
    simp [zeroSliceFactor_add, ih]


/-! ## Arbitrarily many actual time slices in a common certified window

This lifts the previously source-proved full-weighted genuine Weil Gram
margin to n+1 time-sliced translates of ONE arbitrary moment-zero seed.
Unlike the eight-dimensional Bagua showcase, n is unrestricted.

The width hypothesis is DERIVED from the source seed support and explicit
bounds on the slice centers. In particular, the inter-slice B entries are
not assumed small or discarded: all (n+1)^2 genuine mixed coefficients
are retained exactly by the imported Trigram theorem.

The center-span condition remains load-bearing: it does not assert
global arithmetic positivity outside the common 2/5 log window. -/

/-- Actual source packets along an arbitrary finite sequence of signed
integer femtosecond offsets. -/
def timeSliceFamily {n : ℕ}
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin (n + 1) → ℤ) :
    Fin (n + 1) → WeilCompactSmoothGV1 :=
  fun i => timeSlicePacket g p (ticks i)

/-- Moment-zero annihilations are valid for every sliced component. -/
theorem timeSliceFamily_moments {n : ℕ}
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (hm : WeilMomentConditionsV1 g) :
    ∀ i, WeilMomentConditionsV1 (timeSliceFamily g p ticks i) := by
  intro i
  exact timeSlice_moments g hm p (ticks i)

/-- Each component inherits an actual common Trigram support bound
if its exact log-time shift lies within the certified center span.
The per-slice base radius is 1/256, leaving 507/1280 of center slack. -/
theorem timeSliceFamily_common_window {n : ℕ}
    (g : WeilCompactSmoothGV1) (p origin center : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256) origin)
    (hspan : ∀ i, |origin + fsLogSlice p (ticks i) - center| ≤
      (507 / 1280 : ℝ)) :
    ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (timeSliceFamily g p ticks i) (2 / 5) center := by
  intro i
  let d : ℝ := fsLogSlice p (ticks i)
  have htranslated :
      AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
        (timeSliceFamily g p ticks i)
        ((origin - 1 / 256) + d) ((origin + 1 / 256) + d) := by
    change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (translatePacket g d)
      ((origin - 1 / 256) + d) ((origin + 1 / 256) + d)
    exact translate_logSupportIn g d (origin - 1 / 256)
      (origin + 1 / 256) hw
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (timeSliceFamily g p ticks i)
    (center - 2 / 5) (center + 2 / 5)
  intro x hx
  have h := htranslated hx
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hspan i)
  change -(507 / 1280 : ℝ) ≤ origin + d - center at hlo
  change origin + d - center ≤ (507 / 1280 : ℝ) at hhi
  constructor <;> linarith [h.1, h.2]

/-- ACTUAL full Weil Gram, valid for arbitrarily many time slices,
including every complex-weighted off-diagonal entry. -/
theorem timeSliceFamily_full_gram {n : ℕ}
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (z : Fin (n + 1) → ℂ) :
    B (packetSum z (timeSliceFamily g p ticks))
      (packetSum z (timeSliceFamily g p ticks)) =
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      z i * star (z j) *
        B (timeSliceFamily g p ticks i)
          (timeSliceFamily g p ticks j) := by
  exact B_packetSum z (timeSliceFamily g p ticks)

/-- Proven Trigram 1/16 energy margin for ALL (n+1)^2 genuine
mixed coefficients, now carried by arbitrary exact femtosecond
time slices within the common certified log support. -/
theorem timeSliceFamily_full_weighted_margin {n : ℕ}
    (g : WeilCompactSmoothGV1) (p origin center : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (z : Fin (n + 1) → ℂ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256) origin)
    (hspan : ∀ i, |origin + fsLogSlice p (ticks i) - center| ≤
      (507 / 1280 : ℝ)) :
    (1 / 16 : ℝ) *
      energy (packetSum z (timeSliceFamily g p ticks)).1 ≤
      -(∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          z i * star (z j) *
            B (timeSliceFamily g p ticks i)
              (timeSliceFamily g p ticks j)).re := by
  exact AEGIS.RHActualNarrowGramSignV1.trigram_full_weighted_gram_margin
    n z (timeSliceFamily g p ticks) center
    (timeSliceFamily_moments g p ticks hm)
    (timeSliceFamily_common_window g p origin center ticks hw hspan)


/-! ## Two exact femtosecond channels form a dense spectral sampling group

A single fixed femtosecond step at p = 2 samples log 2 / 10^15.
At p = 3 it samples log 3 / 10^15. Their ratio is irrational,
hence the additive group that both generate is dense in real log-time.
This is a theorem about LOGARITHMIC SPECTRAL coordinates, not an
assertion that physical clocks have infinite resolution.

The sign criterion below uses the actual source Weil two-point test
of a fixed moment-zero packet. Density plus proven continuity turns
positivity at these exact discrete coordinates into positivity at
ALL real shifts. The global four-phase sign on the discrete group
remains an explicit, mathematically substantial hypothesis. -/

def fsTwoThreeShiftGroup : AddSubgroup ℝ :=
  AddSubgroup.closure {fsLogSlice 2 1, fsLogSlice 3 1}

/-- Rational rescaling by one femtosecond does not change the
irrational ratio of the two prime-logarithmic sampling steps. -/
theorem fsTwoThree_slice_ratio :
    fsLogSlice 2 1 / fsLogSlice 3 1 =
      Real.log 2 / Real.log 3 := by
  have h3 : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  unfold fsLogSlice
  norm_num only [Int.cast_one]
  field_simp [h3]

/-- The two exact integer-femtosecond sampling channels generate
a dense additive subgroup of the real spectral translation axis. -/
theorem fsTwoThreeShiftGroup_dense :
    Dense (fsTwoThreeShiftGroup : Set ℝ) := by
  unfold fsTwoThreeShiftGroup
  apply (dense_addSubgroupClosure_pair_iff).mpr
  rw [fsTwoThree_slice_ratio]
  exact RHSnowflakeLog23.irrational_log_two_div_log_three

/-- Actual four-phase Weil arithmetic sign of the fixed detecting
packet restricted to the dense femtosecond/log2/log3 subgroup. -/
def FsTwoThreeDetectorSign : Prop :=
  ∀ d : ℝ, d ∈ fsTwoThreeShiftGroup →
    ∀ c : ℂ, WeilFourPhaseV1 c →
      (WeilExplicitRightSideV1
        (WeilAutocorrelationV1
          (WeilTwoPointTranslateV11
            AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket d c))).re ≤ 0

/-- Dense spectral sampling preserves the complete four-phase
test under the ACTUAL Weil kernel continuity. This does not
assert that the sampled values are sign-correct. -/
theorem fsTwoThree_detector_sign_implies_all_shifts
    (h : FsTwoThreeDetectorSign) :
    AEGIS.RHFixedPacketFourPhaseV1.FixedPacketFourPhaseSignV1
      AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket := by
  let g := AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket
  have hm : WeilMomentConditionsV1 g :=
    AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_moments
  intro d c hc
  let Q : ℝ → ℝ := fun x =>
    WeilTwoPointValueV1
      (WeilAutocorrelationZeroQuadraticV11 g).re
      (WeilZeroTranslationKernelV11 g x) c
  have hcontinuous : Continuous Q :=
    AEGIS.RHFixedPacketDenseShiftV1.translated_four_phase_value_continuous g c
  have hset : IsClosed {x : ℝ | 0 ≤ Q x} :=
    isClosed_Ici.preimage hcontinuous
  have hsubset : (fsTwoThreeShiftGroup : Set ℝ) ⊆ {x : ℝ | 0 ≤ Q x} := by
    intro x hx
    have hmx := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      g x c hm
    have hzero : 0 ≤
        (WeilAutocorrelationZeroQuadraticV11
          (WeilTwoPointTranslateV11 g x c)).re :=
      (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        (WeilTwoPointTranslateV11 g x c) hmx).mp (h x hx c hc)
    change 0 ≤ Q x
    rw [AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
      g hm x c] at hzero
    exact hzero
  have hclosed : closure (fsTwoThreeShiftGroup : Set ℝ) ⊆
      {x : ℝ | 0 ≤ Q x} := closure_minimal hsubset hset
  have hQ : 0 ≤ Q d := by
    apply hclosed
    rw [fsTwoThreeShiftGroup_dense.closure_eq]
    trivial
  apply (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    (WeilTwoPointTranslateV11 g d c)
    (AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      g d c hm)).mpr
  change 0 ≤ (WeilAutocorrelationZeroQuadraticV11
    (WeilTwoPointTranslateV11 g d c)).re
  rw [AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    g hm d c]
  exact hQ

/-- Exact RH consumer of the dense two-prime femtosecond sampling
criterion, with the global sign premise plainly visible. -/
theorem riemannHypothesis_of_fsTwoThreeDetectorSign
    (h : FsTwoThreeDetectorSign) : RiemannHypothesis :=
  AEGIS.RHNarrowFixedDetectorV1.riemannHypothesis_of_narrow_four_phase_sign
    (fsTwoThree_detector_sign_implies_all_shifts h)

/-- Conversely, RH implies the actual signed tests on every
femtosecond sampled shift. Neither direction is a claim of
an unconditional RH theorem. -/
theorem fsTwoThreeDetectorSign_of_riemannHypothesis
    (h : RiemannHypothesis) : FsTwoThreeDetectorSign := by
  intro d _hd c _hc
  let g := AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket
  have hm :=
    AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      g d c AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_moments
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    (WeilTwoPointTranslateV11 g d c) hm).mpr
    (AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13
      h (WeilTwoPointTranslateV11 g d c) hm)

theorem fsTwoThreeDetectorSign_iff_riemannHypothesis :
    FsTwoThreeDetectorSign ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_fsTwoThreeDetectorSign,
    fsTwoThreeDetectorSign_of_riemannHypothesis⟩


/-! ## Genuine von Mangoldt signed-prime/Arch-29 bridge for time layers

The exact time-slice family inherits the source fine support and two
vanishing moments. For ORDERED, separated time layers the existing
moment-zero Arch theorem bounds the full infinite geometric row by
29 / 65536, uniformly in n. We therefore preserve the signed REAL
prime-row allowance 57401 / 65536, without taking absolute values
of favorable negative prime interference.

This is an actual Weil coercivity theorem for every finite n WITH
the genuine prime cost and its row budget supplied as explicit
hypotheses. It does not fabricate a global signed-prime producer,
a far-separated exact reconstruction of all compact packets, or RH. -/

/-- Full source Weil coercivity on an arbitrary-size family of
exact signed-femtosecond spectral slices, with a SIGNED prime row
rather than a norm-based prime row. The only additional analytic
input is the explicit actual von Mangoldt estimate. -/
theorem timeSliceFamily_signed_prime_arch29 {n : ℕ}
    (g : WeilCompactSmoothGV1) (p origin : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      g origin)
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤
        fsLogSlice p (ticks j) - fsLogSlice p (ticks i))
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      (WeilPrimeSumV1
        (mixed (timeSliceFamily g p ticks i)
          (timeSliceFamily g p ticks j))).re ≤
        primeCost i j *
          (energy (timeSliceFamily g p ticks i).1 +
            energy (timeSliceFamily g p ticks j).1))
    (hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ (57401 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) (timeSliceFamily g p ticks))
       (packetSum (fun _ => (1 : ℂ)) (timeSliceFamily g p ticks))).re ≤
      -(641 / 32768 : ℝ) *
        (∑ i, energy (timeSliceFamily g p ticks i).1) := by
  let centers : Fin (n + 1) → ℝ :=
    fun i => origin + fsLogSlice p (ticks i)
  have hwFamily : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (timeSliceFamily g p ticks i) (centers i) := by
    intro i
    have htranslated := translate_logSupportIn g
      (fsLogSlice p (ticks i))
      (origin - 1 / 256) (origin + 1 / 256) hw
    change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (translatePacket g (fsLogSlice p (ticks i)))
      (origin + fsLogSlice p (ticks i) - 1 / 256)
      (origin + fsLogSlice p (ticks i) + 1 / 256)
    convert htranslated using 1 <;> ring
  have hsepFamily : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ centers j - centers i := by
    intro i j hij
    obtain ⟨hpositive, hgap⟩ := hsep i j hij
    refine ⟨hpositive, ?_⟩
    dsimp [centers]
    linarith
  exact AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_signed_prime_arch29_row
    (timeSliceFamily g p ticks) centers hwFamily
    (timeSliceFamily_moments g p ticks hm)
    hsepFamily primeCost hsym hprime hprimeRow

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
#print axioms AEGIS.RHTimeSliceWeilV1.bagua_time_64_pow_2_pow_3
#print axioms AEGIS.RHTimeSliceWeilV1.bagua_time_64_pow_2_pow_3_q16
#print axioms AEGIS.RHTimeSliceWeilV1.bagua_time_three_exact_q16_product
#print axioms AEGIS.RHTimeSliceWeilV1.fsLogSlice_list_sum
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_list_product
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceFamily_moments
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceFamily_common_window
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_gram
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin
#print axioms AEGIS.RHTimeSliceWeilV1.fsTwoThree_slice_ratio
#print axioms AEGIS.RHTimeSliceWeilV1.fsTwoThreeShiftGroup_dense
#print axioms AEGIS.RHTimeSliceWeilV1.fsTwoThree_detector_sign_implies_all_shifts
#print axioms AEGIS.RHTimeSliceWeilV1.riemannHypothesis_of_fsTwoThreeDetectorSign
#print axioms AEGIS.RHTimeSliceWeilV1.fsTwoThreeDetectorSign_of_riemannHypothesis
#print axioms AEGIS.RHTimeSliceWeilV1.fsTwoThreeDetectorSign_iff_riemannHypothesis

#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceAngle_add
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_re
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_im
#print axioms AEGIS.RHTimeSliceWeilV1.zeroSliceFactor_polar
#print axioms AEGIS.RHTimeSliceWeilV1.timeSlice_mellin_at_zero_polar
#print axioms AEGIS.RHTimeSliceWeilV1.timeSliceFamily_signed_prime_arch29
