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
import WeilH64AssemblyV7
import WeilLogTransportCanonicalV1

/-!
# OPTIMUS V7: the packet class is not empty

V7 §4, formalized. For every centre `c`, `pkt c` is a smooth compactly supported packet on the
positive half-line whose logarithmic lift lives in `[c − 1/4096, c + 1/4096]`, with energy `1` and
**both repository moments zero** (`WeilMomentConditionsV1`). It is `k · mulPacket (momentKiller ψ)`,
`ψ` a smooth bump of outer radius `1/4096` at `c` (the moment killer `ψ' + ψ''` of
`WeilMomentKillerConstructionV1`; it is not zero because `ψ` is not).

`h64_nonvacuous`: the 64 packets `pkt (ctr x)` satisfy every hypothesis of `h64_coercive`, so the V7
coercivity holds on a genuine 64-dimensional space of moment-zero test packets. Not RH.
-/

open Set Function MeasureTheory Complex Metric
open scoped ComplexConjugate BigOperators ContDiff

noncomputable section

namespace AEGIS.WeilH64WitnessV7

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilLogTransportCanonicalV1
open AEGIS.WeilH64DiagonalV7
open AEGIS.WeilH64AssemblyV7

/-- The seed bump at `c` (outer radius `1/4096`). -/
def bmp (c : ℝ) : ContDiffBump c := ⟨1 / 8192, 1 / 4096, by norm_num, by norm_num⟩

def psi (c : ℝ) : ℝ → ℝ := fun u => bmp c u

/-- The moment-killed seed. -/
def phi (c : ℝ) : ℝ → ℝ := momentKiller (psi c)

theorem psi_contDiff (c : ℝ) : ContDiff ℝ ∞ (psi c) := (bmp c).contDiff

theorem psi_tsupport (c : ℝ) : tsupport (psi c) = closedBall c (1 / 4096) := (bmp c).tsupport_eq

theorem psi_hasCompactSupport (c : ℝ) : HasCompactSupport (psi c) := by
  rw [HasCompactSupport, psi_tsupport]; exact isCompact_closedBall _ _

theorem phi_tsupport (c : ℝ) : tsupport (phi c) ⊆ Icc (c - 1 / 4096) (c + 1 / 4096) := by
  refine (tsupport_momentKiller_subset (psi c)).trans ?_
  rw [psi_tsupport, Real.closedBall_eq_Icc]

theorem phi_zero_of_not_mem {c u : ℝ} (hu : u ∉ Icc (c - 1 / 4096) (c + 1 / 4096)) : phi c u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hu (phi_tsupport c h)

theorem phi_zero_below (c : ℝ) : ∀ u ≤ c - 1 / 2048, phi c u = 0 := fun u hu =>
  phi_zero_of_not_mem fun h => by linarith [h.1]

theorem phi_zero_above (c : ℝ) : ∀ u, c + 1 / 2048 ≤ u → phi c u = 0 := fun u hu =>
  phi_zero_of_not_mem fun h => by linarith [h.2]

theorem phi_contDiff (c : ℝ) : ContDiff ℝ ∞ (phi c) := momentKiller_contDiff (psi_contDiff c)

theorem phi_continuous (c : ℝ) : Continuous (phi c) := (phi_contDiff c).continuous

theorem phi_ne_zero (c : ℝ) : ∃ u, phi c u ≠ 0 := by
  by_contra h
  have h0 : phi c = 0 := funext fun u => not_not.mp fun hu => h ⟨u, hu⟩
  have := eq_zero_of_momentKiller_eq_zero (psi_contDiff c) (psi_hasCompactSupport c) h0 c
  have h1 : psi c c = 1 := (bmp c).one_of_mem_closedBall (mem_closedBall_self (bmp c).rIn_pos.le)
  rw [h1] at this
  norm_num at this

/-- The log-lift mass `∫ eᵘ φ(u)² du`. -/
def mass (c : ℝ) : ℝ := ∫ u, Real.exp u * phi c u ^ 2

theorem mass_pos (c : ℝ) : 0 < mass c := by
  obtain ⟨u0, hu0⟩ := phi_ne_zero c
  have hcont : Continuous fun u => Real.exp u * phi c u ^ 2 :=
    Real.continuous_exp.mul ((phi_continuous c).pow 2)
  have hcs : HasCompactSupport fun u => Real.exp u * phi c u ^ 2 := by
    have : HasCompactSupport (phi c) := momentKiller_hasCompactSupport (psi_hasCompactSupport c)
    have h2 : HasCompactSupport (Real.exp * (phi c * phi c)) := this.mul_left.mul_left
    convert h2 using 1
    funext u
    simp [Pi.mul_apply, sq]
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun u => by positivity) (by positivity)

/-- The normalising constant. -/
def kk (c : ℝ) : ℝ := (Real.sqrt (mass c))⁻¹

/-- The real packet `k · mulPacket φ`. -/
def pktR (c : ℝ) : ℝ → ℝ := fun x => kk c * mulPacket (phi c) x

theorem pktR_contDiff (c : ℝ) : ContDiff ℝ ∞ (pktR c) :=
  contDiff_const.mul (mulPacket_contDiff (phi_contDiff c) (phi_zero_below c))

theorem pktR_tsupport (c : ℝ) :
    tsupport (pktR c) ⊆ Icc (Real.exp (c - 1 / 2048)) (Real.exp (c + 1 / 2048)) := by
  refine (tsupport_mul_subset_right (f := fun _ => kk c)).trans ?_
  exact tsupport_mulPacket_subset (phi_zero_below c) (phi_zero_above c)

/-- **The witness packet.** -/
def pkt (c : ℝ) : WeilCompactSmoothGV1 :=
  ⟨fun x => ((pktR c x : ℝ) : ℂ),
    Complex.ofRealCLM.contDiff.comp (pktR_contDiff c),
    by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc
        (a := Real.exp (c - 1 / 2048)) (b := Real.exp (c + 1 / 2048))) ?_
      intro x hx
      have : pktR c x ≠ 0 := fun h => hx (by simp [h])
      exact pktR_tsupport c (subset_tsupport _ this),
    by
      intro x hx
      have hsub : tsupport (fun x => ((pktR c x : ℝ) : ℂ)) ⊆ tsupport (pktR c) :=
        tsupport_comp_subset Complex.ofReal_zero (pktR c)
      exact lt_of_lt_of_le (Real.exp_pos _) (pktR_tsupport c (hsub hx)).1⟩

theorem logLift_pkt (c t : ℝ) :
    logLift (pkt c).1 t = ((kk c * (Real.exp (t / 2) * phi c t) : ℝ) : ℂ) := by
  change (Real.exp (t / 2) : ℂ) * ((kk c * mulPacket (phi c) (Real.exp t) : ℝ) : ℂ) = _
  rw [mulPacket_of_pos (Real.exp_pos t), Real.log_exp]
  push_cast
  ring

/-- The log support. -/
theorem pkt_logRadius (c : ℝ) : LogRadiusAt (pkt c) c (1 / 4096) := by
  intro t ht
  by_contra hnot
  have h0 : ∀ s ∉ Icc (c - 1 / 4096) (c + 1 / 4096), logLift (pkt c).1 s = 0 := fun s hs => by
    rw [logLift_pkt, phi_zero_of_not_mem hs]; simp
  have hsub : tsupport (logLift (pkt c).1) ⊆ Icc (c - 1 / 4096) (c + 1 / 4096) :=
    closure_minimal (fun s hs => by
      by_contra h; exact hs (h0 s h)) isClosed_Icc
  exact hnot (hsub ht)

/-- Energy one. -/
theorem pkt_energy (c : ℝ) : energy (pkt c).1 = 1 := by
  rw [← logLift_energy_eq_packet_energy]
  have hpt : ∀ t, ‖logLift (pkt c).1 t‖ ^ 2 = kk c ^ 2 * (Real.exp t * phi c t ^ 2) := by
    intro t
    rw [logLift_pkt, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have : Real.exp (t / 2) ^ 2 = Real.exp t := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, this]
  simp_rw [hpt]
  rw [integral_const_mul]
  change kk c ^ 2 * mass c = 1
  unfold kk
  rw [inv_pow, Real.sq_sqrt (mass_pos c).le, inv_mul_cancel₀ (mass_pos c).ne']

/-- **Both repository moments vanish.** -/
theorem pkt_moments (c : ℝ) : WeilMomentConditionsV1 (pkt c) := by
  have hm1 := integral_momentKiller (psi_contDiff c) (psi_hasCompactSupport c)
  have hm2 := integral_momentKiller_mul_exp (psi_contDiff c) (psi_hasCompactSupport c)
  have h1 := integral_mulPacket_inv (phi_continuous c) (phi_zero_below c) (phi_zero_above c)
  have h2 := integral_mulPacket (phi_continuous c) (phi_zero_below c) (phi_zero_above c)
  constructor
  · have e : ∀ x : ℝ, (pkt c).1 x / (x : ℂ) = ((kk c * (x⁻¹ * mulPacket (phi c) x) : ℝ) : ℂ) := by
      intro x
      change ((kk c * mulPacket (phi c) x : ℝ) : ℂ) / (x : ℂ) = _
      push_cast
      ring
    simp_rw [e]
    rw [integral_complex_ofReal, integral_const_mul, h1]
    change ((kk c * ∫ u, momentKiller (psi c) u : ℝ) : ℂ) = 0
    rw [hm1]; simp
  · change (∫ x in Ioi (0 : ℝ), ((kk c * mulPacket (phi c) x : ℝ) : ℂ)) = 0
    rw [integral_complex_ofReal, integral_const_mul, h2]
    change ((kk c * ∫ u, momentKiller (psi c) u * Real.exp u : ℝ) : ℂ) = 0
    rw [hm2]; simp

/-- **V7 is not vacuous**: 64 moment-zero packets meeting every hypothesis of `h64_coercive`. -/
theorem h64_nonvacuous :
    ∃ g : Idx → WeilCompactSmoothGV1,
      (∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096)) ∧ (∀ x, energy (g x).1 = 1) ∧
      (∀ x, WeilMomentConditionsV1 (g x)) ∧
      ∀ z : Idx → ℂ, (1475 / 6144 : ℝ) * ∑ x, ‖z x‖ ^ 2 ≤
        (∑ x, ∑ y, z x * (-AEGIS.WeilMixedAlgebraV2.B (g x) (g y)) * conj (z y)).re :=
  ⟨fun x => pkt (ctr x), fun _ => pkt_logRadius _, fun _ => pkt_energy _, fun _ => pkt_moments _,
    h64_coercive _ (fun _ => pkt_logRadius _) (fun _ => pkt_energy _)⟩

end AEGIS.WeilH64WitnessV7

#print axioms AEGIS.WeilH64WitnessV7.pkt_energy
#print axioms AEGIS.WeilH64WitnessV7.pkt_moments
#print axioms AEGIS.WeilH64WitnessV7.h64_nonvacuous
