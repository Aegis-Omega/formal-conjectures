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

import WeilSeparatedArchL1BridgeV32

/-!
AEGIS Ω — distance-dependent log-free row charge on a lattice of centres (Claude Lab, 2026-11-21).

`RHPrimeFreeRecompositionJoinV1.combinedFineCost` charges every log-free pair of width-1/128 atoms the same
constant `676/65536`, and `eighty_five_log_free_links_exceed_fixed_row_budget` records that 85 such links already
exceed the row budget `57430/65536`. On a log-free pair the prime sum vanishes and the Weil entry is the
Archimedean term alone. By `WeilSeparatedArchL1BridgeV32.distinct_arch_norm_bound_gap_l1` (with `w = 1/128`), the
pair at centre distance `d` costs at most `R(d - 1/128)/256` per unit of `E(p) + E(q)`, with
`R(δ) = e^{-5δ/2}/(1 - e^{-2δ})`. This charge decays geometrically in `d`.

This module proves that, for centres on a lattice of spacing `1/192`, the distance-dependent charges of one row
sum to at most `4/5 < 57430/65536`, whatever the length of the row. The only condition is that every
charged offset satisfies `|d| ≥ 53` (that is, `d/192 ≥ 35/128`, the left end of `FineLogFreeGap`).

Pure real analysis on the kernel `archRemainderV32`; no partition, prime sum or Weil sign is used. Not RH.
-/

open Finset
set_option autoImplicit false
noncomputable section
namespace AEGIS.RHLogFreeRowDecayV1

open AEGIS.WeilSeparatedArchL1BridgeV32

theorem exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x + x ^ 2 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

/-- Geometric domination of the remainder kernel on the lattice `m/192`, `m ≥ 53`. -/
theorem archRemainder_le_geom (m : ℕ) (hm : 53 ≤ m) :
    archRemainderV32 ((m : ℝ) / 192 - 1 / 128) ≤
      Real.exp (-(515 / 768)) / (1 - Real.exp (-(103 / 192))) *
        Real.exp (-(5 / 384)) ^ (m - 53) := by
  unfold archRemainderV32
  have hm' : (53 : ℝ) ≤ m := by exact_mod_cast hm
  have hmk : ((m - 53 : ℕ) : ℝ) = (m : ℝ) - 53 := by
    rw [Nat.cast_sub hm]
    norm_num
  have hnum : Real.exp (-5 * ((m : ℝ) / 192 - 1 / 128) / 2) =
      Real.exp (-(515 / 768)) * Real.exp (-(5 / 384)) ^ (m - 53) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hmk]
    ring
  have hden0 : 0 < 1 - Real.exp (-(103 / 192)) := by
    have h : Real.exp (-(103 / 192 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hden : 1 - Real.exp (-(103 / 192)) ≤ 1 - Real.exp (-2 * ((m : ℝ) / 192 - 1 / 128)) := by
    have h : Real.exp (-2 * ((m : ℝ) / 192 - 1 / 128)) ≤ Real.exp (-(103 / 192)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [hnum]
  calc Real.exp (-(515 / 768)) * Real.exp (-(5 / 384)) ^ (m - 53) /
        (1 - Real.exp (-2 * ((m : ℝ) / 192 - 1 / 128)))
      ≤ Real.exp (-(515 / 768)) * Real.exp (-(5 / 384)) ^ (m - 53) /
          (1 - Real.exp (-(103 / 192))) :=
        div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = Real.exp (-(515 / 768)) / (1 - Real.exp (-(103 / 192))) *
          Real.exp (-(5 / 384)) ^ (m - 53) := by ring

theorem sum_geom_le_of_injOn {ι : Type*} (T : Finset ι) (φ : ι → ℕ) (hφ : Set.InjOn φ T)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ T, q ^ φ j ≤ 1 / (1 - q) := by
  classical
  rw [← Finset.sum_image (f := fun k => q ^ k) hφ]
  calc ∑ k ∈ T.image φ, q ^ k ≤ ∑' k, q ^ k :=
        (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
    _ = 1 / (1 - q) := by rw [tsum_geometric_of_lt_one hq0 hq1, one_div]

/-- **Row bound.** For any finite set of lattice offsets `d` with `|d| ≥ 53` (spacing `1/192`),
`∑ R(|d|/192 - 1/128)/256 ≤ 4/5`. -/
theorem offsets_row_charge_le (D : Finset ℤ) (hD : ∀ d ∈ D, 53 ≤ d ∨ d ≤ -53) :
    ∑ d ∈ D, archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 ≤ 4 / 5 := by
  classical
  set q : ℝ := Real.exp (-(5 / 384)) with hqdef
  set C : ℝ := Real.exp (-(515 / 768)) / (1 - Real.exp (-(103 / 192))) with hCdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hB1 : Real.exp (-(103 / 192 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hC0 : 0 ≤ C := div_nonneg (Real.exp_pos _).le (by linarith)
  have hterm : ∀ m : ℕ, 53 ≤ m →
      archRemainderV32 ((m : ℝ) / 192 - 1 / 128) / 256 ≤ C / 256 * q ^ (m - 53) := by
    intro m hm
    have h := archRemainder_le_geom m hm
    calc archRemainderV32 ((m : ℝ) / 192 - 1 / 128) / 256 ≤ C * q ^ (m - 53) / 256 :=
          div_le_div_of_nonneg_right h (by norm_num)
      _ = C / 256 * q ^ (m - 53) := by ring
  have hpos : ∑ d ∈ D.filter (fun d => 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 ≤ C / 256 * (1 / (1 - q)) := by
    calc ∑ d ∈ D.filter (fun d => 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256
        ≤ ∑ d ∈ D.filter (fun d => 0 < d), C / 256 * q ^ (d.toNat - 53) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_filter] at hd
          obtain ⟨hdD, hd2⟩ := hd
          have hd0 : 0 ≤ d := hd2.le
          have hcast : ((d.toNat : ℕ) : ℝ) = |(d : ℝ)| := by
            rw [abs_of_nonneg (by exact_mod_cast hd0)]
            exact_mod_cast Int.toNat_of_nonneg hd0
          have h53 : 53 ≤ d.toNat := by
            have := hD d hdD
            omega
          rw [← hcast]
          exact hterm _ h53
      _ = C / 256 * ∑ d ∈ D.filter (fun d => 0 < d), q ^ (d.toNat - 53) := by
          rw [Finset.mul_sum]
      _ ≤ C / 256 * (1 / (1 - q)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hC0 (by norm_num))
          apply sum_geom_le_of_injOn _ _ _ q hq0 hq1
          intro a ha b hb hab
          have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
          have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
          obtain ⟨haD, ha2⟩ := ha'
          obtain ⟨hbD, hb2⟩ := hb'
          have ha53 := hD a haD
          have hb53 := hD b hbD
          simp only at hab
          omega
  have hneg : ∑ d ∈ D.filter (fun d => ¬ 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 ≤ C / 256 * (1 / (1 - q)) := by
    calc ∑ d ∈ D.filter (fun d => ¬ 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256
        ≤ ∑ d ∈ D.filter (fun d => ¬ 0 < d), C / 256 * q ^ ((-d).toNat - 53) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_filter] at hd
          obtain ⟨hdD, hd2⟩ := hd
          have hdm : d ≤ -53 := by
            have := hD d hdD
            omega
          have hd0 : 0 ≤ -d := by omega
          have hdneg : (d : ℝ) < 0 := by exact_mod_cast (show d < 0 by omega)
          have hcast : (((-d).toNat : ℕ) : ℝ) = |(d : ℝ)| := by
            rw [abs_of_neg hdneg]
            exact_mod_cast Int.toNat_of_nonneg hd0
          have h53 : 53 ≤ (-d).toNat := by omega
          rw [← hcast]
          exact hterm _ h53
      _ = C / 256 * ∑ d ∈ D.filter (fun d => ¬ 0 < d), q ^ ((-d).toNat - 53) := by
          rw [Finset.mul_sum]
      _ ≤ C / 256 * (1 / (1 - q)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hC0 (by norm_num))
          apply sum_geom_le_of_injOn _ _ _ q hq0 hq1
          intro a ha b hb hab
          have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
          have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
          obtain ⟨haD, ha2⟩ := ha'
          obtain ⟨hbD, hb2⟩ := hb'
          have ha53 := hD a haD
          have hb53 := hD b hbD
          simp only at hab
          omega
  have hsplit : ∑ d ∈ D, archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 =
      ∑ d ∈ D.filter (fun d => 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 + ∑ d ∈ D.filter (fun d => ¬ 0 < d), archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256 :=
    (Finset.sum_filter_add_sum_filter_not D (fun d => 0 < d)
      (fun d => archRemainderV32 (|(d : ℝ)| / 192 - 1 / 128) / 256)).symm
  -- numerical constant
  have hA : Real.exp (-(515 / 768 : ℝ)) ≤ 1179648 / 2235913 :=
    (exp_neg_le_quadratic (515 / 768) (by norm_num)).trans (by norm_num)
  have hB : Real.exp (-(103 / 192 : ℝ)) ≤ 73728 / 123889 :=
    (exp_neg_le_quadratic (103 / 192) (by norm_num)).trans (by norm_num)
  have hQ : q ≤ 294912 / 298777 :=
    (exp_neg_le_quadratic (5 / 384) (by norm_num)).trans (by norm_num)
  have h1B : (1 - 73728 / 123889 : ℝ) ≤ 1 - Real.exp (-(103 / 192 : ℝ)) := by linarith
  have h1q : (1 - 294912 / 298777 : ℝ) ≤ 1 - q := by linarith
  have hprod : (1 - 73728 / 123889 : ℝ) * (1 - 294912 / 298777) ≤
      (1 - Real.exp (-(103 / 192 : ℝ))) * (1 - q) :=
    mul_le_mul h1B h1q (by norm_num) (by linarith)
  have hden : 0 < (1 - Real.exp (-(103 / 192 : ℝ))) * 256 * (1 - q) :=
    mul_pos (mul_pos (by linarith) (by norm_num)) (by linarith)
  have hhalf : C / 256 * (1 / (1 - q)) ≤ 2 / 5 := by
    rw [hCdef, div_div, mul_one_div, div_div, div_le_iff₀ hden]
    nlinarith [hA, hprod]
  rw [hsplit]
  linarith [hpos, hneg, hhalf]

/-- The bound sits strictly inside the row budget of `RHPrimeFreeRecompositionJoinV1`. -/
theorem four_fifths_lt_row_budget : (4 / 5 : ℝ) < 57430 / 65536 := by norm_num

end AEGIS.RHLogFreeRowDecayV1

#print axioms AEGIS.RHLogFreeRowDecayV1.archRemainder_le_geom
#print axioms AEGIS.RHLogFreeRowDecayV1.offsets_row_charge_le
