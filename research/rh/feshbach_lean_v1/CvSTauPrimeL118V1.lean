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
import CvSTauL118DataV1
import CvSTauPrimeL12V1

/-!
# `τ_k` at `L = 11/8`, `k = 1, …, 70`

`τ_k = ∫ h₊ S_k + π Σ_{j<M} ppw_j sin(2πk ℓ_j/L)` (`CvSRowTailV1.tau`). At `L = 11/8` the nodes
`ℓ_j = min(log(j+1), L)` of the prime powers `j + 1 ≥ 4` still sit at the window end
(`log 4 > 11/8`), where the sine vanishes, so for every cutoff `M ≥ 3` only `p = 2, 3` remain
(`primeSum_eq`):
  `τ_k = ∫ h₊ S_k + π (√2 log 2 · sin(16πk log 2/11) + (2/√3) log 3 · sin(16πk log 3/11))`.
The logarithm, square root and sine enclosures and the weights `ppw 1`, `ppw 2` are those of
`CvSTauPrimeL12V1`, which do not depend on the window. With `CvSTauL118DataV1.source_integral_mem`,
`tau_mem` gives a box of width at most `2·10⁻⁸` for `τ_k`, `k = 1, …, 70` (data from
`tools/gen_tau_prime118.py`, untrusted; one `decide +kernel`). Not RH.
-/

open Finset

namespace AEGIS.CvSTauPrimeL118V1

open AEGIS.CvSTauL118DataV1 AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchLorentzV1
open AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds)
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds s2Lo s3Lo thLo sinPiLo
  sinPiHi sinPi_bounds mul_lo mul_hi piLo_nonneg ppw_one ppw_two w2Lo w2Hi w3Lo w3Hi w2_bounds
  w3_bounds)

/-! ### The prime part of `τ_k` at `L = 11/8` -/

theorem node_zero : node (11 / 8) 0 = 0 := by
  simp only [node]
  norm_num

theorem node_one : node (11 / 8) 1 = Real.log 2 := by
  simp only [node]
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

theorem node_two : node (11 / 8) 2 = Real.log 3 := by
  simp only [node]
  rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l3Hi : ℝ) ≤ 11 / 8 := by norm_num [l3Hi]
  exact min_eq_left (by linarith [log3_bounds.2])

/-- Prime powers `j + 1 ≥ 4` have `log(j+1) > 11/8`, so their node is the window end. -/
theorem node_big {j : ℕ} (hj : 3 ≤ j) : node (11 / 8) j = 11 / 8 := by
  simp only [node]
  apply min_eq_right
  have h4 : (4 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ j + 1)
  have hl : Real.log 4 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h4
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlo : (11 / 8 : ℝ) ≤ 2 * l2Lo := by norm_num [l2Lo]
  have := log2_bounds.1
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

/-- **At `L = 11/8` only `p = 2, 3` contribute to the prime sum** (for any cutoff `M ≥ 3`). -/
theorem primeSum_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    ∑ j ∈ range M, ppw j * Real.sin (2 * Real.pi * k * node (11 / 8) j / (11 / 8)) =
      ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
        ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11)) := by
  have hz : ∀ j ∈ range M, j ∉ range 3 →
      ppw j * Real.sin (2 * Real.pi * k * node (11 / 8) j / (11 / 8)) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [node_big hj, show 2 * Real.pi * k * (11 / 8) / (11 / 8) = ((2 * k : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.sin_int_mul_pi, mul_zero]
  rw [← sum_subset (range_mono hM) hz]
  simp only [sum_range_succ, sum_range_zero, node_zero, node_one, node_two]
  rw [show 2 * Real.pi * k * Real.log 2 / (11 / 8) = Real.pi * (16 * k * Real.log 2 / 11) by ring,
    show 2 * Real.pi * k * Real.log 3 / (11 / 8) = Real.pi * (16 * k * Real.log 3 / 11) by ring]
  simp

def s2l (k : ℕ) : ℚ := sinPiLo (16 * k * l2Lo / 11) (16 * k * l2Hi / 11)
def s2h (k : ℕ) : ℚ := sinPiHi (16 * k * l2Lo / 11) (16 * k * l2Hi / 11)
def s3l (k : ℕ) : ℚ := sinPiLo (16 * k * l3Lo / 11) (16 * k * l3Hi / 11)
def s3h (k : ℕ) : ℚ := sinPiHi (16 * k * l3Lo / 11) (16 * k * l3Hi / 11)

def sumLo (k : ℕ) : ℚ := min (w2Lo * s2l k) (w2Hi * s2l k) + min (w3Lo * s3l k) (w3Hi * s3l k)
def sumHi (k : ℕ) : ℚ := max (w2Lo * s2h k) (w2Hi * s2h k) + max (w3Lo * s3h k) (w3Hi * s3h k)

/-- Rational bounds for `π Σ_j ppw_j sin(2πk ℓ_j/L)` at `L = 11/8`. -/
def primeLo (k : ℕ) : ℚ := min (piLo * sumLo k) (piHi * sumLo k)
def primeHi (k : ℕ) : ℚ := max (piLo * sumHi k) (piHi * sumHi k)

theorem prime_bounds (k : ℕ) (h2 : |thLo (16 * k * l2Lo / 11)| ≤ 2)
    (h3 : |thLo (16 * k * l3Lo / 11)| ≤ 2) :
    (primeLo k : ℝ) ≤ Real.pi * (ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
        ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11))) ∧
      Real.pi * (ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
        ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11))) ≤ primeHi k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have l2 := log2_bounds
  have l3 := log3_bounds
  have hs2 : (s2l k : ℝ) ≤ Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) ∧
      Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) ≤ s2h k :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have hs3 : (s3l k : ℝ) ≤ Real.sin (Real.pi * (16 * k * Real.log 3 / 11)) ∧
      Real.sin (Real.pi * (16 * k * Real.log 3 / 11)) ≤ s3h k :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  have hw2 := w2_bounds
  have hw3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have hπ := pi_bounds
  have hlo : (sumLo k : ℝ) ≤ ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
      ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11)) := by
    simp only [sumLo]
    push_cast
    exact add_le_add (mul_lo z2 hw2.1 hw2.2 hs2.1) (mul_lo z3 hw3.1 hw3.2 hs3.1)
  have hhi : ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
      ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11)) ≤ sumHi k := by
    simp only [sumHi]
    push_cast
    exact add_le_add (mul_hi z2 hw2.1 hw2.2 hs2.2) (mul_hi z3 hw3.1 hw3.2 hs3.2)
  constructor
  · simp only [primeLo]
    push_cast
    exact mul_lo piLo_nonneg hπ.1.le hπ.2.le hlo
  · simp only [primeHi]
    push_cast
    exact mul_hi piLo_nonneg hπ.1.le hπ.2.le hhi

/-! ### `τ_k` at `L = 11/8` -/

theorem tau_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    tau M (11 / 8) k = (∫ r, hplus r * sourceS (11 / 8) r k) +
      Real.pi * (ppw 1 * Real.sin (Real.pi * (16 * k * Real.log 2 / 11)) +
        ppw 2 * Real.sin (Real.pi * (16 * k * Real.log 3 / 11))) := by
  rw [tau, primeSum_eq hM]

/-- The full check: source box from `CvSTauL118DataV1` plus the prime part, inside `[lo, hi]`. -/
def tauFullCheck (k : ℕ) (lo hi : ℚ) : Bool :=
  decide (|thLo (16 * k * l2Lo / 11)| ≤ 2) && decide (|thLo (16 * k * l3Lo / 11)| ≤ 2) &&
    decide (lo ≤ tauLo.getD (k - 1) 0 + primeLo k) &&
    decide (tauHi.getD (k - 1) 0 + primeHi k ≤ hi)

theorem tauFullCheck_sound {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70)
    {lo hi : ℚ} (h : tauFullCheck k lo hi = true) :
    (lo : ℝ) ≤ tau M (11 / 8) k ∧ tau M (11 / 8) k ≤ hi := by
  simp only [tauFullCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, h3⟩, hl⟩, hh⟩ := h
  have hs := source_integral_mem hk1 hk
  have hp := prime_bounds k h2 h3
  have hl' : (lo : ℝ) ≤ ((tauLo.getD (k - 1) 0 : ℚ) : ℝ) + (primeLo k : ℝ) := by
    exact_mod_cast hl
  have hh' : ((tauHi.getD (k - 1) 0 : ℚ) : ℝ) + (primeHi k : ℝ) ≤ hi := by exact_mod_cast hh
  rw [tau_eq hM]
  push_cast at hs hp ⊢
  constructor <;> linarith [hs.1, hs.2, hp.1, hp.2]

/-- Boxes for `τ_k`, `k = 1, …, 70` (untrusted, from `tools/gen_tau_prime118.py`). -/
def tauFLo : List ℚ := [
  193310538870494 / 281474976710656,
  731329520134595 / 281474976710656,
  1961732432850216 / 281474976710656,
  2508408589443088 / 281474976710656,
  1219764541060215 / 281474976710656,
  424933101547369 / 281474976710656,
  599000227527296 / 281474976710656,
  2257357136454505 / 281474976710656,
  2222528595504676 / 281474976710656,
  1528042046459776 / 281474976710656,
  47730066520793 / 281474976710656,
  1055460801936683 / 281474976710656,
  1826958370342037 / 281474976710656,
  2719410380311797 / 281474976710656,
  947862434528006 / 281474976710656,
  633404430888426 / 281474976710656,
  456412978419782 / 281474976710656,
  2529594024102190 / 281474976710656,
  1992463211634906 / 281474976710656,
  1669353684231611 / 281474976710656,
  -166798674480559 / 281474976710656,
  1323313643986859 / 281474976710656,
  1683644446101100 / 281474976710656,
  2889553953354774 / 281474976710656,
  686262056136174 / 281474976710656,
  814378222611320 / 281474976710656,
  333552834303391 / 281474976710656,
  2767567396187555 / 281474976710656,
  1780865014242964 / 281474976710656,
  1779208924111688 / 281474976710656,
  -350384177496480 / 281474976710656,
  1559789923470718 / 281474976710656,
  1567032421304430 / 281474976710656,
  3020404068804920 / 281474976710656,
  458198305000475 / 281474976710656,
  962639326527384 / 281474976710656,
  248211980368116 / 281474976710656,
  2963167063975210 / 281474976710656,
  1603330628248814 / 281474976710656,
  1848859719364162 / 281474976710656,
  -489146733903234 / 281474976710656,
  1755180327489223 / 281474976710656,
  1489574626352416 / 281474976710656,
  3102597188797247 / 281474976710656,
  275641805927501 / 281474976710656,
  1068896126349547 / 281474976710656,
  210979936977337 / 281474976710656,
  3107194649668063 / 281474976710656,
  1470079122619199 / 281474976710656,
  1869994724258597 / 281474976710656,
  -573729122730203 / 281474976710656,
  1901119356057880 / 281474976710656,
  1459692796724085 / 281474976710656,
  3128727733119969 / 281474976710656,
  146753951791562 / 281474976710656,
  1126193371504932 / 281474976710656,
  228750997869158 / 281474976710656,
  3193124208814575 / 281474976710656,
  1387704121031431 / 281474976710656,
  1837191166650070 / 281474976710656,
  -598425655210717 / 281474976710656,
  1992314993760096 / 281474976710656,
  1482174018830344 / 281474976710656,
  3094637125464401 / 281474976710656,
  76014661814253 / 281474976710656,
  1130915080161307 / 281474976710656,
  304704458401230 / 281474976710656,
  3217905639574581 / 281474976710656,
  1359071364178724 / 281474976710656,
  1748567618608001 / 281474976710656
]

/-- Upper ends. -/
def tauFHi : List ℚ := [
  193310544427443 / 281474976710656,
  731329525692835 / 281474976710656,
  1961732438439597 / 281474976710656,
  2508408595038016 / 281474976710656,
  1219764546659124 / 281474976710656,
  424933107126075 / 281474976710656,
  599000233129393 / 281474976710656,
  2257357142058510 / 281474976710656,
  2222528601105980 / 281474976710656,
  1528042052064029 / 281474976710656,
  47730072115806 / 281474976710656,
  1055460807540124 / 281474976710656,
  1826958375951132 / 281474976710656,
  2719410385904665 / 281474976710656,
  947862440130559 / 281474976710656,
  633404436483983 / 281474976710656,
  456412984015323 / 281474976710656,
  2529594029705639 / 281474976710656,
  1992463217234645 / 281474976710656,
  1669353689837501 / 281474976710656,
  -166798668877914 / 281474976710656,
  1323313649597315 / 281474976710656,
  1683644451711522 / 281474976710656,
  2889553958958193 / 281474976710656,
  686262061744881 / 281474976710656,
  814378228219270 / 281474976710656,
  333552839905145 / 281474976710656,
  2767567401796008 / 281474976710656,
  1780865019853250 / 281474976710656,
  1779208929719366 / 281474976710656,
  -350384171895456 / 281474976710656,
  1559789929078415 / 281474976710656,
  1567032426915055 / 281474976710656,
  3020404074415012 / 281474976710656,
  458198310606842 / 281474976710656,
  962639332143472 / 281474976710656,
  248211985974630 / 281474976710656,
  2963167069585721 / 281474976710656,
  1603330633860687 / 281474976710656,
  1848859724974934 / 281474976710656,
  -489146728295862 / 281474976710656,
  1755180333106627 / 281474976710656,
  1489574631962120 / 281474976710656,
  3102597194412712 / 281474976710656,
  275641811531495 / 281474976710656,
  1068896131955516 / 281474976710656,
  210979942583498 / 281474976710656,
  3107194655272734 / 281474976710656,
  1470079128235588 / 281474976710656,
  1869994729870292 / 281474976710656,
  -573729117124620 / 281474976710656,
  1901119361670507 / 281474976710656,
  1459692802342301 / 281474976710656,
  3128727738728039 / 281474976710656,
  146753957402582 / 281474976710656,
  1126193377117641 / 281474976710656,
  228751003482347 / 281474976710656,
  3193124214427094 / 281474976710656,
  1387704126642183 / 281474976710656,
  1837191172258008 / 281474976710656,
  -598425649592832 / 281474976710656,
  1992314999373124 / 281474976710656,
  1482174024437606 / 281474976710656,
  3094637131078559 / 281474976710656,
  76014667420857 / 281474976710656,
  1130915085772954 / 281474976710656,
  304704464017020 / 281474976710656,
  3217905645193646 / 281474976710656,
  1359071369787008 / 281474976710656,
  1748567624217977 / 281474976710656
]

def tauFullAll : Bool :=
  (List.range 70).all fun i => tauFullCheck (i + 1) (tauFLo.getD i 0) (tauFHi.getD i 0)

set_option maxRecDepth 100000 in
theorem tauFullAll_true : tauFullAll = true := by decide +kernel

/-- **`τ_k` at `L = 11/8` for `k = 1, …, 70` and every prime cutoff `M ≥ 3`**, each box of width
at most `2·10⁻⁸`. -/
theorem tau_mem {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70) :
    ((tauFLo.getD (k - 1) 0 : ℚ) : ℝ) ≤ tau M (11 / 8) k ∧
      tau M (11 / 8) k ≤ ((tauFHi.getD (k - 1) 0 : ℚ) : ℝ) := by
  have h := tauFullAll_true
  simp only [tauFullAll, List.all_eq_true, List.mem_range] at h
  have := h (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at this
  exact tauFullCheck_sound hM hk1 hk this

end AEGIS.CvSTauPrimeL118V1

#print axioms AEGIS.CvSTauPrimeL118V1.primeSum_eq
#print axioms AEGIS.CvSTauPrimeL118V1.prime_bounds
#print axioms AEGIS.CvSTauPrimeL118V1.tauFullCheck_sound
#print axioms AEGIS.CvSTauPrimeL118V1.tauFullAll_true
#print axioms AEGIS.CvSTauPrimeL118V1.tau_mem
