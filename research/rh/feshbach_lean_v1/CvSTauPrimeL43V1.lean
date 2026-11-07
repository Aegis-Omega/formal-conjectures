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
import CvSTauL43DataV1
import CvSTauPrimeL12V1

/-!
# `τ_k` at `L = 4/3`, `k = 1, …, 70`

`τ_k = ∫ h₊ S_k + π Σ_{j<M} ppw_j sin(2πk ℓ_j/L)` (`CvSRowTailV1.tau`). At `L = 4/3` the nodes
`ℓ_j = min(log(j+1), L)` of the prime powers `j + 1 ≥ 4` still sit at the window end
(`log 4 > 4/3`), where the sine vanishes, so for every cutoff `M ≥ 3` only `p = 2, 3` remain
(`primeSum_eq`):
  `τ_k = ∫ h₊ S_k + π (√2 log 2 · sin(3πk log 2/2) + (2/√3) log 3 · sin(3πk log 3/2))`.
The logarithm, square root and sine enclosures and the weights `ppw 1`, `ppw 2` are those of
`CvSTauPrimeL12V1`, which do not depend on the window. With `CvSTauL43DataV1.source_integral_mem`,
`tau_mem` gives a box of width at most `2·10⁻⁷` for `τ_k`, `k = 1, …, 70` (data from
`tools/gen_tau_prime43.py`, untrusted; one `decide +kernel`). Not RH.
-/

open Finset

namespace AEGIS.CvSTauPrimeL43V1

open AEGIS.CvSTauL43DataV1 AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchLorentzV1
open AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauL12V1 (piLo piHi pi_bounds)
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds s2Lo s3Lo thLo sinPiLo
  sinPiHi sinPi_bounds mul_lo mul_hi piLo_nonneg ppw_one ppw_two w2Lo w2Hi w3Lo w3Hi w2_bounds
  w3_bounds)

/-! ### The prime part of `τ_k` at `L = 4/3` -/

theorem node_zero : node (4 / 3) 0 = 0 := by
  simp only [node]
  norm_num

theorem node_one : node (4 / 3) 1 = Real.log 2 := by
  simp only [node]
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

theorem node_two : node (4 / 3) 2 = Real.log 3 := by
  simp only [node]
  rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l3Hi : ℝ) ≤ 4 / 3 := by norm_num [l3Hi]
  exact min_eq_left (by linarith [log3_bounds.2])

/-- Prime powers `j + 1 ≥ 4` have `log(j+1) > 4/3`, so their node is the window end. -/
theorem node_big {j : ℕ} (hj : 3 ≤ j) : node (4 / 3) j = 4 / 3 := by
  simp only [node]
  apply min_eq_right
  have h4 : (4 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ j + 1)
  have hl : Real.log 4 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h4
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlo : (4 / 3 : ℝ) ≤ 2 * l2Lo := by norm_num [l2Lo]
  have := log2_bounds.1
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

/-- **At `L = 4/3` only `p = 2, 3` contribute to the prime sum** (for any cutoff `M ≥ 3`). -/
theorem primeSum_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    ∑ j ∈ range M, ppw j * Real.sin (2 * Real.pi * k * node (4 / 3) j / (4 / 3)) =
      ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
        ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2)) := by
  have hz : ∀ j ∈ range M, j ∉ range 3 →
      ppw j * Real.sin (2 * Real.pi * k * node (4 / 3) j / (4 / 3)) = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [node_big hj, show 2 * Real.pi * k * (4 / 3) / (4 / 3) = ((2 * k : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.sin_int_mul_pi, mul_zero]
  rw [← sum_subset (range_mono hM) hz]
  simp only [sum_range_succ, sum_range_zero, node_zero, node_one, node_two]
  rw [show 2 * Real.pi * k * Real.log 2 / (4 / 3) = Real.pi * (3 * k * Real.log 2 / 2) by ring,
    show 2 * Real.pi * k * Real.log 3 / (4 / 3) = Real.pi * (3 * k * Real.log 3 / 2) by ring]
  simp

def s2l (k : ℕ) : ℚ := sinPiLo (3 * k * l2Lo / 2) (3 * k * l2Hi / 2)
def s2h (k : ℕ) : ℚ := sinPiHi (3 * k * l2Lo / 2) (3 * k * l2Hi / 2)
def s3l (k : ℕ) : ℚ := sinPiLo (3 * k * l3Lo / 2) (3 * k * l3Hi / 2)
def s3h (k : ℕ) : ℚ := sinPiHi (3 * k * l3Lo / 2) (3 * k * l3Hi / 2)

def sumLo (k : ℕ) : ℚ := min (w2Lo * s2l k) (w2Hi * s2l k) + min (w3Lo * s3l k) (w3Hi * s3l k)
def sumHi (k : ℕ) : ℚ := max (w2Lo * s2h k) (w2Hi * s2h k) + max (w3Lo * s3h k) (w3Hi * s3h k)

/-- Rational bounds for `π Σ_j ppw_j sin(2πk ℓ_j/L)` at `L = 4/3`. -/
def primeLo (k : ℕ) : ℚ := min (piLo * sumLo k) (piHi * sumLo k)
def primeHi (k : ℕ) : ℚ := max (piLo * sumHi k) (piHi * sumHi k)

theorem prime_bounds (k : ℕ) (h2 : |thLo (3 * k * l2Lo / 2)| ≤ 2)
    (h3 : |thLo (3 * k * l3Lo / 2)| ≤ 2) :
    (primeLo k : ℝ) ≤ Real.pi * (ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
        ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2))) ∧
      Real.pi * (ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
        ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2))) ≤ primeHi k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have l2 := log2_bounds
  have l3 := log3_bounds
  have hs2 : (s2l k : ℝ) ≤ Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) ∧
      Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) ≤ s2h k :=
    sinPi_bounds (by push_cast; gcongr; exact l2.1) (by push_cast; gcongr; exact l2.2) h2
  have hs3 : (s3l k : ℝ) ≤ Real.sin (Real.pi * (3 * k * Real.log 3 / 2)) ∧
      Real.sin (Real.pi * (3 * k * Real.log 3 / 2)) ≤ s3h k :=
    sinPi_bounds (by push_cast; gcongr; exact l3.1) (by push_cast; gcongr; exact l3.2) h3
  have hw2 := w2_bounds
  have hw3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have hπ := pi_bounds
  have hlo : (sumLo k : ℝ) ≤ ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
      ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2)) := by
    simp only [sumLo]
    push_cast
    exact add_le_add (mul_lo z2 hw2.1 hw2.2 hs2.1) (mul_lo z3 hw3.1 hw3.2 hs3.1)
  have hhi : ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
      ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2)) ≤ sumHi k := by
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

/-! ### `τ_k` at `L = 4/3` -/

theorem tau_eq {M : ℕ} (hM : 3 ≤ M) (k : ℤ) :
    tau M (4 / 3) k = (∫ r, hplus r * sourceS (4 / 3) r k) +
      Real.pi * (ppw 1 * Real.sin (Real.pi * (3 * k * Real.log 2 / 2)) +
        ppw 2 * Real.sin (Real.pi * (3 * k * Real.log 3 / 2))) := by
  rw [tau, primeSum_eq hM]

/-- The full check: source box from `CvSTauL43DataV1` plus the prime part, inside `[lo, hi]`. -/
def tauFullCheck (k : ℕ) (lo hi : ℚ) : Bool :=
  decide (|thLo (3 * k * l2Lo / 2)| ≤ 2) && decide (|thLo (3 * k * l3Lo / 2)| ≤ 2) &&
    decide (lo ≤ tauLo.getD (k - 1) 0 + primeLo k) &&
    decide (tauHi.getD (k - 1) 0 + primeHi k ≤ hi)

theorem tauFullCheck_sound {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70)
    {lo hi : ℚ} (h : tauFullCheck k lo hi = true) :
    (lo : ℝ) ≤ tau M (4 / 3) k ∧ tau M (4 / 3) k ≤ hi := by
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

/-- Boxes for `τ_k`, `k = 1, …, 70` (untrusted, from `tools/gen_tau_prime43.py`). -/
def tauFLo : List ℚ := [
  171777902346563 / 281474976710656,
  648608674791538 / 281474976710656,
  1231769411245664 / 281474976710656,
  2851328190675868 / 281474976710656,
  1626867614022864 / 281474976710656,
  1572003582572064 / 281474976710656,
  -406452380199771 / 281474976710656,
  1492486587431083 / 281474976710656,
  1162247480006828 / 281474976710656,
  3319093480574299 / 281474976710656,
  964991737980738 / 281474976710656,
  1515607636571477 / 281474976710656,
  -574417487688155 / 281474976710656,
  1986679589563845 / 281474976710656,
  1420705559992216 / 281474976710656,
  3196201956550503 / 281474976710656,
  695117516320739 / 281474976710656,
  1080587809443405 / 281474976710656,
  -149449996842472 / 281474976710656,
  2051388588510619 / 281474976710656,
  2011926426686245 / 281474976710656,
  2522089596174547 / 281474976710656,
  812116226060470 / 281474976710656,
  403092184499843 / 281474976710656,
  711953490498746 / 281474976710656,
  1817836175809584 / 281474976710656,
  2702011166688306 / 281474976710656,
  1568862122478045 / 281474976710656,
  1094699088145212 / 281474976710656,
  -205878284901375 / 281474976710656,
  1663743623085057 / 281474976710656,
  1566861403931817 / 281474976710656,
  3148406822777947 / 281474976710656,
  715577875192486 / 281474976710656,
  1249079807666132 / 281474976710656,
  -416620235134836 / 281474976710656,
  2343953600434274 / 281474976710656,
  1561420144618166 / 281474976710656,
  3081338803958398 / 281474976710656,
  262810810077819 / 281474976710656,
  1084642470556330 / 281474976710656,
  -56853074388492 / 281474976710656,
  2550704409349096 / 281474976710656,
  1890504899456067 / 281474976710656,
  2452336278635489 / 281474976710656,
  291473359333565 / 281474976710656,
  629533944907574 / 281474976710656,
  789013327701775 / 281474976710656,
  2330378599385246 / 281474976710656,
  2411087721680239 / 281474976710656,
  1470742214893338 / 281474976710656,
  639610157512529 / 281474976710656,
  123125509021699 / 281474976710656,
  1811788196951562 / 281474976710656,
  1933510847727975 / 281474976710656,
  2820635032776627 / 281474976710656,
  507530511256245 / 281474976710656,
  1007220265789463 / 281474976710656,
  -111452460159532 / 281474976710656,
  2625236673903751 / 281474976710656,
  1664440191897724 / 281474976710656,
  2821955154157920 / 281474976710656,
  -84030222484344 / 281474976710656,
  1130829560483648 / 281474976710656,
  153436737108339 / 281474976710656,
  2952829958632386 / 281474976710656,
  1707183916760130 / 281474976710656,
  2291850276856755 / 281474976710656,
  -137286205222865 / 281474976710656,
  932709015414245 / 281474976710656
]

/-- Upper ends. -/
def tauFHi : List ℚ := [
  171777954049961 / 281474976710656,
  648608729859150 / 281474976710656,
  1231769466892196 / 281474976710656,
  2851328245757972 / 281474976710656,
  1626867669750821 / 281474976710656,
  1572003638079484 / 281474976710656,
  -406452324685152 / 281474976710656,
  1492486642793991 / 281474976710656,
  1162247535765608 / 281474976710656,
  3319093536257271 / 281474976710656,
  964991793746138 / 281474976710656,
  1515607692115728 / 281474976710656,
  -574417432118864 / 281474976710656,
  1986679645416695 / 281474976710656,
  1420705615930414 / 281474976710656,
  3196202012408012 / 281474976710656,
  695117571958748 / 281474976710656,
  1080587865180784 / 281474976710656,
  -149449941121990 / 281474976710656,
  2051388644113695 / 281474976710656,
  2011926482498848 / 281474976710656,
  2522089652107663 / 281474976710656,
  812116282034720 / 281474976710656,
  403092240444485 / 281474976710656,
  711953546350787 / 281474976710656,
  1817836231512990 / 281474976710656,
  2702011222574551 / 281474976710656,
  1568862178114899 / 281474976710656,
  1094699143864332 / 281474976710656,
  -205878229145456 / 281474976710656,
  1663743678836113 / 281474976710656,
  1566861459639852 / 281474976710656,
  3148406878765590 / 281474976710656,
  715577931065737 / 281474976710656,
  1249079863395689 / 281474976710656,
  -416620179229022 / 281474976710656,
  2343953656140466 / 281474976710656,
  1561420200442340 / 281474976710656,
  3081338859873205 / 281474976710656,
  262810866057562 / 281474976710656,
  1084642526576865 / 281474976710656,
  -56853018349843 / 281474976710656,
  2550704465384559 / 281474976710656,
  1890504955468346 / 281474976710656,
  2452336334605813 / 281474976710656,
  291473415244319 / 281474976710656,
  629534000742232 / 281474976710656,
  789013383444842 / 281474976710656,
  2330378655335499 / 281474976710656,
  2411087777507765 / 281474976710656,
  1470742270894911 / 281474976710656,
  639610213363569 / 281474976710656,
  123125565016583 / 281474976710656,
  1811788252771117 / 281474976710656,
  1933510903663844 / 281474976710656,
  2820635088815440 / 281474976710656,
  507530567085939 / 281474976710656,
  1007220321698101 / 281474976710656,
  -111452404183744 / 281474976710656,
  2625236729935364 / 281474976710656,
  1664440247391929 / 281474976710656,
  2821955207722098 / 281474976710656,
  -84030170489912 / 281474976710656,
  1130829610726235 / 281474976710656,
  153436785923923 / 281474976710656,
  2952830005853032 / 281474976710656,
  1707183962679721 / 281474976710656,
  2291850321528296 / 281474976710656,
  -137286161949005 / 281474976710656,
  932709057545674 / 281474976710656
]

def tauFullAll : Bool :=
  (List.range 70).all fun i => tauFullCheck (i + 1) (tauFLo.getD i 0) (tauFHi.getD i 0)

set_option maxRecDepth 100000 in
theorem tauFullAll_true : tauFullAll = true := by decide +kernel

/-- **`τ_k` at `L = 4/3` for `k = 1, …, 70` and every prime cutoff `M ≥ 3`**, each box of width
at most `2·10⁻⁷`. -/
theorem tau_mem {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 70) :
    ((tauFLo.getD (k - 1) 0 : ℚ) : ℝ) ≤ tau M (4 / 3) k ∧
      tau M (4 / 3) k ≤ ((tauFHi.getD (k - 1) 0 : ℚ) : ℝ) := by
  have h := tauFullAll_true
  simp only [tauFullAll, List.all_eq_true, List.mem_range] at h
  have := h (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at this
  exact tauFullCheck_sound hM hk1 hk this

end AEGIS.CvSTauPrimeL43V1

#print axioms AEGIS.CvSTauPrimeL43V1.primeSum_eq
#print axioms AEGIS.CvSTauPrimeL43V1.prime_bounds
#print axioms AEGIS.CvSTauPrimeL43V1.tauFullCheck_sound
#print axioms AEGIS.CvSTauPrimeL43V1.tauFullAll_true
#print axioms AEGIS.CvSTauPrimeL43V1.tau_mem
