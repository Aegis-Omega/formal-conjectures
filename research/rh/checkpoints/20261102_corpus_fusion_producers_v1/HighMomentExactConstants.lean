/- Exact arithmetic component of the ordinary high-moment complement proof.
   This file proves integer inequalities only. It does not define the Weil form,
   prove Hermite interpolation, identify digamma, or prove RH. No native_decide.
   Pin: Lean 4.33.1, 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace AEGIS.HighMomentExactConstants

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- After clearing positive denominators, this is
    68 (260109/100)^141 / (141!)^2 < 13/20000. -/
theorem hermite141_T85_integer_bound :
    1360000 * 260109 ^ 141 < 13 * 100 ^ 141 * factorial 141 ^ 2 := by
  decide

def scale : Nat := 1000000000
def termDenominator (j : Nat) : Nat := (j + 1) * ((4 * j + 1)^2 + 28900)
def termNumerator (j : Nat) : Nat := 28897 - 12 * j
def lowerTerm (j : Nat) : Nat := scale * termNumerator j / termDenominator j
def lowerSum : Nat := ((List.range 1024).map lowerTerm).sum

/-- All 1024 rows are checked; this is not a sample or an unchecked receipt.
    The separate analytic proof interprets these rational summands as digamma.
    Subtraction is nontruncated on this finite range, as checked below. -/
theorem all1024_numerators_positive :
    (List.range 1024).all (fun j => decide (12 * j < 28897)) = true := by
  decide

theorem all1024_denominators_positive :
    (List.range 1024).all (fun j => decide (0 < termDenominator j)) = true := by
  decide

theorem all1024_rounded_lower_bounds :
    (List.range 1024).all (fun j =>
      decide (lowerTerm j * termDenominator j ≤ scale * termNumerator j)) = true := by
  decide

/-- sum lowerTerm/scale - 7/4 - 3/4093 > 103/40.
    The tail 3/4093 and gamma/log bounds are justified in the paper proof. -/
theorem digamma_T85_finite_lower_integer_bound :
    scale * (173 * 4093 + 120) < 40 * 4093 * lowerSum := by
  decide

/-- 103/40 - 9/4 - (103/40 + 6) * (13/20000) = 255541/800000 > 31/100. -/
theorem complement_margin_integer_bound : 31 * 800000 < 255541 * 100 := by
  decide

end AEGIS.HighMomentExactConstants

#print AEGIS.HighMomentExactConstants.hermite141_T85_integer_bound
#print axioms AEGIS.HighMomentExactConstants.hermite141_T85_integer_bound
#print axioms AEGIS.HighMomentExactConstants.all1024_numerators_positive
#print axioms AEGIS.HighMomentExactConstants.all1024_denominators_positive
#print axioms AEGIS.HighMomentExactConstants.all1024_rounded_lower_bounds
#print axioms AEGIS.HighMomentExactConstants.digamma_T85_finite_lower_integer_bound
#print axioms AEGIS.HighMomentExactConstants.complement_margin_integer_bound
