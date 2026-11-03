/- Source-bound exact arithmetic for the weighted independent-shape
composition. The original weights and exact costs are extracted from Git
blob 97a98db382e433488ed20f7df0980f41b20e4cbc; they are not newly optimized.
This module proves integer facts only. It does not define B, prove the
analytic mixed estimate, or prove RH. Lean4.33.1, no Mathlib dependency. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace AEGIS.WeightedIndependentShapeArithmetic

def weights : List Nat := [427, 355, 24, 24, 24, 24, 24, 24, 24, 355, 427]
def weight (i : Nat) : Nat := weights[i]!
def costNum (i j : Nat) : Nat :=
  if i = j then 0 else
  if i - j = 9 ∨ j - i = 9 then 2109 else
  if i - j = 10 ∨ j - i = 10 then 837 else 37
def rowNum (i : Nat) : Nat :=
  ((List.range 11).map (fun j => costNum i j * weight j)).sum

theorem exact_row_ledger :
    (List.range 11).map rowNum = [1125445, 935693, 63196, 63196, 63196, 63196, 63196, 63196, 63196, 935693, 1125445] := by decide

theorem positive_weights :
    (List.range 11).all (fun i => decide (0 < weight i)) = true := by decide

theorem all_eleven_weighted_rows :
    (List.range 11).all (fun i =>
      decide (355 * rowNum i ≤ 25289 * 37 * weight i)) = true := by decide

theorem maximum_attained :
    355 * rowNum 1 = 25289 * 37 * weight 1 := by decide

theorem exact_margin :
    5671 * 355 = 2 * 25289 * 32 + 394709 := by decide

theorem positive_margin : 0 < (394709 : Nat) := by decide

/- The stronger independent-shape argument pays each off-diagonal cost
only once. Keep the original factor-two certificate above unchanged, and
kernel-check the improved exact rational margin separately. -/
theorem exact_direct_independent_margin :
    (5671 : Nat) * 355 = 25289 * 32 + 1203957 := by decide

theorem positive_direct_independent_margin :
    0 < (1203957 : Nat) := by decide

theorem improves_previous_weights :
    (732143 : Nat) * 1136000 < 394709 * 2107520 := by decide

end AEGIS.WeightedIndependentShapeArithmetic

#print axioms AEGIS.WeightedIndependentShapeArithmetic.exact_row_ledger
#print axioms AEGIS.WeightedIndependentShapeArithmetic.positive_weights
#print axioms AEGIS.WeightedIndependentShapeArithmetic.all_eleven_weighted_rows
#print axioms AEGIS.WeightedIndependentShapeArithmetic.maximum_attained
#print axioms AEGIS.WeightedIndependentShapeArithmetic.exact_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.positive_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.exact_direct_independent_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.positive_direct_independent_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.improves_previous_weights
