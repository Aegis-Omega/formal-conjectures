/- Exact integer component of the ordinary Li quartet counterexample.
   This file does not define zeta, prove the analytic bridge, or prove RH.
   The analytic coefficient identity is in LI_ROUTE_ATTACK.md. -/

namespace AEGIS.LiQuartetArithmetic

def gaussianMul (z w : Int × Int) : Int × Int :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def gaussianPow (z : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => gaussianMul (gaussianPow z n) z

def denominator : Nat := 17 ^ 6 * 25 ^ 6

def sixthNumerator : Int :=
  4 * (denominator : Int) -
    2 * (gaussianPow (13, 16) 6).1 * ((17 ^ 6 + 25 ^ 6 : Nat) : Int)

theorem gaussian_sixth_exact :
    gaussianPow (13, 16) 6 = (44509113, -62545184) := by decide

theorem denominator_exact_and_positive :
    denominator = 5892961181640625 ∧ 0 < denominator := by decide

theorem sixth_numerator_exact_and_negative :
    sixthNumerator = -309804177801344 ∧ sixthNumerator < 0 := by decide

end AEGIS.LiQuartetArithmetic

#print AEGIS.LiQuartetArithmetic.sixth_numerator_exact_and_negative
#print axioms AEGIS.LiQuartetArithmetic.gaussian_sixth_exact
#print axioms AEGIS.LiQuartetArithmetic.denominator_exact_and_positive
#print axioms AEGIS.LiQuartetArithmetic.sixth_numerator_exact_and_negative
