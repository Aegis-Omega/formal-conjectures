/- Integer constants for the reflection-invariant 142-moment construction.
   Analytic Hermite, moment projection, and Weil form links remain paper proofs.
   This source does not prove RH or global positivity. -/
import HighMomentExactConstants

set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace AEGIS.HighMomentSymmetric142

/-- 68*(260109/100)^142/(142!)² < 1/10000, cleared denominators. -/
theorem hermite142_T85_integer_bound :
    680000 * 260109 ^ 142 <
      100 ^ 142 * AEGIS.HighMomentExactConstants.factorial 142 ^ 2 := by
  decide

/-- (103/40)*(9999/10000)-6/10000-9/4 = 129657/400000 > 8/25. -/
theorem symmetric_complement_margin_integer_bound :
    8 * 400000 < 129657 * 25 := by
  decide

end AEGIS.HighMomentSymmetric142

#print AEGIS.HighMomentSymmetric142.hermite142_T85_integer_bound
#print AEGIS.HighMomentSymmetric142.symmetric_complement_margin_integer_bound
#print axioms AEGIS.HighMomentSymmetric142.hermite142_T85_integer_bound
#print axioms AEGIS.HighMomentSymmetric142.symmetric_complement_margin_integer_bound
