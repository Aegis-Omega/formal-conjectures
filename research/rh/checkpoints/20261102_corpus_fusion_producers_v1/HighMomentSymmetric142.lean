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
