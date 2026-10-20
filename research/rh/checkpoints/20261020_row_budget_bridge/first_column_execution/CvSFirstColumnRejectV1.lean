import RowBudgetFirstColumnBatch0
open AEGIS.RHFixIntervalV1 AEGIS.CvSFirstColumnCheckerV1
namespace AEGIS.CvSFirstColumnRejectV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- Omitting the weighted column cannot produce an accepted certificate. -/
theorem reject_missing_weighted :
    check { AEGIS.RowBudgetFirstColumnBatch0.entry0 with da := [] } = false := by
  decide +kernel

/-- Replacing the positive stored target by the zero interval is rejected. -/
theorem reject_zero_target :
    check { AEGIS.RowBudgetFirstColumnBatch0.entry0 with target := ⟨0, 0⟩ } = false := by
  decide +kernel

end AEGIS.CvSFirstColumnRejectV1
#print axioms AEGIS.CvSFirstColumnRejectV1.reject_missing_weighted
#print axioms AEGIS.CvSFirstColumnRejectV1.reject_zero_target
