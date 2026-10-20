/- Rejection controls for the full-table arithmetic and its packing boundary. -/
import CvSFullTableClosureV1
namespace AEGIS.CvSFullTableRejectV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSFullTableClosureV1
open AEGIS.RowBudgetListCell0Pilot
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem reject_zero_output : contains ⟨0, 0⟩ (downscale 16
    (value (Q 0 0) LP2 (columns 0).x (columns 0).dx (columns 0).z
      (columns 0).z (columns 0).gx (columns 0).gdx)) = false := by decide +kernel

theorem reject_missing_diagonal : contains (target 0 0) (downscale 16
    (value ⟨0, 0⟩ LP2 (columns 0).x (columns 0).dx (columns 0).z
      (columns 0).z (columns 0).gx (columns 0).gdx)) = false := by decide +kernel

theorem reject_modified_cache :
    ({ (columns 0).z.cache with middle :=
      { (columns 0).z.cache.middle with forward := (columns 0).z.cache.middle.forward + 1 } } :
      AEGIS.CvSPackedIntervalDotV1.PackedIntervalRow) ≠
    AEGIS.CvSPackedIntervalDotV1.prepareInterval (2^280) (2^128) (columns 0).z.values := by
  decide +kernel
end AEGIS.CvSFullTableRejectV1
#print axioms AEGIS.CvSFullTableRejectV1.reject_zero_output
#print axioms AEGIS.CvSFullTableRejectV1.reject_missing_diagonal
#print axioms AEGIS.CvSFullTableRejectV1.reject_modified_cache
