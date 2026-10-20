/- Fail closed when the actual cross kernel's 2*pi normalization is omitted. -/
import CvSSourceQAllV1
namespace AEGIS.CvSSourceQRejectV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1 AEGIS.CvSIntervalMatrixProductV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem reject_missing_inverse_two_pi :
    contains (AEGIS.CvSFullTableClosureV1.Q 0 0)
      (evalDot (AEGIS.CvSSourceProductAllV1.inputColumn 0).x
        (AEGIS.CvSSourceQAllV1.vector 0)) = false := by decide +kernel
end AEGIS.CvSSourceQRejectV1
#print axioms AEGIS.CvSSourceQRejectV1.reject_missing_inverse_two_pi
