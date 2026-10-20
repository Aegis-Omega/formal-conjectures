/- Source indexing of the 141 inner rows inside the 301-row cross product. -/
import CvSCachedSourceProductV1
namespace AEGIS.CvSCachedSliceV1
open AEGIS.RHFixIntervalV1

theorem inner_slice (ys : List Iv) (k : Fin 141) :
    ((ys.drop 80).take 141).getD k.val ⟨0, 0⟩ = ys.getD (k.val + 80) ⟨0, 0⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, k.isLt,
    Nat.add_comm]
end AEGIS.CvSCachedSliceV1
#print axioms AEGIS.CvSCachedSliceV1.inner_slice
