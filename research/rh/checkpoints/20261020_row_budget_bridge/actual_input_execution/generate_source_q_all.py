from pathlib import Path
w=Path(__file__).resolve().parent
s='/- Complete Q input checks with exact 2*pi normalization and source-row indexing. -/\nimport CvSCachedSliceV1\nimport CvSSourceProductAllV1\nimport CvSFullTableClosureV1\n'
s+=''.join(f'import CvSSourceQCache{i}\n' for i in range(14))+''.join(f'import CvSSourceQCheck{i}\n' for i in range(139))
s+='''import Mathlib.Tactic.FinCases
namespace AEGIS.CvSSourceQAllV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSSourceProductAllV1 AEGIS.CvSSourceQNormalizeV1 AEGIS.CvSCachedSliceV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
s+='def vectors : List (Vector 141) := ['+', '.join(f'AEGIS.CvSSourceQCache{i//10}.column{i}' for i in range(139))+']\n'
s+='''def vector (j : Fin 139) : Vector 141 := vectors.getD j.val AEGIS.CvSSourceQCache0.column0

theorem vector_source (k : Fin 141) (j : Fin 139) :
    (vector j).values.getD k.val ⟨0, 0⟩ = Y ⟨k.val + 80, by omega⟩ j := by
  fin_cases j
'''
for j in range(139):s+=f'  · exact inner_slice AEGIS.CvSSourceProduct{j}.Y k\n'
s+='''theorem checked (i j : Fin 139) : contains (AEGIS.CvSFullTableClosureV1.Q i j)
    (normalize (evalDot (inputColumn i).x (vector j))) = true := by
  fin_cases j
'''
for j in range(139):s+=f'  · exact AEGIS.CvSSourceQCheck{j}.all_rows i\n'
s+='end AEGIS.CvSSourceQAllV1\n#print axioms AEGIS.CvSSourceQAllV1.vector_source\n#print axioms AEGIS.CvSSourceQAllV1.checked\n'
(w/'CvSSourceQAllV1.lean').write_text(s)
print('Generated complete normalized source-Q composition candidate')
