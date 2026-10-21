from pathlib import Path
w=Path(__file__).resolve().parent
s='/- Concrete indexing of the original 139 cached source columns. -/\nimport CvSCachedInputsV1\nimport CvSCachedEnvelopeJoinV1\n'
s+='''open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSCachedEnvelopeJoinV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace AEGIS.CvSFullCachedTableV1
'''
s+='def columnList : List Column := ['+', '.join(f'⟨AEGIS.CvSCachedInput{i}.x, AEGIS.CvSCachedInput{i}.dx, AEGIS.CvSCachedInput{i}.z, AEGIS.CvSCachedInput{i}.gx, AEGIS.CvSCachedInput{i}.gdx⟩' for i in range(139))+']\n'
s+='''def column (i : ℕ) : Column := columnList.getD i
  ⟨AEGIS.CvSCachedInput0.x, AEGIS.CvSCachedInput0.dx, AEGIS.CvSCachedInput0.z,
    AEGIS.CvSCachedInput0.gx, AEGIS.CvSCachedInput0.gdx⟩
theorem column_count : columnList.length = 139 := by decide +kernel
end AEGIS.CvSFullCachedTableV1
#print axioms AEGIS.CvSFullCachedTableV1.column_count
'''
(w/'CvSFullCachedTableV1.lean').write_text(s)
# Change output checks to a single, finite list traversal per column. All orientations included.
import json
D=json.loads((w/'EXACT_FULL_INPUTS.json').read_text())
for j in range(139):
 s='/- All 139 ordered output entries of one unchanged original matrix column. -/\nimport CvSFullCachedTableV1\nimport RowBudgetListCell0Pilot\nimport CvSRelativeRowCertificateL12V1\n'
 s+='''open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSFullCachedTableV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''+f'namespace AEGIS.CvSCachedOutput{j}\n'
 s+='def q : List Iv := ['+', '.join(f'⟨{row[j][0]}, {row[j][1]}⟩' for row in D['QI'])+']\n'
 s+=f'''def check (i : ℕ) : Bool :=
  contains (AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals i {j})
    (downscale 16 (value (q.getD i ⟨0, 0⟩) AEGIS.RowBudgetListCell0Pilot.LP2
      (column i).x (column i).dx (column i).z (column {j}).z
      (column {j}).gx (column {j}).gdx))
theorem checked : (List.range 139).all check = true := by decide +kernel
/-- Every row occurs in the finite acceptance check, with its original target. -/
theorem all_rows (i : Fin 139) : check i.val = true :=
  List.all_eq_true.mp checked i.val (List.mem_range.mpr i.isLt)
end AEGIS.CvSCachedOutput{j}
#print axioms AEGIS.CvSCachedOutput{j}.checked
#print axioms AEGIS.CvSCachedOutput{j}.all_rows
'''
 (w/f'CvSCachedOutput{j}.lean').write_text(s)
