from pathlib import Path
w=Path(__file__).resolve().parent
s='/- Complete staged arithmetic for the actual source-input join. -/\nimport CvSCachedPointV1\nimport CvSSourceECacheV1\nimport CvSSourceXCacheV1\nimport CvSSourceLambdaCacheV1\nimport CvSFullCachedTableV1\n'
s+=''.join(f'import CvSSourceProduct{i}\n' for i in range(139))
s+='''import Mathlib.Tactic.FinCases
open scoped BigOperators
namespace AEGIS.CvSSourceProductAllV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1
open AEGIS.CvSCachedSourceProductV1 AEGIS.CvSCachedPointV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def inputColumn (i : Fin 139) := AEGIS.CvSFullCachedTableV1.column i.val
def eRow (r : Fin 301) : Vector 141 := AEGIS.CvSSourceECacheV1.rows.getD r.val
  AEGIS.CvSSourceERows0.row0
def xRow (k : Fin 141) : Vector 139 := AEGIS.CvSSourceXCacheV1.rows.getD k.val
  AEGIS.CvSSourceXRows0.row0
def lambdaColumn (i : Fin 139) : Vector 139 := AEGIS.CvSSourceLambdaCacheV1.rows.getD i.val
  AEGIS.CvSSourceLambdaRows0.row0
def lambdaBox (j i : Fin 139) : Iv := (lambdaColumn i).values.getD j.val ⟨0, 0⟩
noncomputable def lambdaReal (j i : Fin 139) : ℝ := ((lambdaBox j i).lo : ℝ) / 2^96
'''
for name,source in [('ys','Y'),('inners','inner')]:s+=f'def {name} : List (List Iv) := ['+', '.join(f'AEGIS.CvSSourceProduct{i}.{source}' for i in range(139))+']\n'
s+='''def Y (r : Fin 301) (i : Fin 139) : Iv := (ys.getD i.val []).getD r.val ⟨0, 0⟩
def inner (k : ℕ) (i : Fin 139) : Iv := (inners.getD i.val []).getD k ⟨0, 0⟩

theorem x_transpose (k : Fin 141) (i : Fin 139) :
    (xRow k).values.getD i.val ⟨0, 0⟩ = (inputColumn i).x.values.getD k.val ⟨0, 0⟩ := by
  fin_cases k
'''
for k in range(141):s+=f'  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows{k//10}.transpose{k} i.val (List.mem_range.mpr i.isLt))\n'
s+='''theorem lambda_point (j i : Fin 139) : (lambdaBox j i).lo = (lambdaBox j i).hi := by
  fin_cases i
'''
for i in range(139):s+=f'  · exact point_entry AEGIS.CvSSourceLambdaRows{i//10}.row{i} AEGIS.CvSSourceLambdaRows{i//10}.point{i} j\n'
s+='''theorem lambda_mem (j i : Fin 139) : (lambdaBox j i).Mem 96 (lambdaReal j i) :=
  point_mem 96 _ (lambda_point j i)

theorem Y_cached (i : Fin 139) : AEGIS.CvSSourceECacheV1.rows.map
    (fun row => evalDot row (inputColumn i).x) = ys.getD i.val [] := by
  fin_cases i
'''
for i in range(139):s+=f'  · exact AEGIS.CvSSourceProduct{i}.Y_checked\n'
s+='''theorem inner_cached (i : Fin 139) : AEGIS.CvSSourceXCacheV1.rows.map
    (fun row => evalDot row (lambdaColumn i)) = inners.getD i.val [] := by
  fin_cases i
'''
for i in range(139):s+=f'  · exact AEGIS.CvSSourceProduct{i}.inner_checked\n'
s+='''theorem Y_entry (r : Fin 301) (i : Fin 139) : Y r i =
    AEGIS.CvSListIntervalDotV1.listDot 96 (eRow r).values (inputColumn i).x.values :=
  product_entry_eq (by decide) (by decide) AEGIS.CvSSourceECacheV1.rows
    AEGIS.CvSSourceERows0.row0 (inputColumn i).x (ys.getD i.val [])
    AEGIS.CvSSourceECacheV1.length_eq (Y_cached i) r

theorem inner_entry (k : Fin 141) (i : Fin 139) : inner k.val i =
    AEGIS.CvSListIntervalDotV1.listDot 96 (xRow k).values (lambdaColumn i).values :=
  product_entry_eq (by decide) (by decide) AEGIS.CvSSourceXCacheV1.rows
    AEGIS.CvSSourceXRows0.row0 (lambdaColumn i) (inners.getD i.val [])
    AEGIS.CvSSourceXCacheV1.length_eq (inner_cached i) k

theorem Z_entry (r : Fin 301) (i : Fin 139) :
    (inputColumn i).z.values.getD r.val ⟨0, 0⟩ =
      if 80 ≤ r.val ∧ r.val < 221 then (Y r i).add (inner (r.val - 80) i).neg
      else Y r i := by
  fin_cases i
'''
for i in range(139):s+=f'  · exact AEGIS.CvSSourceProduct{i}.Z_exact r\n'
s+='end AEGIS.CvSSourceProductAllV1\n'
for n in ['x_transpose','lambda_point','lambda_mem','Y_cached','inner_cached','Y_entry','inner_entry','Z_entry']:
 s+=f'#check @AEGIS.CvSSourceProductAllV1.{n}\n#print axioms AEGIS.CvSSourceProductAllV1.{n}\n'
(w/'CvSSourceProductAllV1.lean').write_text(s)
print('Generated whole-source product composition candidate')
