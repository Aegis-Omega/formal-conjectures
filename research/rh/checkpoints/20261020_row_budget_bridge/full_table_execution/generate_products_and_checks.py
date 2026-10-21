from pathlib import Path
import json
w=Path(__file__).resolve().parent;D=json.loads((w/'EXACT_FULL_INPUTS.json').read_text())
head='''open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSListIntervalDotV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
for i in range(139):
 s=f'''/- Exact original Gram-column products, evaluated using verified caches. -/
import CvSCachedGramV1
import CvSCachedInput{i}
{head}namespace AEGIS.CvSCachedProduct{i}
open AEGIS.CvSCachedInput{i} AEGIS.CvSCachedGramV1
'''
 for a,ga in [('x','gx'),('dx','gdx')]:
  s+=f'''theorem {ga}_checked : rows.map (fun g => evalDot g {a}) = {ga}.values := by decide +kernel
theorem {ga}_exact : {ga}.values = AEGIS.RowBudgetListCell0Pilot.G.map
    (fun row => listDot 96 row {a}.values) := by
  rw [← {ga}_checked, gram_product_eq, source_exact]
'''
 s+=f'end AEGIS.CvSCachedProduct{i}\n'
 for n in ['gx_checked','gx_exact','gdx_checked','gdx_exact']:s+=f'#print axioms AEGIS.CvSCachedProduct{i}.{n}\n'
 (w/f'CvSCachedProduct{i}.lean').write_text(s)
# The entire matrix is tested in original ordered orientations, not only its symmetric half.
for j in range(139):
 s='/- All 139 output entries of one unchanged original matrix column. -/\nimport CvSCachedInputsV1\nimport RowBudgetListCell0Pilot\nimport CvSRelativeRowCertificateL12V1\n'+head+f'namespace AEGIS.CvSCachedOutput{j}\n'
 s+='def q : List Iv := ['+', '.join(f'⟨{row[j][0]}, {row[j][1]}⟩' for row in D['QI'])+']\n'
 # Explicit per-entry theorems avoid repeatedly looking up a tail in a large list.
 for start in range(0,139,10):
  end=min(139,start+10)
  conditions=[]
  for i in range(start,end):
   conditions.append(f'contains (AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals {i} {j}) (downscale 16 (value (q.getD {i} ⟨0, 0⟩) AEGIS.RowBudgetListCell0Pilot.LP2 AEGIS.CvSCachedInput{i}.x AEGIS.CvSCachedInput{i}.dx AEGIS.CvSCachedInput{i}.z AEGIS.CvSCachedInput{j}.z AEGIS.CvSCachedInput{j}.gx AEGIS.CvSCachedInput{j}.gdx)) = true')
  s+=f'theorem checked{start//10} : '+ ' ∧\n '.join(conditions)+' := by decide +kernel\n'
  s+=f'#print axioms checked{start//10}\n'
 s+=f'end AEGIS.CvSCachedOutput{j}\n'
 (w/f'CvSCachedOutput{j}.lean').write_text(s)
print('Generated 139 product proof files and 139 output proof files')
