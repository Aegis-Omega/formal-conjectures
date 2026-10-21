"""Keep original E/Y/Lambda/X*Lambda bytes; verify caches and staged products in Lean."""
from pathlib import Path
import json,sys,hashlib
sys.set_int_max_str_digits(0)
w=Path(__file__).resolve().parent;full=Path('/workspace/aegis-full-table-bridge');D=json.loads((w/'EXACT_SOURCE_BRIDGE_INPUTS.json').read_text());F=json.loads((full/'EXACT_FULL_INPUTS.json').read_text())
base=1<<280;bound=1<<128
fmt=lambda a:f'⟨{a[0]}, {a[1]}⟩'
lst=lambda a:'['+', '.join(map(fmt,a))+']'
head='''open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSPackedIntervalDotV1 AEGIS.CvSCachedColumnV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
def pack(a):
 r=0
 for x in reversed(a):r=(x+bound)+base*r
 return r

def cache(a):
 m=[(lo+hi)//2 for lo,hi in a];r=[max(mi-lo,hi-mi) for (lo,hi),mi in zip(a,m)]
 def p(v):
  assert all(-bound<=x<=bound for x in v)
  return f'⟨{pack(v)}, {pack(v[::-1])}, {sum(v)}, {len(v)}⟩'
 return '⟨'+',\n'.join(map(p,[m,list(map(abs,m)),r]))+'⟩'

def vec(name,a):
 return f'''def {name} : Vector {len(a)} := {{
 values := {lst(a)}
 cache := {cache(a)}
 length_eq := by decide +kernel
 components := by unfold bounded; decide +kernel
 preparation := by decide +kernel }}
'''
for key,rows in [('E',D['E']),('X',F['X']),('Lambda',[[D['Lam'][j][i] for j in range(139)] for i in range(139)])]:
 for start in range(0,len(rows),10):
  b=start//10;ns=f'CvSSource{key}Rows{b}'
  s='/- Original source-input interval row cache; no analytic membership claimed here. -/\nimport CvSCachedSourceProductV1\n'
  if key=='X':s+='import CvSFullCachedTableV1\n'
  s+=head+f'namespace AEGIS.{ns}\n'
  for i in range(start,min(start+10,len(rows))):
   s+=vec('row'+str(i),rows[i])
   if key=='X':
    s+=f'''theorem transpose{i} : (List.range 139).all (fun j => decide
      ((row{i}.values.getD j ⟨0, 0⟩) = (AEGIS.CvSFullCachedTableV1.column j).x.values.getD {i} ⟨0, 0⟩)) = true := by decide +kernel
'''
   if key=='Lambda':s+=f'theorem point{i} : row{i}.values.all (fun a => decide (a.lo = a.hi)) = true := by decide +kernel\n'
  s+=f'end AEGIS.{ns}\n'
  if key in ['X','Lambda']:
   for i in range(start,min(start+10,len(rows))):s+=f'#print axioms AEGIS.{ns}.'+('transpose' if key=='X' else 'point')+str(i)+'\n'
  (w/(ns+'.lean')).write_text(s)
 n=len(rows);dim=len(rows[0]);ns=f'CvSSource{key}CacheV1'
 s=''.join(f'import CvSSource{key}Rows{b}\n' for b in range((n+9)//10))+head+f'namespace AEGIS.{ns}\n'
 s+=f'def rows : List (Vector {dim}) := ['+', '.join(f'AEGIS.CvSSource{key}Rows{i//10}.row{i}' for i in range(n))+']\n'
 s+=f'theorem length_eq : rows.length = {n} := by decide +kernel\n'
 s+=f'end AEGIS.{ns}\n#print axioms AEGIS.{ns}.length_eq\n'
 (w/(ns+'.lean')).write_text(s)
for i in range(139):
 s='/- Source residual products: exact cache identities, with original Q96 endpoints. -/\nimport CvSSourceECacheV1\nimport CvSSourceXCacheV1\n'+f'import CvSSourceLambdaRows{i//10}\nimport CvSCachedInput{i}\n'+head+f'namespace AEGIS.CvSSourceProduct{i}\n'
 s+='open AEGIS.CvSCachedSourceProductV1 AEGIS.CvSListIntervalDotV1\n'
 s+='def Y : List Iv := '+lst([row[i] for row in D['Y']])+'\n'
 s+='def inner : List Iv := '+lst([row[i] for row in D['inside']])+'\n'
 s+=f'''theorem Y_checked : AEGIS.CvSSourceECacheV1.rows.map
    (fun row => evalDot row AEGIS.CvSCachedInput{i}.x) = Y := by decide +kernel
theorem inner_checked : AEGIS.CvSSourceXCacheV1.rows.map
    (fun row => evalDot row AEGIS.CvSSourceLambdaRows{i//10}.row{i}) = inner := by decide +kernel
theorem Y_exact : Y = (AEGIS.CvSSourceECacheV1.rows.map Vector.values).map
    (fun row => listDot 96 row AEGIS.CvSCachedInput{i}.x.values) := by
  rw [← Y_checked, mapped_dots_eq (by decide) (by decide)]
theorem inner_exact : inner = (AEGIS.CvSSourceXCacheV1.rows.map Vector.values).map
    (fun row => listDot 96 row AEGIS.CvSSourceLambdaRows{i//10}.row{i}.values) := by
  rw [← inner_checked, mapped_dots_eq (by decide) (by decide)]
def residual (r : ℕ) : Iv := if 80 ≤ r ∧ r < 221 then
  (Y.getD r ⟨0, 0⟩).add (inner.getD (r - 80) ⟨0, 0⟩).neg
  else Y.getD r ⟨0, 0⟩
theorem Z_checked : (List.range 301).all (fun r => decide
    (AEGIS.CvSCachedInput{i}.z.values.getD r ⟨0, 0⟩ = residual r)) = true := by decide +kernel
theorem Z_exact (r : Fin 301) : AEGIS.CvSCachedInput{i}.z.values.getD r.val ⟨0, 0⟩ = residual r.val :=
  of_decide_eq_true (List.all_eq_true.mp Z_checked r.val (List.mem_range.mpr r.isLt))
end AEGIS.CvSSourceProduct{i}
'''
 for n in ['Y_checked','inner_checked','Y_exact','inner_exact','Z_checked','Z_exact']:s+=f'#print axioms AEGIS.CvSSourceProduct{i}.{n}\n'
 (w/f'CvSSourceProduct{i}.lean').write_text(s)
print('SOURCE_PRODUCT_CANDIDATES',len(list(w.glob('*.lean'))),'modules',sum(p.stat().st_size for p in w.glob('*.lean')),'bytes',flush=True)
