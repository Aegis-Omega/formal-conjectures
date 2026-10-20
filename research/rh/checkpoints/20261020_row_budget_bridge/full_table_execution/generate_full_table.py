"""Literal caches of unchanged exact interval data, with kernel proof obligations.
No numerical fitting is performed. Reuse checked first-column source fields.
"""
from pathlib import Path
import json,sys,hashlib
sys.set_int_max_str_digits(0)
w=Path(__file__).resolve().parent
D=json.loads((w/'EXACT_FULL_INPUTS.json').read_text());base=1<<280;bound=1<<128
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
 for v in reversed(a):r=(v+bound)+base*r
 return r

def cache(a):
 m=[(lo+hi)//2 for lo,hi in a];r=[max(mi-lo,hi-mi) for (lo,hi),mi in zip(a,m)]
 def p(v):
  assert all(-bound<=x<=bound for x in v)
  return f'⟨{pack(v)}, {pack(v[::-1])}, {sum(v)}, {len(v)}⟩'
 return '⟨'+',\n'.join(map(p,[m,list(map(abs,m)),r]))+'⟩'

def vec(name,a,values):
 return f'''def {name} : Vector {len(a)} := {{
 values := {values}
 cache := {cache(a)}
 length_eq := by decide +kernel
 components := by unfold bounded; decide +kernel
 preparation := by decide +kernel }}
'''
for start in range(0,141,10):
 b=start//10;s='/- Cached rows of the original rational harmonic Gram enclosure. -/\nimport CvSCachedColumnV1\nimport RowBudgetListCell0Pilot\n'+head+'namespace AEGIS.CvSCachedGramRows'+str(b)+'\n'
 for i in range(start,min(start+10,141)):
  s+=vec('row'+str(i),D['G'][i],f'AEGIS.RowBudgetListCell0Pilot.G.getD {i} []')
 s+='end AEGIS.CvSCachedGramRows'+str(b)+'\n'
 (w/f'CvSCachedGramRows{b}.lean').write_text(s)
s='/- All original Gram rows, with verified packing identities. -/\n'+''.join(f'import CvSCachedGramRows{b}\n' for b in range(15))+head+'namespace AEGIS.CvSCachedGramV1\n'
s+='def rows : List (Vector 141) := ['+', '.join(f'AEGIS.CvSCachedGramRows{i//10}.row{i}' for i in range(141))+']\n'
s+='theorem source_exact : rows.map Vector.values = AEGIS.RowBudgetListCell0Pilot.G := by decide +kernel\nend AEGIS.CvSCachedGramV1\n#print axioms AEGIS.CvSCachedGramV1.source_exact\n'
(w/'CvSCachedGramV1.lean').write_text(s)
for i in range(139):
 ns=f'AEGIS.RowBudgetFirstColumnBatch{i//10}.entry{i}'
 s='/- Cached unchanged source column; no refitting or interval tightening. -/\nimport CvSCachedColumnV1\n'+f'import RowBudgetFirstColumnBatch{i//10}\n'+head+f'namespace AEGIS.CvSCachedInput{i}\n'
 for name,key,field in [('x','X','a'),('dx','DX','da'),('z','Z','u'),('gx','GX',None),('gdx','GDX',None)]:
  a=[row[i] for row in D[key]]
  s+=vec(name,a,ns+'.'+field if field else lst(a))
 s+=f'end AEGIS.CvSCachedInput{i}\n'
 (w/f'CvSCachedInput{i}.lean').write_text(s)
s='/- All cached original input columns. -/\n'+''.join(f'import CvSCachedInput{i}\n' for i in range(139))+head+'namespace AEGIS.CvSCachedInputsV1\n'
for name,n in [('x',141),('dx',141),('z',301),('gx',141),('gdx',141)]:
 s+=f'def {name} : List (Vector {n}) := ['+', '.join(f'AEGIS.CvSCachedInput{i}.{name}' for i in range(139))+']\n'
s+='end AEGIS.CvSCachedInputsV1\n'
(w/'CvSCachedInputsV1.lean').write_text(s)
receipt={'input_sha256':hashlib.sha256((w/'EXACT_FULL_INPUTS.json').read_bytes()).hexdigest(),'fixed_projection':'unchanged Q48 original ROW_BUDGET_DATA.json','dimension':139,'frequency_count':141,'residual_rows':301,'scale':96,'target_scale':80,'packing_base_bits':280,'packing_signed_bound_bits':128,'status':'GENERATED_NOT_YET_KERNEL_VERIFIED'}
(w/'FULL_TABLE_GENERATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Generated',len(list(w.glob('*.lean'))),'modules',sum(p.stat().st_size for p in w.glob('*.lean')),'bytes')
