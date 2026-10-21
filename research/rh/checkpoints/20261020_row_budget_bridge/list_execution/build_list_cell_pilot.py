from pathlib import Path
import json,hashlib
w=Path('/workspace/aegis-row-budget-bridge');d=json.loads((w/'CELL0_INPUTS.json').read_text());P=96;S=1<<P
fmt=lambda v:f'⟨{v[0]}, {v[1]}⟩'
def mul(a,b):
 c=[a[i]*b[j] for i in range(2) for j in range(2)];return [min(c)//S,-((-max(c))//S)]
def dot(a,b):
 am=[(x+y)//2 for x,y in a];ar=[max(m-x,y-m) for (x,y),m in zip(a,am)];bm=[(x+y)//2 for x,y in b];br=[max(m-x,y-m) for (x,y),m in zip(b,bm)];c=sum(x*y for x,y in zip(am,bm));r=sum(abs(x)*yr+xr*abs(y)+xr*yr for x,xr,y,yr in zip(am,ar,bm,br));return [(c-r)//S,-((-(c+r))//S)]
dx=[mul(t,x) for t,x in zip(d['T'],d['X0'])];gx=[dot(row,d['X0']) for row in d['G']];gdx=[dot(row,dx) for row in d['G']]
s='''/- Closed first output entry, preserving all recovered input bytes and rounding.
This is one entry, not the full output table, actual hB, a window theorem or RH. -/
import CvSListIntervalDotV1
import CvSRowBudgetEnvelopeV1
import RowBudgetStagedDotPilot
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSRowBudgetEnvelopeV1 AEGIS.CvSListIntervalDotV1
open AEGIS.RowBudgetStagedDotPilot
namespace AEGIS.RowBudgetListCell0Pilot
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
for i,row in enumerate(d['G']):s+=f'private def GRow{i} : List Iv := ['+', '.join(fmt(v) for v in row)+']\n'
s+='def G : List (List Iv) := ['+', '.join('GRow'+str(i) for i in range(141))+']\n'
for name,v in [('Z0',d['Z0']),('GX0',gx),('GDX0',gdx)]:s+=f'def {name} : List Iv := ['+', '.join(fmt(a) for a in v)+']\n'
for name in ['Q00','LP2','target']:s+=f'def {name} : Iv := '+fmt(d[name] if name!='target' else d['target'])+'\n'
s+='''theorem X_length : X0.length = 141 := by decide +kernel
theorem DX_length : DX0.length = 141 := by decide +kernel
theorem Z_length : Z0.length = 301 := by decide +kernel
theorem G_length : G.length = 141 := by decide +kernel
theorem G_rows : ∀ k : Fin 141, (G.getD k.val []).length = 141 := by decide +kernel

theorem gram_source_exact : G.map (fun row => listDot 96 row X0) = GX0 := by
  decide +kernel

theorem gram_weighted_exact : G.map (fun row => listDot 96 row DX0) = GDX0 := by
  decide +kernel

def fastEnvelope : Iv := downscale 16
  ((((point 96 40).mul 96 Q00).add (listDot 96 Z0 Z0).neg).add
    (LP2.mul 96 (((point 96 2).mul 96
      (listDot 96 DX0 (G.map (fun row => listDot 96 row DX0)))).add
      ((point 96 338).mul 96 (listDot 96 X0 (G.map (fun row => listDot 96 row X0)))))).neg)

theorem stored_cell0_fast : fastEnvelope = target := by
  unfold fastEnvelope
  rw [gram_source_exact, gram_weighted_exact]
  decide +kernel

def originalEnvelope : Iv := downscale 16 (envelope 96
  (fun (_ _ : Fin 1) => Q00)
  (fun (k : Fin 141) (_ : Fin 1) => X0.getD k.val ⟨0, 0⟩)
  (fun (k l : Fin 141) => (G.getD k.val []).getD l.val ⟨0, 0⟩)
  (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩)
  (fun (k : Fin 301) (_ : Fin 1) => Z0.getD k.val ⟨0, 0⟩) LP2 0 0)

/-- Refactoring equality, using the previously verified weighted column. -/
theorem original_eq_fast : originalEnvelope = fastEnvelope := by
  have hw : weighted 96 (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩)
      (fun (k : Fin 141) (_ : Fin 1) => X0.getD k.val ⟨0, 0⟩) =
      (fun (k : Fin 141) (_ : Fin 1) => DX0.getD k.val ⟨0, 0⟩) := by
    funext k i
    exact weighted_column_exact k
  unfold originalEnvelope
  simp only [envelope, sub, scale, add]
  rw [hw, listCongruence_eq 96 DX0 G DX_length G_length G_rows,
    listCongruence_eq 96 X0 G X_length G_length G_rows]
  simp only [matrixMul]
  rw [← listDot_eq_dot 96 Z0 Z0 Z_length Z_length]
  rfl

/-- The original envelope's first stored Q80 output is now kernel replayed. -/
theorem stored_cell0_original : originalEnvelope = target :=
  original_eq_fast.trans stored_cell0_fast

end AEGIS.RowBudgetListCell0Pilot
'''
for n in ['gram_source_exact','gram_weighted_exact','stored_cell0_fast','original_eq_fast','stored_cell0_original']:s+='#print axioms AEGIS.RowBudgetListCell0Pilot.'+n+'\n'
p=w/'RowBudgetListCell0Pilot.lean';p.write_text(s)
rec={'input_source':'CELL0_INPUTS.json','input_sha256':hashlib.sha256((w/'CELL0_INPUTS.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'Complete first output entry, plus equivalence to original envelope. Not all 19,321 entries, actual input memberships, hB or RH.','unchanged_input':'Same Q00, X0, T, G, Z0 and LP2 from the earlier resource-terminated monolithic attempt; old X0/T/DX0 imported from previously verified staged source.','new_witnesses':'Only GX0/GDX0, proposed by exact integer arithmetic and checked by kernel.'}
(w/'LIST_CELL0_PROVENANCE.json').write_text(json.dumps(rec,indent=2)+'\n');print('emitted',len(s.encode()),flush=True)
