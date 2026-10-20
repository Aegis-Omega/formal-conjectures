from pathlib import Path
import json,hashlib
w=Path('/workspace/aegis-row-budget-bridge')
prefix=(w/'build_cell_pilot.py').read_text().split('pair=lambda')[0]
state={};exec(compile(prefix,'unchanged-input-reconstruction','exec'),state)
ns=state['ns'];D=state['D']
pair=lambda a,i,j:[int(a[0][i,j]),int(a[1][i,j])]
fmt=lambda v:f'⟨{v[0]}, {v[1]}⟩'
lst=lambda vs:'['+', '.join(map(fmt,vs))+']'
outputs=[]
for b,start in enumerate(range(0,139,10)):
    stop=min(start+10,139)
    s='''/- First-column arithmetic only; original target boxes, unchanged Q96 inputs. -/
import CvSFirstColumnCheckerV1
import CvSRelativeRowCertificateL12V1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSFirstColumnCheckerV1
namespace AEGIS.RowBudgetFirstColumnBatch'''+str(b)+'''
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
    for i in range(start,stop):
        s+=f'def entry{i} : Entry := {{\n row := ⟨{i}, by decide⟩\n q := '+fmt(pair(ns['QI'],i,0))+'\n'
        for name,key,n in [('a','X',141),('da','DX',141),('u','Z',301)]:
            s+=f' {name} := '+lst([pair(ns[key],k,i) for k in range(n)])+'\n'
        s+=' target := '+fmt(D['I'][i][0])+' }\n'
    s+='def entries : List Entry := ['+', '.join('entry'+str(i) for i in range(start,stop))+']\n'
    s+='theorem checked : entries.all check = true := by decide +kernel\n'
    s+='theorem target_source : entries.all (fun e => decide (e.target = AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals e.row.val 0)) = true := by decide +kernel\n'
    s+='theorem row_order : entries.map (fun e => e.row.val) = List.range\' '+str(start)+' '+str(stop-start)+' := by decide +kernel\n'
    s+='end AEGIS.RowBudgetFirstColumnBatch'+str(b)+'\n'
    for root in ['checked','target_source','row_order']:s+='#print axioms AEGIS.RowBudgetFirstColumnBatch'+str(b)+'.'+root+'\n'
    p=w/f'RowBudgetFirstColumnBatch{b}.lean';p.write_text(s)
    outputs.append({'path':p.name,'rows':[start,stop],'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(w/'FIRST_COLUMN_INPUT_PROVENANCE.json').write_text(json.dumps({'scope':'139 first-column entries only; not complete 139-square table, actual input identification or hB/RH','input_reconstruction':'Existing exact integer interval generator, fixed stored rational Q48 projection, no floating fitting','python_all_19321_output_cells_match_stored':True,'target_source':'Original CvSRelativeRowCertificateL12V1.intervals; kernel target_source checks per batch','files':outputs},indent=2)+'\n')
print('EMITTED',len(outputs),'batches',flush=True)
