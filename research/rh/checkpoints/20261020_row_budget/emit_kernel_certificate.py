from pathlib import Path
import json,hashlib
out=Path('/workspace/aegis-row-budget-recovery');d=json.loads((out/'ROW_BUDGET_DATA.json').read_text())
s='''/- Finite interval-box certificate for the proposed L=6/5 relative row budget.
The analytic source-to-interval correspondence remains a separate obligation.
No positivity of the actual CvS residual is asserted by this Boolean theorem. -/
import CvSPackedGramV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSPackedGramV1
namespace AEGIS.CvSRelativeRowCertificateL12V1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
for name in ['base','B','eps','eta']:
 s+=f'def {name} : '+('ℕ' if name in ['base','B'] else 'ℤ')+f' := {d[name]}\n'
for name,ty,rows in [('factor','ℤ',d['L']),('intervals','Iv',d['I'])]:
 for i,row in enumerate(rows):
  body=', '.join(str(v) if ty=='ℤ' else f'⟨{v[0]}, {v[1]}⟩' for v in row)
  s+=f'private def {name}Row{i} : List {ty} :=\n  [{body}]\n'
 s+=f'def {name} : List (List {ty}) :=\n  ['+', '.join(f'{name}Row{i}' for i in range(len(rows)))+']\n'
s+='''theorem row_budget_check_true :
    check base B 139 eps eta factor intervals = true := by
  decide +kernel

theorem row_budget_margin_positive : (0 : ℤ) < eps - eta := by
  decide +kernel
end AEGIS.CvSRelativeRowCertificateL12V1
#print axioms AEGIS.CvSRelativeRowCertificateL12V1.row_budget_check_true
#print axioms AEGIS.CvSRelativeRowCertificateL12V1.row_budget_margin_positive
'''
(out/'CvSRelativeRowCertificateL12V1.lean').write_text(s)
r=json.loads((out/'ROW_BUDGET_EXACT_RECEIPT.json').read_text());r['floating_point_use']='Least-squares proposes an exact rational projection; an eigenvalue hint proposes the shift; Decimal Cholesky proposes the integer factor. Only exact integer checks accept the certificate.';(out/'ROW_BUDGET_EXACT_RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
print('source_bytes',len(s.encode()),'sha256',hashlib.sha256(s.encode()).hexdigest())
