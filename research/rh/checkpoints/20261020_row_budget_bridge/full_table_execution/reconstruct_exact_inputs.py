"""Recover the exact matrices from committed source and the original Q48 witness.
This regenerates arithmetic data, not a Lean proof of analytic membership.
"""
from pathlib import Path
import json,zipfile,hashlib,sys,os
w=Path(__file__).resolve().parent
repo=Path(os.environ.get('AEGIS_REPOSITORY','/workspace/formal-conjectures'))
src=repo/'research/rh/checkpoints/20261020_row_budget/row_budget_exact.py'
code=src.read_text().split('# Deterministic rational Cholesky witness')[0]
with zipfile.ZipFile(src.parent/'ROW_BUDGET_INPUTS.zip') as z:
 names=[n for n in z.namelist() if Path(n).name=='ROW_BUDGET_DATA.json'];assert len(names)==1
 stored=json.loads(z.read(names[0]))
start=code.index('Y=mm(E,X);');end=code.index('Lam=(LI*',start)
code=code[:start]+"Y=mm(E,X)\nqproj=stored['projection_fractional_bits'];LI=np.array(stored['projection'],dtype=object)\n"+code[end:]
assert 'lstsq' not in code and 'dtype=float' not in code
ns={'stored':stored};exec(compile(code,str(src)+'[exact-prefix-only]','exec'),ns)
C=ns['C'];assert all((int(C[0][i,j])//(1<<16),-((-int(C[1][i,j]))//(1<<16)))==tuple(stored['I'][i][j]) for i in range(139) for j in range(139))
pair=lambda a,i,j:[int(a[0][i,j]),int(a[1][i,j])]
arrays={k:[[pair(ns[k],i,j) for j in range(ns[k][0].shape[1])] for i in range(ns[k][0].shape[0])] for k in ['X','DX','Z','G','QI']}
for key,source in [('GX','X'),('GDX','DX')]:
 a=ns['mm'](ns['G'],ns[source]);arrays[key]=[[pair(a,i,j) for j in range(139)] for i in range(141)]
arrays['LP2']=list(map(int,ns['mul'](ns['lp'],ns['lp'])));arrays['targets']=stored['I']
b=(json.dumps(arrays,separators=(',',':'))+'\n').encode();actual=hashlib.sha256(b).hexdigest()
assert actual=='69014b7fbf4246f20f6bc0a8ee1245b4d401315899511308b8c226b0606ec63c',actual
p=w/'EXACT_FULL_INPUTS.json'
if p.exists():assert p.read_bytes()==b
else:p.write_bytes(b)
print('EXACT_INPUT_RECONSTRUCTION_PASS',actual)
