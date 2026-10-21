"""Replay every new mathematical module in the existing original-source CI context."""
from pathlib import Path
import os,sys,subprocess,json,zipfile,hashlib,re,time
repo=Path.cwd();d=repo/'research/rh/checkpoints/20261020_row_budget_bridge/full_table_execution';out=repo/'.lake/full-table-source';out.mkdir(parents=True,exist_ok=True)
manifest=json.loads((d/'SOURCE_MANIFEST.json').read_text());arc=d/'FULL_TABLE_SOURCES.zip'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(arc)==manifest['archive_sha256']
with zipfile.ZipFile(arc) as z:
 assert len(z.namelist())==len(set(z.namelist()))
 for name in z.namelist():
  assert Path(name).name==name and not Path(name).is_absolute()
  if name.endswith('.lean'):(out/name).write_bytes(z.read(name))
for row in manifest['sources']:assert digest(out/row['path'])==row['sha256']
ring=repo/'.lake/ringout';env=os.environ.copy();env['LEAN_PATH']=str(ring)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
extra={'CvSPackedIntervalDotV1':repo/'research/rh/checkpoints/20261020_row_budget_bridge/packed_execution/CvSPackedIntervalDotV1.lean','CvSRowBudgetAlgebraV1':repo/'research/rh/checkpoints/20261020_row_budget/CvSRowBudgetAlgebraV1.lean'}
names=['CvSPackedIntervalDotV1','CvSCachedColumnV1','CvSCachedEnvelopeJoinV1']+[f'CvSCachedGramRows{i}' for i in range(15)]+['CvSCachedGramV1']+[f'CvSCachedInput{i}' for i in range(139)]+['CvSCachedInputsV1','CvSFullCachedTableV1']+[f'CvSCachedProduct{i}' for i in range(139)]+[f'CvSCachedOutput{i}' for i in range(139)]+['CvSRowBudgetAlgebraV1','CvSRowBudgetGramBridgeV1','CvSRealTailMatrixV1','CvSStrictRowBudgetV1','CvSFullTableClosureV1','CvSFullBudgetJoinV1','CvSFullTableRejectV1']
receipt={'commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean':subprocess.check_output(['lean','--version'],text=True).strip(),'mathlib':subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip(),'status':'RUNNING','scope':'Fresh compilation of the entire new full-table extension against the original-source dependency context; input analytic memberships remain explicit. Not RH.','runs':[]}
assert receipt['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
logs=[];roots={}
for name in names:
 src=extra.get(name,out/(name+'.lean'));t=time.monotonic();cmd=['lean','-DwarningAsError=true','-R',str(src.parent),'-o',str(ring/(name+'.olean')),str(src)]
 r=subprocess.run(cmd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 logs.append(name+'\n'+r.stdout)
 for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",r.stdout):
  ax=[v.strip() for v in a.split(',') if v.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'},(n,ax);roots[n]=ax
 row={'module':name,'source_sha256':digest(src),'command':cmd,'seconds':time.monotonic()-t,'exit_code':r.returncode,'compiler_output':r.stdout};receipt['runs'].append(row)
 (repo/'full-table-replay.log').write_text('\n'.join(logs));(repo/'FULL_TABLE_CI_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('FULL_TABLE_KERNEL_MODULE',name,'PASS' if r.returncode==0 else 'FAIL',round(row['seconds'],3),flush=True)
 if r.returncode:print(r.stdout,flush=True);sys.exit(r.returncode)
required=['AEGIS.CvSFullTableClosureV1.full_table_contains','AEGIS.CvSFullTableClosureV1.real_envelope_mem','AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs','AEGIS.CvSFullTableRejectV1.reject_modified_cache']
assert all(n in roots for n in required),'MISSING_TERMINAL_AXIOM_AUDIT'
receipt.update(status='PASS',axiom_audits=roots,ordered_output_cells=139*139,source_product_columns=139*2)
(repo/'FULL_TABLE_CI_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('FULL_TABLE_KERNEL_PASS',len(names),'modules',len(roots),'axiom audits; 19321 ordered cells; actual input identities and universal RH not asserted',flush=True)
