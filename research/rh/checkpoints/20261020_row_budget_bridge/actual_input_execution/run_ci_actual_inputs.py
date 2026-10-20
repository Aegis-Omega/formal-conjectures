"""Original-import source replay with dependency barriers and bounded memory use."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import os,sys,json,zipfile,hashlib,subprocess,re,time
repo=Path.cwd();d=repo/'research/rh/checkpoints/20261020_row_budget_bridge/actual_input_execution';out=repo/'.lake/actual-input-sources';out.mkdir(parents=True,exist_ok=True);ring=repo/'.lake/ringout'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((d/'ACTUAL_INPUT_SOURCE_MANIFEST.json').read_text());arc=d/'ACTUAL_INPUT_SOURCES.zip';assert digest(arc)==m['archive_sha256']
with zipfile.ZipFile(arc) as z:
 assert len(z.namelist())==len(set(z.namelist()))
 for name in z.namelist():
  assert Path(name).name==name and not Path(name).is_absolute()
  if name.endswith('.lean'):(out/name).write_bytes(z.read(name))
 source_json_sha=hashlib.sha256(z.read('EXACT_SOURCE_BRIDGE_INPUTS.json')).hexdigest()
for a in m['sources']:assert digest(out/a['name'])==a['sha256']
expected_source=json.loads((repo/'research/rh/checkpoints/20261020_row_budget_bridge/full_table_execution/SOURCE_BINDING_NEXT_INPUTS.json').read_text())['sha256'];assert source_json_sha==expected_source
phases=[['CvSCachedSourceProductV1'],[f'CvSSourceERows{i}' for i in range(31)],['CvSSourceECacheV1'],[f'CvSSourceXRows{i}' for i in range(15)],['CvSSourceXCacheV1'],[f'CvSSourceLambdaRows{i}' for i in range(14)],['CvSSourceLambdaCacheV1'],[f'CvSSourceProduct{i}' for i in range(139)],['CvSCachedPointV1','CvSCachedSliceV1','CvSSourceQNormalizeV1'],['CvSSourceProductAllV1'],[f'CvSSourceQCache{i}' for i in range(14)],[f'CvSSourceQCheck{i}' for i in range(139)],['CvSSourceQAllV1'],['CvSSourceQRejectV1'],[f'CvSAnalyticERows{i}' for i in range(31)],[f'CvSAnalyticXColumns{i}' for i in range(14)],[f'CvSAnalyticGRows{i}' for i in range(15)],['CvSAnalyticScalarInputsV1'],['CvSActualLiteralInputsV1'],['CvSActualBasisBudgetV1']]
names=[name for phase in phases for name in phase];assert len(names)==len(set(names))==425
memory=os.sysconf('SC_PHYS_PAGES')*os.sysconf('SC_PAGE_SIZE')
p=Path('/sys/fs/cgroup/memory.max')
if p.exists() and p.read_text().strip()!='max':memory=min(memory,int(p.read_text()))
workers=2 if memory>=12*1024**3 else 1
# The existing public runner has 16 GiB. Smaller runners remain sequential.
env=os.environ.copy();env['LEAN_PATH']=str(ring)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
r={'commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean':subprocess.check_output(['lean','--version'],text=True).strip(),'mathlib':subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip(),'status':'RUNNING','source_archive_sha256':digest(arc),'source_json_sha256':source_json_sha,'worker_count':workers,'memory_limit_bytes':memory,'planned_modules':names,'scope':'Fresh original-import source compilation of staged source products, 2*pi-normalized Q enclosures, literal analytic box identities and the actual finite relative-budget producer. Not RH.','runs':[]}
assert r['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
logs=[];audits={};rp=repo/'ACTUAL_INPUT_CI_RECEIPT.json';lp=repo/'actual-input-replay.log'
def compile_one(name):
 src=out/(name+'.lean');cmd=['lean','-DwarningAsError=true','-R',str(out),'-o',str(ring/(name+'.olean')),str(src)];t=time.monotonic();p=subprocess.run(cmd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 return {'module':name,'source_sha256':digest(src),'command':cmd,'seconds':time.monotonic()-t,'exit_code':p.returncode,'compiler_output':p.stdout}
def record(entry):
 text=entry['compiler_output'];bad=[]
 for decl,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
  xs=[x.strip() for x in ax.split(',') if x.strip()];audits[decl]=xs
  if not set(xs)<={'propext','Classical.choice','Quot.sound'}:bad.append((decl,xs))
 for decl in re.findall(r"'([^']+)' does not depend on any axioms",text):audits[decl]=[]
 entry['bad_axioms']=bad;entry['status']='PASS' if entry['exit_code']==0 and not bad else 'FAIL'
 r['runs'].append(entry);r['axiom_audits']=audits;logs.append(entry['module']+'\n'+text)
 lp.write_text('\n'.join(logs));rp.write_text(json.dumps(r,indent=2)+'\n')
 print('ACTUAL_INPUT_KERNEL_MODULE',entry['module'],entry['status'],round(entry['seconds'],3),flush=True)
 if entry['status']=='FAIL':print(text,flush=True)
 return entry['status']=='FAIL'
with ThreadPoolExecutor(max_workers=workers) as pool:
 for number,phase in enumerate(phases):
  r['current_phase']=number;failed=False
  for future in as_completed([pool.submit(compile_one,name) for name in phase]):failed=record(future.result()) or failed
  if failed:
   r['status']='FAIL';rp.write_text(json.dumps(r,indent=2)+'\n');sys.exit(1)
terminal='AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin';assert terminal in audits,'MISSING_ACTUAL_TERMINAL_AUDIT'
assert 'AEGIS.CvSActualBasisBudgetV1.actualBudget_le_original' in audits,'MISSING_ACTUAL_TRANSPORT_AUDIT'
r.update(status='PASS',actual_terminal=terminal,actual_scope='For every M >= 3 and every complex vector, the actual sourceZ residual and proved Gram-tail majorant satisfy the quantitative 40*projectedEntry budget. Fixed window only; no RH conclusion.')
rp.write_text(json.dumps(r,indent=2)+'\n')
print('ACTUAL_INPUT_KERNEL_PASS',len(names),'modules',len(audits),'axiom roots; actual finite source budget; NOT_RH',flush=True)
