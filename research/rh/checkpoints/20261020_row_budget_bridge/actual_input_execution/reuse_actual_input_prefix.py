"""Validate reusable PASS modules of a completed actual-input run, including failed runs.
Only source-identical modules whose complete custom import prefix is reusable are copied.
A failed run is never classified as a proof of its failed or unexecuted terminal.
"""
from pathlib import Path
import io,json,hashlib,re,subprocess,zipfile,shutil,sys
REPO='tarikskalic33/formal-conjectures'
PREFIX='research/rh/checkpoints/20261020_row_budget_bridge/'
ACTUAL=PREFIX+'actual_input_execution/'
ALLOW={'propext','Classical.choice','Quot.sound'}
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,name):
 p=Path(name);assert not p.is_absolute() and '..' not in p.parts,'UNSAFE_ARCHIVE_PATH';return root/p

def main():
 run_id=int(sys.argv[1]);sha=sys.argv[2];target=Path(sys.argv[3]);root=Path.cwd()
 assert re.fullmatch('[0-9a-f]{40}',sha)
 run=json.loads(subprocess.check_output(['gh','api',f'repos/{REPO}/actions/runs/{run_id}'],text=True))
 assert run['head_sha']==sha and run['status']=='completed','PREFIX_RUN_NOT_COMPLETED_AT_EXACT_SHA'
 if subprocess.run(['git','cat-file','-e',sha+'^{commit}'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
  subprocess.run(['git','fetch','--no-tags','--depth=1','origin',sha],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
 # The original full-table source and all baseline binaries were validated separately.
 base=json.loads((root/'COMPLETE_TABLE_REUSE_RECEIPT.json').read_text())
 assert base['status']=='EXACT_SUCCESSFUL_FULL_TABLE_DEPENDENCIES_REUSED'
 assert base['source_commit']=='2d2ea90dd2db6d57a8d5cf4bbf7ac734566d3925'
 assert subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()==MATHLIB
 cache=root/'.lake'/('actual-prefix-'+str(run_id));cache.mkdir(parents=True,exist_ok=True)
 if '--validate-existing' not in sys.argv:
  subprocess.run(['gh','run','download',str(run_id),'--repo',REPO,'--name','source-cross-row-'+sha,'--dir',str(cache)],check=True,timeout=180)
 m=json.loads((cache/'SOURCE_CROSS_ROW_CHECKPOINT.json').read_text())
 r=json.loads((cache/'ACTUAL_INPUT_CI_RECEIPT.json').read_text())
 assert m['source_commit']==r['commit']==sha
 assert 'version 4.33.1' in r['lean'] and '819816b2e0' in r['lean']
 assert m['lean_toolchain']=='leanprover/lean4:v4.33.1' and m['mathlib_sha']==r['mathlib']==MATHLIB
 assert m['li_criterion_sha']=='35df682f3b709ffe5fbcfdd452dfa964bd622b87'
 assert (root/'lean-toolchain').read_text().strip()==m['lean_toolchain']
 for name,h in m['source_sha256'].items():
  if not name.startswith(ACTUAL):assert digest(safe(root,name))==h,'OTHER_LEAN_SOURCE_CHANGED '+name
 for name,h in m['log_sha256'].items():assert digest(safe(cache,name))==h,'OLD_LOG_CHANGED '+name
 old_bytes=subprocess.check_output(['git','show',sha+':'+ACTUAL+'ACTUAL_INPUT_SOURCES.zip'])
 old_manifest=json.loads(subprocess.check_output(['git','show',sha+':'+ACTUAL+'ACTUAL_INPUT_SOURCE_MANIFEST.json'],text=True))
 assert hashlib.sha256(old_bytes).hexdigest()==old_manifest['archive_sha256']==r['source_archive_sha256']
 assert m['source_archive_sha256'][ACTUAL+'ACTUAL_INPUT_SOURCES.zip']==r['source_archive_sha256']
 with zipfile.ZipFile(io.BytesIO(old_bytes)) as z:
  assert len(z.namelist())==len(set(z.namelist()))
  old={Path(n).stem:z.read(n) for n in z.namelist() if n.endswith('.lean')}
  for a in old_manifest['sources']:assert hashlib.sha256(old[Path(a['name']).stem]).hexdigest()==a['sha256']
 current_manifest=json.loads((root/ACTUAL/'ACTUAL_INPUT_SOURCE_MANIFEST.json').read_text())
 archive=root/ACTUAL/'ACTUAL_INPUT_SOURCES.zip';assert digest(archive)==current_manifest['archive_sha256']
 with zipfile.ZipFile(archive) as z:
  assert len(z.namelist())==len(set(z.namelist()))
  current={Path(n).stem:z.read(n) for n in z.namelist() if n.endswith('.lean')}
 for a in current_manifest['sources']:assert hashlib.sha256(current[Path(a['name']).stem]).hexdigest()==a['sha256']
 for name,origin in current_manifest.get('unchanged_existing_source_copies',{}).items():
  assert hashlib.sha256(current[Path(name).stem]).hexdigest()==origin['sha256']==digest(root/origin['original_path'])
 assert len(r['runs'])==len({a['module'] for a in r['runs']}),'DUPLICATE_MODULE_RECEIPTS'
 passed={};audits={}
 for a in r['runs']:
  name=a['module'];assert name in old and a['source_sha256']==hashlib.sha256(old[name]).hexdigest()
  if a['status']!='PASS' or a['exit_code']!=0:continue
  assert '-DwarningAsError=true' in a['command']
  text=a['compiler_output'];assert not re.search(r'error:|error\(lean|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler',text),'BAD_PASS_LOG '+name
  ax={}
  for decl,items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
   values=[s.strip() for s in items.split(',') if s.strip()];assert set(values)<=ALLOW,(decl,values);ax[decl]=values
  for decl in re.findall(r"'([^']+)' does not depend on any axioms",text):ax[decl]=[]
  if not ax:assert re.fullmatch(r'CvSSource(?:ERows|QCache)\d+',name),'NO_MODULE_AXIOM_AUDIT '+name
  passed[name]=a;audits[name]=ax
 # Verify every old binary; select only successful modules below.
 binaries=m['binary_sha256']
 for name,h in binaries.items():
  assert name.startswith('.lake/ringout/') and name.endswith('.olean')
  assert digest(safe(cache,name))==h,'OLD_BINARY_CHANGED '+name
 baseline=json.loads((root/'.lake/complete-table-checkpoint/SOURCE_CROSS_ROW_CHECKPOINT.json').read_text())['binary_sha256']
 for name,h in baseline.items():assert binaries[name]==h and digest(target/Path(name).relative_to('.lake/ringout'))==h,'BASE_BINARY_CHANGED '+name
 imports={n:re.findall(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)',s.decode(),re.M) for n,s in current.items()}
 eligible={n for n,a in passed.items() if n in current and a['source_sha256']==hashlib.sha256(current[n]).hexdigest()}
 # Remove all transitive dependants of a changed, failed or absent source module.
 while True:
  keep={n for n in eligible if all(i not in current or i in eligible for i in imports[n])}
  if keep==eligible:break
  eligible=keep
 old_stems={Path(n).stem for n in baseline}
 for n in eligible:
  assert all(i in current or i in old_stems or i.startswith(('Mathlib.','Lean.','Std.','Batteries.')) for i in imports[n]),'UNKNOWN_IMPORT '+n
  path='.lake/ringout/'+n+'.olean';assert path in binaries,'MISSING_PASS_BINARY '+n
  dst=target/(n+'.olean')
  if dst.exists():assert digest(dst)==binaries[path],'EXISTING_PREFIX_CONFLICT '+n
 for n in sorted(eligible):
  dst=target/(n+'.olean')
  if not dst.exists():shutil.copyfile(cache/'.lake/ringout'/(n+'.olean'),dst)
 data_modules=sorted(n for n in eligible if not audits[n])
 roots=[f'AEGIS.{n}.{decl}' for n in data_modules for decl in re.findall(r'^def\s+(\w+)',current[n].decode(),re.M)]
 assert all(any(x.startswith('AEGIS.'+n+'.') for x in roots) for n in data_modules)
 audit=''.join('import '+n+'\n' for n in data_modules)+''.join('#print axioms '+n+'\n' for n in roots)
 (root/'ACTUAL_INPUT_PREFIX_REAUDIT.lean').write_text(audit)
 receipt={'fresh_data_axiom_roots_required':roots,'status':'VALIDATED_SUCCESSFUL_SOURCE_IDENTICAL_PREFIX','source_run':run_id,'source_commit':sha,'source_run_conclusion':run['conclusion'],'old_terminal_status':r['status'],'source_archive_sha256':digest(archive),'validated_binary_count':len(binaries),'reused_modules':{n:{'run':passed[n],'axiom_audits':audits[n],'binary_sha256':binaries['.lake/ringout/'+n+'.olean']} for n in sorted(eligible)},'scope':'Only successful source-identical modules with a fully preserved custom import prefix. Failed or unexecuted terminal results are not reused or classified as proved.'}
 (root/'ACTUAL_INPUT_PREFIX_REUSE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('VALIDATED_ACTUAL_INPUT_PREFIX',len(eligible),'successful modules; old run conclusion',run['conclusion'])
def check_reaudit(log_path):
 root=Path.cwd();rp=root/'ACTUAL_INPUT_PREFIX_REUSE_RECEIPT.json';r=json.loads(rp.read_text());text=Path(log_path).read_text();found={}
 assert not re.search(r'error:|error\(lean|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler',text),'BAD_PREFIX_REAUDIT_LOG'
 for decl,items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
  values=[s.strip() for s in items.split(',') if s.strip()];assert set(values)<=ALLOW,(decl,values);found[decl]=values
 for decl in re.findall(r"'([^']+)' does not depend on any axioms",text):found[decl]=[]
 assert set(r['fresh_data_axiom_roots_required'])<=set(found),'MISSING_DATA_AXIOM_ROOT'
 out={'status':'PASS','prefix_receipt_sha256':digest(rp),'source_archive_sha256':r['source_archive_sha256'],'audits':found,'log_sha256':digest(Path(log_path))}
 (root/'ACTUAL_INPUT_PREFIX_AXIOM_RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
 print('ACTUAL_INPUT_PREFIX_DATA_AXIOMS_PASS',len(found))

if __name__=='__main__':
 try:
  if sys.argv[1]=='--check-reaudit':check_reaudit(sys.argv[2])
  else:main()
 except Exception as e:print('ACTUAL_INPUT_PREFIX_REJECTED',type(e).__name__,str(e));raise SystemExit(1)
