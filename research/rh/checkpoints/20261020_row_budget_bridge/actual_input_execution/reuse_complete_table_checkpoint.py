"""Reuse only the exact, successful original-import full-table compilation.
This validates prior sources, pins, all compiler outputs and every binary.
It never represents reused dependencies as freshly compiled source.
"""
from pathlib import Path
import json,subprocess,hashlib,re,shutil,sys,zipfile
RUN=39505154095
SHA='2d2ea90dd2db6d57a8d5cf4bbf7ac734566d3925'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
PREFIX='research/rh/checkpoints/20261020_row_budget_bridge/'
ALLOW={'propext','Classical.choice','Quot.sound'}
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,name):
 p=Path(name);assert not p.is_absolute() and '..' not in p.parts,'UNSAFE_ARCHIVE_PATH';return root/p

def main():
 repo=Path.cwd();target=Path(sys.argv[1]);cache=repo/'.lake/complete-table-checkpoint';cache.mkdir(parents=True,exist_ok=True)
 run=json.loads(subprocess.check_output(['gh','api',f'repos/tarikskalic33/formal-conjectures/actions/runs/{RUN}'],text=True))
 assert run['head_sha']==SHA and run['conclusion']=='success' and run['status']=='completed','FULL_TABLE_RUN_NOT_SUCCESSFUL'
 subprocess.run(['git','fetch','--no-tags','--depth=1','origin',SHA],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 metadata={PREFIX+n for n in ['AEGIS_RH_EXACT_HEAD_PROOF_GRAPH.json','AEGIS_RH_KERNEL_RECEIPT.json','AEGIS_RH_LEAN_PATCH.diff','AEGIS_RH_MATHEMATICAL_ALIGNMENT.md','AEGIS_RH_Q16_CERTIFICATE.md','AEGIS_RH_ZERO_COORDINATE_AUDIT.md','AEGIS_RH_FINAL_DECISION.md','NEXT_STEPS.md','full_table_execution/FULL_TABLE_KERNEL_RECEIPT.json','full_table_execution/FULL_TABLE_PROOF_GRAPH.json']}
 metadata.add('.github/workflows/rh-cvs-actual-row-replay.yml')
 changes=subprocess.check_output(['git','diff','--no-renames','--name-status',SHA,'--'],text=True).splitlines()
 for line in changes:
  status,name=line.split('\t',1)
  assert name in metadata or (status=='A' and name.startswith(PREFIX)), 'OTHER_PROOF_INPUT_CHANGED '+name
 if '--validate-existing' not in sys.argv:
  subprocess.run(['gh','run','download',str(RUN),'--repo','tarikskalic33/formal-conjectures','--name','source-cross-row-'+SHA,'--dir',str(cache)],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
 m=json.loads((cache/'SOURCE_CROSS_ROW_CHECKPOINT.json').read_text());r=json.loads((cache/'FULL_TABLE_CI_RECEIPT.json').read_text())
 assert m['source_commit']==SHA and r['commit']==SHA and r['status']=='PASS'
 assert m['math_step_outcome']=='success'
 assert 'version 4.33.1' in r['lean'] and '819816b2e0' in r['lean'], 'WRONG_COMPILED_LEAN'
 assert m['lean_toolchain']=='leanprover/lean4:v4.33.1' and m['mathlib_sha']==r['mathlib']==MATHLIB
 assert m['li_criterion_sha']=='35df682f3b709ffe5fbcfdd452dfa964bd622b87'
 assert (repo/'lean-toolchain').read_text().strip()==m['lean_toolchain']
 assert subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()==MATHLIB
 for name,sha in m['source_sha256'].items():assert digest(safe(repo,name))==sha,'OLD_SOURCE_CHANGED '+name
 for name,sha in m['log_sha256'].items():assert digest(safe(cache,name))==sha,'OLD_LOG_CHANGED '+name
 # Match the archived mathematical sources and the unchanged exact source input.
 fm=json.loads(subprocess.check_output(['git','show',SHA+':'+PREFIX+'full_table_execution/SOURCE_MANIFEST.json'],text=True))
 archive=repo/PREFIX/'full_table_execution/FULL_TABLE_SOURCES.zip';assert digest(archive)==fm['archive_sha256'],'FULL_SOURCE_ARCHIVE_CHANGED'
 with zipfile.ZipFile(archive) as z:
  arch={Path(n).stem:hashlib.sha256(z.read(n)).hexdigest() for n in z.namelist() if n.endswith('.lean')}
  assert hashlib.sha256(z.read('EXACT_FULL_INPUTS.json')).hexdigest()=='69014b7fbf4246f20f6bc0a8ee1245b4d401315899511308b8c226b0606ec63c'
 extras={'CvSPackedIntervalDotV1':repo/PREFIX/'packed_execution/CvSPackedIntervalDotV1.lean','CvSRowBudgetAlgebraV1':repo/'research/rh/checkpoints/20261020_row_budget/CvSRowBudgetAlgebraV1.lean'}
 expected=['CvSPackedIntervalDotV1','CvSCachedColumnV1','CvSCachedEnvelopeJoinV1']+[f'CvSCachedGramRows{i}' for i in range(15)]+['CvSCachedGramV1']+[f'CvSCachedInput{i}' for i in range(139)]+['CvSCachedInputsV1','CvSFullCachedTableV1']+[f'CvSCachedProduct{i}' for i in range(139)]+[f'CvSCachedOutput{i}' for i in range(139)]+['CvSRowBudgetAlgebraV1','CvSRowBudgetGramBridgeV1','CvSRealTailMatrixV1','CvSStrictRowBudgetV1','CvSFullTableClosureV1','CvSFullBudgetJoinV1','CvSFullTableRejectV1']
 assert len(r['runs'])==len(expected)==445 and [a['module'] for a in r['runs']]==expected
 audits={}
 for a in r['runs']:
  assert a['exit_code']==0 and a['source_sha256']==(digest(extras[a['module']]) if a['module'] in extras else arch[a['module']]),'FULL_TABLE_SOURCE_MISMATCH '+a['module']
  text=a['compiler_output'];assert not re.search(r'error:|error\(lean|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler',text),'BAD_COMPILER_LOG'
  for name,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
   axes=[x.strip() for x in ax.split(',') if x.strip()];assert set(axes)<=ALLOW,(name,axes);audits[name]=axes
  for name in re.findall(r"'([^']+)' does not depend on any axioms",text):audits[name]=[]
 for name in ['AEGIS.CvSFullTableClosureV1.full_table_contains','AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs','AEGIS.CvSFullTableRejectV1.reject_modified_cache']:assert name in audits,'MISSING_TERMINAL_AUDIT'
 assert len(audits)>=860,'INCOMPLETE_FULL_TABLE_AUDITS'
 binaries=m['binary_sha256'];assert len(binaries)>=600
 for name,sha in binaries.items():
  assert name.startswith('.lake/ringout/') and name.endswith('.olean')
  assert digest(safe(cache,name))==sha,'COMPILED_BINARY_CHANGED '+name
  dst=target/Path(name).relative_to('.lake/ringout')
  if dst.exists():assert digest(dst)==sha,'EXISTING_BINARY_CONFLICT '+name
 # A new tracked module may not shadow any old cached module name.
 old_stems={Path(n).stem for n in binaries};tracked=subprocess.check_output(['git','ls-files','--','*.lean'],text=True).splitlines()
 for n in set(tracked)-set(m['source_sha256']):assert Path(n).stem not in old_stems,'NEW_MODULE_SHADOWS_CACHE '+n
 target.mkdir(parents=True,exist_ok=True)
 for name in binaries:
  dst=target/Path(name).relative_to('.lake/ringout');dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copyfile(safe(cache,name),dst)
 lean='import CvSFullBudgetJoinV1\nimport CvSFullTableRejectV1\n'
 for name in ['AEGIS.CvSFullTableClosureV1.full_table_contains','AEGIS.CvSFullTableClosureV1.real_envelope_mem','AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs']:
  lean+='#check @'+name+'\n#print axioms '+name+'\n'
 (repo/'COMPLETE_TABLE_CHECKPOINT_REAUDIT.lean').write_text(lean)
 receipt={'status':'EXACT_SUCCESSFUL_FULL_TABLE_DEPENDENCIES_REUSED','source_run':RUN,'source_commit':SHA,'verified_binary_count':len(binaries),'validated_full_table_modules':445,'validated_axiom_audits':audits,'manifest_sha256':digest(cache/'SOURCE_CROSS_ROW_CHECKPOINT.json'),'full_table_receipt_sha256':digest(cache/'FULL_TABLE_CI_RECEIPT.json'),'scope':'Reused original-import source compilation after exact source, archive, pin, compiler, axiom and binary validation. New actual-input sources require fresh compilation.'}
 (repo/'COMPLETE_TABLE_REUSE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('SOURCE_IDENTICAL_COMPLETE_TABLE_REUSE',SHA,len(binaries),'binaries',len(audits),'axiom roots')
if __name__=='__main__':
 try:main()
 except Exception as e:print('COMPLETE_TABLE_CHECKPOINT_REJECTED',type(e).__name__,str(e));raise SystemExit(1)
