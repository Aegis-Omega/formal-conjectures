from pathlib import Path
import json,hashlib,zipfile,subprocess
repo=Path.cwd();p=repo/'research/rh/checkpoints/20261020_row_budget_bridge';a=p/'actual_input_execution'
def digest_stream(f):
 h=hashlib.sha256()
 while b:=f.read(1048576):h.update(b)
 return h.hexdigest()
def dh(p):
 with p.open('rb') as f:return digest_stream(f)
assert dh(Path('/workspace/aegis-source-bound-graph.zip'))=='daf948d4b68d23f89a376f7e24c576ebf8305d30d4efac6b690d58688509c059'
recovery=json.loads((a/'GRAPH_RECOVERY_RECEIPT.json').read_text());assert recovery['source_run']==39571212916 and recovery['status']=='EXACT_REPACKAGING_ONLY'
for n,h in recovery['files'].items():assert dh(a/n)==h,'RECOVERY_FILE_CHANGED '+n
r=json.loads((a/'ACTUAL_INPUT_CI_RECEIPT.json').read_text());m=json.loads((a/'SOURCE_CROSS_ROW_CHECKPOINT.json').read_text());g=json.loads((a/'ACTUAL_SOURCE_PROOF_GRAPH.json').read_text())
sha='9d98c4e99e3ab3d271215192f100964a5fdaac0c';assert g['source_commit']==r['commit']==m['source_commit']==sha
assert r['status']==g['status']=='PASS' and m['actual_input_step_outcome']=='success'
assert r['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and '819816b2e0' in r['lean'] and '4.33.1' in r['lean']
assert len(r['runs'])==433 and r['fresh_module_count']==0 and r['reused_module_count']==433
with zipfile.ZipFile('/workspace/aegis-actual-window-kernel-pass.zip') as z:
 previous=json.loads(z.read('SOURCE_CROSS_ROW_CHECKPOINT.json'));assert m['binary_sha256']==previous['binary_sha256']
 for n,h in previous['binary_sha256'].items():
  with z.open(n) as f:assert digest_stream(f)==h,'SOURCE_BINARY_CHANGED '+n
changed=set(subprocess.check_output(['git','diff','--name-only',sha,'--','*.lean'],text=True).splitlines())
for n,h in m['source_sha256'].items():
 data=subprocess.check_output(['git','show',sha+':'+n]) if n in changed else (repo/n).read_bytes()
 assert hashlib.sha256(data).hexdigest()==h,'TRACKED_SOURCE_CHANGED '+n
with zipfile.ZipFile(a/'ACTUAL_INPUT_SOURCES.zip') as z:
 assert dh(a/'ACTUAL_INPUT_SOURCES.zip')==r['source_archive_sha256']
 for x in r['runs']:
  assert x['status']=='PASS' and x['exit_code']==0
  assert hashlib.sha256(z.read(x['module']+'.lean')).hexdigest()==x['source_sha256']
  assert x['dependency_reuse']['source_commit']=='f118d06204bc50fe719810794af5bac4dfd14889'
  assert not any(w in x['compiler_output'] for w in ['sorryAx','Lean.ofReduceBool','Lean.trustCompiler','error:'])
assert len(r['axiom_audits'])==2055 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in r['axiom_audits'].values())
assert g['missing_dependencies']==g['proof_cycles']==0 and len(g['roots'])==14
assert sum(len(x['declarations']) for x in g['groups'])==g['declaration_count']==82601
sources={x['module']:x for x in g['source_manifest']}
assert sources['RHFixIntervalV1']['path']=='research/rh/critical_line_v1/RHFixIntervalV1.lean'
assert sources['RHFixIntervalV1']['sha256']==dh(repo/sources['RHFixIntervalV1']['path'])
recipe=json.loads((repo/'research/rh/feshbach_lean_v1/tools/krein_ring_closure.json').read_text())
for x in recipe['modules']:
 if x['module'] in sources:assert sources[x['module']]['blob_sha']==x['blob']
for x in sources.values():
 if x['path'].startswith('.lake/packages/mathlib/'):assert dh(repo/x['path'])==x['sha256'],'MATHLIB_USED_SOURCE_CHANGED '+x['module']
with zipfile.ZipFile(a/'ACTUAL_SOURCE_PROOF_GRAPH.zip') as z:
 with z.open('ACTUAL_SOURCE_PROOF_GRAPH_RAW.json') as f:assert digest_stream(f)==g['raw_graph_sha256']
receipt={'status':'PASS','source_commit':sha,'run':39571212916,'artifact_id':12332549155,'artifact_sha256':recovery['original_artifact_sha256'],'graph_recovery_run':39578861869,'downloaded_graph_artifact_id':12335312281,'downloaded_graph_artifact_sha256':'daf948d4b68d23f89a376f7e24c576ebf8305d30d4efac6b690d58688509c059','validated_binary_count':len(m['binary_sha256']),'binary_validation_method':'All1044 exact binary bytes rehashed from the independently downloaded f118 ZIP; their entire map is identical to the successful9d98 source snapshot. The recovery runner separately checked the original583535823-byte ZIP SHA before extracting unchanged graph/receipts.','validated_actual_module_count':433,'fresh_actual_modules':[],'reused_actual_modules':433,'axiom_audit_count':2055,'proof_graph_status':'PASS','proof_graph_roots':14,'proof_graph_declarations':82601,'source_manifest_modules':len(sources),'proof_graph_zip_sha256':dh(a/'ACTUAL_SOURCE_PROOF_GRAPH.zip'),'scope':'Actual CvS finite source budget, original-vector hfin/hB and conditional fixed-window zero-side theorem. No unconditional RH or analytic Krein/trace witness claimed.'}
(a/'ACTUAL_TERMINAL_ARTIFACT_VALIDATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
