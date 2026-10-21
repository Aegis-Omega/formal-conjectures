"""Repackage only a previously successful, exact-SHA graph artifact. No proof claims change."""
from pathlib import Path
import subprocess,json,hashlib,zipfile,shutil
repo='tarikskalic33/formal-conjectures';run=39571212916;sha='9d98c4e99e3ab3d271215192f100964a5fdaac0c';artifact=12332549155
expected='405437564d10c5e8ea7df5db96be3efaa261a6ae2486c03de2913e8efe70b693'
meta=json.loads(subprocess.check_output(['gh','api',f'repos/{repo}/actions/runs/{run}'],text=True))
assert meta['head_sha']==sha and meta['status']=='completed' and meta['conclusion']=='success'
p=Path('recovered-source.zip')
with p.open('wb') as f:subprocess.run(['gh','api',f'repos/{repo}/actions/artifacts/{artifact}/zip'],stdout=f,check=True)
h=hashlib.sha256()
with p.open('rb') as f:
 while b:=f.read(1048576):h.update(b)
assert h.hexdigest()==expected,'ORIGINAL_ARTIFACT_DIGEST_MISMATCH'
out=Path('recovered-actual-graph');out.mkdir(exist_ok=True)
names=['ACTUAL_SOURCE_PROOF_GRAPH.json','ACTUAL_SOURCE_PROOF_GRAPH.zip','actual-proof-graph.log','ACTUAL_INPUT_CI_RECEIPT.json','SOURCE_CROSS_ROW_CHECKPOINT.json','ACTUAL_INPUT_PREFIX_AXIOM_RECEIPT.json','ACTUAL_INPUT_PREFIX_REUSE_RECEIPT.json','actual-input-replay.log']
with zipfile.ZipFile(p) as z:
 for n in names:
  with z.open(n) as f,(out/n).open('wb') as w:shutil.copyfileobj(f,w)
g=json.loads((out/'ACTUAL_SOURCE_PROOF_GRAPH.json').read_text())
assert g['status']=='PASS' and g['source_commit']==sha and g['missing_dependencies']==g['proof_cycles']==0
r={'status':'EXACT_REPACKAGING_ONLY','source_run':run,'source_commit':sha,'original_artifact_id':artifact,'original_artifact_sha256':expected,'files':{n:hashlib.sha256((out/n).read_bytes()).hexdigest() for n in names},'scope':'Unchanged original graph and source/kernel receipts. No new Lean execution is claimed.'}
(out/'GRAPH_RECOVERY_RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
print('SOURCE_BOUND_GRAPH_RECOVERED',g['declaration_count'],'declarations; exact bytes and original successful run validated')
