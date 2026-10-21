"""Preserve staged actual-input integration with explicit per-module proof status."""
from pathlib import Path
import json,hashlib,zipfile,shutil,datetime
w=Path(__file__).resolve().parent;repo=Path('/workspace/formal-conjectures');d=repo/'research/rh/checkpoints/20261020_row_budget_bridge/actual_input_execution';d.mkdir(exist_ok=True)
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for p in sorted(w.glob('*.RECEIPT.json')):
 r=json.loads(p.read_text());src=w/(r['module']+'.lean');log=w/r['log']
 if r['status']=='PASS' and r['source_sha256']==digest(src) and r['log_sha256']==digest(log):records.append(r)
passed={r['module'] for r in records}
for p in w.glob('*.py'):shutil.copyfile(p,d/p.name)
for n in ['CvSCachedSourceProductV1','CvSCachedPointV1','CvSCachedSliceV1','CvSSourceQNormalizeV1','CvSSourceProductAllV1','CvSSourceQAllV1','CvSSourceQRejectV1','CvSActualLiteralInputsV1','CvSActualBasisBudgetV1','CvSRealTailFormV1','CvSActualRowConsumerV1','CvSActualGramWindowV1','CvSKreinScalarUniformV1']:shutil.copyfile(w/(n+'.lean'),d/(n+'.lean'))
with zipfile.ZipFile(d/'ACTUAL_INPUT_SOURCES.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(w.glob('*.lean')):z.write(p,p.name)
 z.write(w/'EXACT_SOURCE_BRIDGE_INPUTS.json','EXACT_SOURCE_BRIDGE_INPUTS.json')
with zipfile.ZipFile(d/'ACTUAL_INPUT_LOGS.zip','w',zipfile.ZIP_DEFLATED) as z:
 for r in records:z.write(w/r['log'],r['log'])
manifest={'base_mathematical_source_commit':'2d2ea90dd2db6d57a8d5cf4bbf7ac734566d3925','archive_sha256':digest(d/'ACTUAL_INPUT_SOURCES.zip'),'classification':'New exact-integer reconstruction and staged source-product continuation; generated roots are candidates until kernel receipts say PASS. Not recovered Claude artifacts.','sources':[{'name':p.name,'sha256':digest(p),'kernel_status':'PASS' if p.stem in passed else 'NOT_RUN'} for p in sorted(w.glob('*.lean'))]}
manifest['unchanged_existing_source_copies'] = {n+'.lean': {'original_path': 'research/rh/feshbach_lean_v1/'+n+'.lean', 'sha256': digest(w/(n+'.lean'))} for n in ['CvSTriangularTransportV1','CvSRealBasisBoundV1','CvSProjectedBasisL12V1','CvSTauFarL12V1']}
(d/'ACTUAL_INPUT_SOURCE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean':'4.33.1','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474','status':'PARTIAL_NATIVE_REPLAY','archive_sha256':manifest['archive_sha256'],'runs':records,'actual_analytic_input_membership_producer':'NOT_YET_KERNEL_VERIFIED','canonical_RH':'NOT_PROVED','scope':'Cached E rows, transposed X rows, point Lambda columns and staged Y=E*X / inner=X*Lambda / Z=Y-inner equality checks. Only explicit successful runs are certified.'}
(d/'ACTUAL_INPUT_KERNEL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('ACTUAL_INPUT_CHECKPOINT',len(passed),'PASS of',len(manifest['sources']),'generated source modules; archive bytes',(d/'ACTUAL_INPUT_SOURCES.zip').stat().st_size,flush=True)
