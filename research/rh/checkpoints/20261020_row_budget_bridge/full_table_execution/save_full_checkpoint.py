"""Preserve exact candidates, compiler evidence and the latest verified scope."""
from pathlib import Path
import json,zipfile,hashlib,shutil,datetime,re
w=Path(__file__).resolve().parent;repo=Path('/workspace/formal-conjectures');d=repo/'research/rh/checkpoints/20261020_row_budget_bridge/full_table_execution';d.mkdir(exist_ok=True)
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Prefer source- and log-matching successful receipts; retain scope distinctions.
records={}
for p in sorted(w.glob('*KERNEL_RECEIPT.json'))+sorted(w.glob('*.RECEIPT.json')):
 try:a=json.loads(p.read_text())
 except (ValueError,OSError):continue
 for r in a.get('runs',[a] if 'module' in a else []):
  src=w/(r['module']+'.lean');log=w/r.get('log','')
  if src.is_file() and log.is_file() and r.get('status')=='PASS' and r.get('source_sha256')==digest(src) and r.get('log_sha256')==digest(log):records[r['module']]=r
for n in ['CvSCachedColumnV1','CvSCachedEnvelopeJoinV1','CvSFullTableClosureV1','CvSFullBudgetJoinV1','CvSStrictRowBudgetV1','CvSRealTailMatrixV1','CvSFullTableRejectV1']:
 shutil.copyfile(w/(n+'.lean'),d/(n+'.lean'))
for p in w.glob('*.py'):shutil.copyfile(p,d/p.name)
shutil.copyfile(w/'FULL_TABLE_GENERATION.json',d/'FULL_TABLE_GENERATION.json')
with zipfile.ZipFile(d/'FULL_TABLE_SOURCES.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(w.glob('*.lean')):z.write(p,p.name)
 z.write(w/'EXACT_FULL_INPUTS.json','EXACT_FULL_INPUTS.json')
manifest={'base_head':'b133be9d88ca0a58ad5ea90aeee3fc5c765be445','status':'SOURCE_SNAPSHOT_WITH_PER_MODULE_KERNEL_STATUS','archive_sha256':digest(d/'FULL_TABLE_SOURCES.zip'),'sources':[{'path':p.name,'sha256':digest(p),'bytes':p.stat().st_size,'kernel_status':records.get(p.stem,{}).get('status','NOT_RECORDED_IN_MATCHING_RECEIPT')} for p in sorted(w.glob('*.lean'))]}
(d/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(d/'FULL_TABLE_COMPILER_LOGS.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for name,r in sorted(records.items()):z.write(w/r['log'],r['log'])
 for n in ['input-replay-progress.log','product-replay-progress.log','output-replay-progress.log','output-a-progress.log','output-b-progress.log']:
  if (w/n).exists():z.write(w/n,n)
receipt={'decision':'STRONGEST_VERIFIED_RESULT_WITH_EXACT_REMAINING_OBLIGATION','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_base_commit':manifest['base_head'],'lean':'4.33.1','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474','native_import_scope':'The prior exact mathematical bodies of RHFixIntervalV1 and CvSPackedGramV1 have their documented narrowed Mathlib imports. Original-source CI is recorded separately and is not presumed to cover new modules.','source_archive_sha256':manifest['archive_sha256'],'runs':[records[n] for n in sorted(records)],'verified_cached_inputs':sum(f'CvSCachedInput{i}' in records for i in range(139)),'verified_product_columns':sum(f'CvSCachedProduct{i}' in records for i in range(139)),'verified_output_columns':sum(f'CvSCachedOutput{i}' in records for i in range(139)),'canonical_RH':'NOT_PROVED','analytic_input_memberships':'Not discharged by the finite table. Existing actual source lemmas and exact literal identities must be composed.'}
(d/'FULL_TABLE_KERNEL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
# Preserve the next analytic-binding reconstruction without attributing any Lean status to it.
if (w/'EXACT_SOURCE_BRIDGE_INPUTS.json').is_file():
 with zipfile.ZipFile(d/'SOURCE_BINDING_NEXT_INPUTS.zip','w',compression=zipfile.ZIP_DEFLATED) as z:z.write(w/'EXACT_SOURCE_BRIDGE_INPUTS.json','EXACT_SOURCE_BRIDGE_INPUTS.json')
 (d/'SOURCE_BINDING_NEXT_INPUTS.json').write_text(json.dumps({'sha256':digest(w/'EXACT_SOURCE_BRIDGE_INPUTS.json'),'status':'EXACT_INTEGER_RECONSTRUCTION; NOT_A_LEAN_SOURCE_MEMBERSHIP_PROOF','data':['original E kernel interval rows','original Y finite products','unchanged Q48 projection at Q96','original X*Lambda interval products'],'source_archive_sha256':digest(d/'SOURCE_BINDING_NEXT_INPUTS.zip')},indent=2)+'\n')
print('Saved scope:',receipt['verified_cached_inputs'],'inputs,',receipt['verified_product_columns'],'product columns,',receipt['verified_output_columns'],'output columns; archive', (d/'FULL_TABLE_SOURCES.zip').stat().st_size,flush=True)
