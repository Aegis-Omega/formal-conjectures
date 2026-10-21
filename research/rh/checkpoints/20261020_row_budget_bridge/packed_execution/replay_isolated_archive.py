"""Replay new packed proof closure from the published source archive, on this host.
Mathlib's pinned cache is reused; existing custom-module caches are not reused.
"""
from pathlib import Path
import zipfile,hashlib,json,re,subprocess,os,time,datetime,resource
repo=Path('/workspace/formal-conjectures')
checkpoint=repo/'research/rh/checkpoints/20261020_row_budget_bridge'
work=Path('/workspace/aegis-packed-independent-replay')
work.mkdir(exist_ok=True)
archive=checkpoint/'NATIVE_PACKED_COLUMN_GRAPH.zip'
sources={}
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        if name.startswith('native_sources/') and name.endswith('.lean'):
            target=work/Path(name).name
            data=z.read(name)
            if target.exists():
                assert target.read_bytes()==data, str(target)
            else:
                target.write_bytes(data)
            sources[target.stem]=target
order=[];active=set();visited=set()
def visit(name):
    if name in visited:return
    assert name not in active, 'IMPORT_CYCLE '+name
    active.add(name)
    for imported in re.findall(r'^import (\S+)',sources[name].read_text(),re.M):
        if imported in sources:visit(imported)
        else:assert imported.startswith(('Mathlib.','Lean.')), 'MISSING_CUSTOM_SOURCE '+imported
    active.remove(name);visited.add(name);order.append(name)
visit('RowBudgetPackedZ0Pilot')
env=os.environ.copy()
env['LEAN_PATH']=str(work)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
rows=[]
receipt={'status':'IN_PROGRESS','machine':'Same workspace host; isolated native custom-module directory, not independent human review','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'mathematical_source_snapshot_commit':'08938284963992cd231315e9d9b6c8fe77815ecb','lean':'4.33.1','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474','scope':'New packed interval correctness and unchanged 301-element Z0 pilot, with their complete native custom import closure. Narrowed original-body import context; original-import first-column CI is separate.','modules':rows}
for name in order:
    source=sources[name]
    # Refuse pre-existing compiled custom output rather than silently reusing it.
    assert not (work/(name+'.olean')).exists(), 'OUTPUT_ALREADY_EXISTS '+name
    command=['lake','env','lean','-DwarningAsError=true','-R',str(work),'-o',str(work/(name+'.olean')),str(source)]
    start=time.monotonic()
    result=subprocess.run(command,cwd=repo,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (work/(name+'.log')).write_text(result.stdout)
    status='PASS' if result.returncode==0 and 'sorryAx' not in result.stdout else 'FAIL'
    row={'module':name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'command':command,'returncode':result.returncode,'status':status,'seconds':time.monotonic()-start,'compiler_output':result.stdout}
    rows.append(row)
    receipt['status']='IN_PROGRESS' if status=='PASS' else 'FAIL'
    (work/'ISOLATED_PACKED_REPLAY_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(name,status,round(row['seconds'],3),flush=True)
    if status!='PASS':print(result.stdout,flush=True);raise SystemExit(1)
receipt.update(status='PASS',timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
(work/'ISOLATED_PACKED_REPLAY_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('ISOLATED_NATIVE_PACKED_CLOSURE_PASS',len(rows),'modules',flush=True)
