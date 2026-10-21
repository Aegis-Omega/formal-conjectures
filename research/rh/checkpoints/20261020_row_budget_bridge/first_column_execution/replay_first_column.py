from pathlib import Path
import subprocess,os,time,json,hashlib,resource
w=Path('/workspace/aegis-row-budget-bridge');r=Path('/workspace/formal-conjectures')
env=os.environ.copy();env['LEAN_PATH']=str(w)+':/workspace/aegis-research-execution/integration:'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,text=True).strip()
rows=[]
for i in range(14):
    name=f'RowBudgetFirstColumnBatch{i}';p=w/(name+'.lean')
    cmd=['lake','env','lean','-DwarningAsError=true','-R',str(w),'-o',str(w/(name+'.olean')),str(p)]
    t=time.monotonic();res=subprocess.run(cmd,cwd=r,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (w/(name+'.log')).write_text(res.stdout)
    rec={'module':name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'command':cmd,'returncode':res.returncode,'status':'PASS' if res.returncode==0 and 'sorryAx' not in res.stdout else 'FAIL','seconds':time.monotonic()-t,'compiler_output':res.stdout}
    rows.append(rec)
    (w/'FIRST_COLUMN_KERNEL_RECEIPT.json').write_text(json.dumps({'status':'IN_PROGRESS' if rec['status']=='PASS' else 'FAIL','source_base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'lean':'4.33.1','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474','native_context':'Original mathematical bodies; RHFixIntervalV1 and CvSPackedGramV1 use explicit narrower imports in local work copies. Original CvSRelativeRowCertificateL12V1 source unchanged.','scope':'139 first-column interval-envelope output comparisons and original target identities only; not full matrix/actual hB/RH','batches':rows},indent=2)+'\n')
    print(name,rec['status'],round(rec['seconds'],3),flush=True)
    if rec['status']!='PASS':print(res.stdout,flush=True);raise SystemExit(1)
q=json.loads((w/'FIRST_COLUMN_KERNEL_RECEIPT.json').read_text());q['status']='PASS';q['max_child_rss_kib']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss;(w/'FIRST_COLUMN_KERNEL_RECEIPT.json').write_text(json.dumps(q,indent=2)+'\n')
