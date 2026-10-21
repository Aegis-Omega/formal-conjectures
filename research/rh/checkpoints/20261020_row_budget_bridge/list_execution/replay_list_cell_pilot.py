from pathlib import Path
import subprocess,time,os,json,hashlib,resource
w=Path('/workspace/aegis-row-budget-bridge');r=Path('/workspace/formal-conjectures');env=os.environ.copy();env['LEAN_PATH']=str(w)+':/workspace/aegis-research-execution/integration:'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,text=True).strip()
cmd=['lake','env','lean','-DwarningAsError=true','-R',str(w),'-o',str(w/'RowBudgetListCell0Pilot.olean'),str(w/'RowBudgetListCell0Pilot.lean')];t=time.monotonic()
try:
 p=subprocess.run(cmd,cwd=r,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180);code=p.returncode;s=p.stdout
except subprocess.TimeoutExpired as e:code='TIMEOUT';s=e.stdout or '';s=s.decode() if isinstance(s,bytes) else s
sec=time.monotonic()-t;(w/'list-cell0.log').write_text(s);rec={'status':'PASS' if code==0 else 'FAIL_OR_RESOURCE_NOT_VERIFIED','command':cmd,'seconds':sec,'returncode':code,'max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'source_sha256':hashlib.sha256((w/'RowBudgetListCell0Pilot.lean').read_bytes()).hexdigest(),'source_base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'compiler_output':s,'scope':'One complete recovered output cell and its equality to the original interval-envelope formula. Not full output table, analytic input correspondence, hB or RH.'};(w/'LIST_CELL0_KERNEL_RECEIPT.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2),flush=True)
