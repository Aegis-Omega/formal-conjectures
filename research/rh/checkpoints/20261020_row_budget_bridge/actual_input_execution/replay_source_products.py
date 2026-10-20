"""Sequential pinned Lean execution with per-source hashes and axiom receipts."""
from pathlib import Path
import subprocess,os,time,json,hashlib,sys,resource,re
w=Path(__file__).resolve().parent;root=Path('/workspace/formal-conjectures')
env=os.environ.copy();base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip();env['LEAN_PATH']=f'{w}:/workspace/aegis-full-table-bridge:/workspace/aegis-row-budget-bridge:/workspace/aegis-research-execution/integration:'+base
names=sys.argv[1:];receipt_path=w/('FULL_TABLE_'+os.environ.get('AEGIS_RECEIPT_SCOPE','MAIN')+'_KERNEL_RECEIPT.json')
receipt=json.loads(receipt_path.read_text()) if receipt_path.exists() else {'lean':subprocess.check_output(['lake','env','lean','--version'],cwd=root,text=True).strip(),'base_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'mathlib':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'.lake/packages/mathlib',text=True).strip(),'runs':[]}
for name in names:
 p=w/(name+'.lean');log=w/(name+'.log');t=time.monotonic()
 cmd=['lake','env','lean','-DwarningAsError=true','-R',str(w),'-o',str(w/(name+'.olean')),str(p)]
 with log.open('w') as f:r=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 data=log.read_text();audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",data)
 bad=[(n,a) for n,a in audits if set(x.strip() for x in a.split(',') if x.strip()) - {'propext','Classical.choice','Quot.sound',''}]
 row={'module':name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'command':cmd,'seconds':time.monotonic()-t,'exit_code':r.returncode,'status':'PASS' if r.returncode==0 and not bad else 'FAIL','log':log.name,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'audits':[{'theorem':n,'axioms':[x.strip() for x in a.split(',') if x.strip()] if a else []} for n,a in audits],'bad_axioms':bad,'max_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
 (w/(name+'.RECEIPT.json')).write_text(json.dumps(row,indent=2)+'\n');receipt['runs'].append(row);receipt_path.write_text(json.dumps(receipt,indent=2)+'\n');print(name,row['status'],round(row['seconds'],3),'s',flush=True)
 if row['status']!='PASS':print(data[-6000:],flush=True);sys.exit(1)
