from pathlib import Path
import subprocess,os,json,time,hashlib,re,sys,datetime
r=Path('/workspace/formal-conjectures');w=Path('/workspace/aegis-row-budget-bridge')
env=os.environ.copy();env['LEAN_PATH']=str(w)+':/workspace/aegis-research-execution/integration:'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,text=True).strip()
sha=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();pin=subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],cwd=r,text=True).strip();assert pin=='0df444a360eaa60ab8c11dca51a86af692955474'
for mod,names in [('CvSIntervalDivideV1',['divPos_mem','divInt_mem']),('CvSFrequencyIntervalV1',['pi_bounds','frequency_bounds','coefficient_mem','lp_mem','lp_squared_mem'])]:
 src=w/(mod+'.lean');cmd=['lake','env','lean','-DwarningAsError=true','-R',str(w),'-o',str(w/(mod+'.olean')),str(src)];t=time.monotonic();p=subprocess.run(cmd,cwd=r,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);sec=time.monotonic()-t;(w/(mod+'.log')).write_text(p.stdout)
 roots=[]
 for name in names:
  ident='AEGIS.'+mod+'.'+name;h=re.search("'"+re.escape(ident)+r"' depends on axioms:\s*\[([^]]*)\]",p.stdout,re.S);h0=re.search("'"+re.escape(ident)+"' does not depend on any axioms",p.stdout);ax=[x.strip() for x in h.group(1).split(',') if x.strip()] if h else [];okay=(h is not None or h0 is not None) and set(ax)<={'propext','Classical.choice','Quot.sound'};roots.append({'name':ident,'axioms':ax,'audit_pass':okay})
 okay=p.returncode==0 and all(n['audit_pass'] for n in roots)
 rec={'status':'PASS' if okay else 'FAIL','source_base_commit':sha,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'cwd':str(r),'seconds':sec,'returncode':p.returncode,'compiler_output':p.stdout,'roots':roots,'mathlib_sha':pin,'lean_version':subprocess.check_output(['lake','env','lean','--version'],cwd=r,text=True).strip(),'native_import_scope':'Existing RHFixInterval mathematical body unchanged, import Mathlib narrowed as archived earlier. Full actual-source imports require separate CI.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(w/(mod+'.RECEIPT.json')).write_text(json.dumps(rec,indent=2)+'\n');print(mod,rec['status'],sec,flush=True)
 if not okay:print(p.stdout,flush=True);sys.exit(1)
