"""Certificate-contract rejection checks in ordinary Python and python -O."""
from pathlib import Path
import copy
import hashlib
import json
import os
import subprocess
import sys

root=Path(__file__).parent
out=root/'adversarial_input_checks'
out.mkdir(exist_ok=False)
checker=root/'check_exact_witness.py'
base=json.loads((root/'replay_a3_4_K40/EXACT_WITNESS.json').read_text())
cases={}
case=copy.deepcopy(base); case['trial']=[['0','1']]; cases['zero_trial']=case
case=copy.deepcopy(base); p,q=map(int,case['trial'][0]); case['trial'][0]=[str(p+q),str(q)]
cases['changed_differential_coefficient']=case
case=copy.deepcopy(base); p,q=map(int,case['exact_norm_squared']); case['exact_norm_squared']=[str(p+q),str(q)]
cases['wrong_norm']=case
case=copy.deepcopy(base); case['operator']='d2/dx2 - 1/4'; cases['wrong_operator']=case
case=copy.deepcopy(base); case['a']=['3','0']; cases['zero_denominator']=case
case=copy.deepcopy(base)
p,q=map(int,case['potential'][0]); case['potential'][0]=[str(p+q),str(q)]
p,q=map(int,case['trial'][0]); case['trial'][0]=[str(4*p+q),str(4*q)]
cases['differentially_consistent_unclamped_potential']=case
inputs={name:json.dumps(data,indent=2) for name,data in cases.items()}
inputs['duplicate_schema']='{"schema":"duplicate",'+json.dumps(base)[1:]
results=[]
for name,raw in inputs.items():
    path=out/(name+'.json'); path.write_text(raw+'\n')
    for optimized in (False,True):
        receipt=out/(name+('_optimized' if optimized else '_ordinary')+'.receipt.json')
        command=[sys.executable]+(['-O'] if optimized else [])+[str(checker),str(path),str(receipt)]
        process=subprocess.run(command,capture_output=True,text=True,timeout=30)
        log=out/(name+('_optimized' if optimized else '_ordinary')+'.log')
        log.write_text(process.stdout+process.stderr)
        if process.returncode==0 or receipt.exists():
            raise RuntimeError('malformed witness accepted: '+name)
        results.append(dict(case=name,optimized=optimized,returncode=process.returncode,
                            receipt_created=False,error=process.stderr.strip().splitlines()[-1]))
report=dict(schema='AEGIS_EXACT_WITNESS_NEGATIVE_REPLAY_V1',
            checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
            tests=results, passed=len(results), rh_proven=False)
(out/'NEGATIVE_REPLAY_RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
