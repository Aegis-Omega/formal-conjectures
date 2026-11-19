"""Check source/input/receipt binding and conservative trial upper bounds.

This audit verifies recorded evidence consistency; it does not replay Arb.
"""
from pathlib import Path
import hashlib
import json
from flint import arb, fmpq, ctx

root=Path(__file__).parent
ctx.prec=800
checker_sha=hashlib.sha256((root/'check_exact_witness.py').read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise ValueError(message)
def fraction(pair):return fmpq(int(pair[0]),int(pair[1]))
def ball(q):return arb(q.p)/q.q
sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'certify.py',root/'qwhp.py')}
rows=[]
for n,d,limit in ((3,4,fmpq(77,10**11)),(1,1,fmpq(2,10**18)),
                  (5,4,fmpq(5,10**23)),(3,2,fmpq(43,10**27))):
    folder=root/f'replay_a{n}_{d}_K40'
    witness_path=folder/'EXACT_WITNESS.json'
    data=json.loads(witness_path.read_text())
    original=json.loads((folder/'ORIGINAL_REPLAY_RECEIPT.json').read_text())
    direct=json.loads((folder/'DIRECT_WITNESS_RECEIPT_FINAL.json').read_text())
    require(direct['input_sha256']==hashlib.sha256(witness_path.read_bytes()).hexdigest(),'input digest mismatch')
    require(direct['checker_sha256']==checker_sha,'checker source mismatch')
    require(direct['arb_precision']==800 and direct['integration']['panels']==16,'precision or partition mismatch')
    require(fraction(data['a'])==fmpq(n,d),'witness support mismatch')
    require(fraction(data['exact_norm_squared'])==fraction(direct['exact_norm_squared']),'norm binding mismatch')
    for identity in original['source_identities']:
        require(sources[identity['file']]==identity['sha256'],'original source mismatch')
    actual=arb(direct['quotient_ball']); prior=arb(original['quotient_ball'])
    require(actual.is_finite() and actual.overlaps(prior),'independent formulas disagree')
    upper=fraction(direct['rigorous_rational_upper'])
    dyadic=fraction(direct['exact_dyadic_upper'])
    require(actual<ball(upper) and dyadic<upper<limit,'directed/conservative upper bound fails')
    require(actual>0,'this positive trial unexpectedly has nonpositive enclosure')
    printed_below=bool(arb(original['original_formatted_upper'])<actual)
    require(printed_below==original['formatted_upper_below_trial_ball'],'formatting diagnostic mismatch')
    rows.append(dict(a=[str(n),str(d)],witness_sha256=direct['input_sha256'],
                     direct_receipt_sha256=hashlib.sha256((folder/'DIRECT_WITNESS_RECEIPT_FINAL.json').read_bytes()).hexdigest(),
                     conservative_upper=[str(limit.p),str(limit.q)],
                     exact_directed_upper=direct['rigorous_rational_upper'],
                     quotient_ball=direct['quotient_ball'],
                     implementations_overlap=True,original_decimal_below_selected_trial=printed_below))
negative=json.loads((root/'adversarial_input_checks/NEGATIVE_REPLAY_RECEIPT.json').read_text())
require(negative['checker_sha256']==checker_sha and negative['passed']==14,'negative replay binding mismatch')
report=dict(schema='AEGIS_CLAUDE_HANDOFF_REPLAY_AUDIT_V1',checker_sha256=checker_sha,
            exact_trial_upper_bounds=rows,negative_input_cases_passed=14,
            implementation_diversity=True,independent_formal_kernel=False,
            certificate_library='python-flint 0.9.0 / Arb',
            analytic_soundness='ordinary manuscript DIRECT_WITNESS_SOUNDNESS.md',
            proof_scope='upper bounds only; no lower bound for the global infimum',
            lean_analytic_replay=False,final_RH_theorem=None,rh_proven=False)
out=root/'HANDOFF_REPLAY_AUDIT.json'
require(not out.exists(),'refusing to overwrite audit')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
