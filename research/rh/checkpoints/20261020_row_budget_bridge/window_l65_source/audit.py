"""Axiom audit of every log written by build.py; fail closed. Run from the repo root.

Every `#print axioms` result in every compiled module must use only propext, Classical.choice
and Quot.sound, no log may report a `sorry`, and the named roots below must all be audited.
Writes WINDOW_L65_SOURCE_RECEIPT.json. Not RH.
"""
import hashlib, json, re, subprocess
from pathlib import Path
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
required = ['AEGIS.CvSWindowL65V1.window_L65', 'AEGIS.CvSTraceCertL65V1.trace_premises_L65',
            'AEGIS.CvSActualMomentWindowJoinV1.window_of_actual_rows_moment',
            'AEGIS.CvSActualRowConsumerV1.hfin', 'AEGIS.CvSActualRowConsumerV1.hB',
            'AEGIS.CvSActualGramWindowV1.window_of_actual_rows',
            'AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin',
            'AEGIS.RHWindowL65ExhaustionV1.window_le_three_fifths',
            'AEGIS.RHWindowL65ExhaustionV1.final_sign_iff_windows_above_three_fifths',
            'AEGIS.RHWindowL65ExhaustionV1.rh_iff_windows_above_three_fifths']
plan = json.loads(Path('.lake/real_plan.json').read_text())
state = json.loads(Path('.lake/real_status.json').read_text())
audits, bad, sorries = {}, [], []
for mod in sorted(plan):
    text = (Path('.lake/reallogs')/(mod + '.log')).read_text()
    if re.search(r"declaration uses 'sorry'|sorryAx", text): sorries.append(mod)
    for name, ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        xs = sorted(x.strip() for x in ax.split(',') if x.strip())
        audits.setdefault(name, xs)
        if not set(xs) <= allowed: bad.append((mod, name, xs))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text): audits.setdefault(name, [])
out = lambda *a: subprocess.check_output(a, text=True).strip()
receipt = {
    'commit': out('git', 'rev-parse', 'HEAD'), 'lean': out('lean', '--version'),
    'mathlib': out('git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'),
    'modules': len(plan), 'passed': sum(v == 'PASS' for v in state['status'].values()),
    'compile_seconds_total': round(sum(state['seconds'].values()), 1),
    'source_sha256': {m: hashlib.sha256(Path(r['path']).read_bytes()).hexdigest() for m, r in sorted(plan.items())},
    'axiom_audits': audits, 'unexpected_axioms': bad, 'sorry_modules': sorries,
    'missing_required': [n for n in required if n not in audits],
    'required_roots': {n: audits.get(n) for n in required},
    'scope': 'Every module compiled from source in this run; no binary reuse. window_L65: for '
             'every compactly supported smooth g with the moment conditions and half-width r, '
             '2r <= 6/5, the Weil zero sum of its autocorrelation has nonnegative real part. '
             'One fixed window only. RHWindowL65ExhaustionV1: RH is equivalent to the arithmetic sign on '
             'the log windows L > 3/5; those windows are not proved. Not RH.',
}
ok = (receipt['passed'] == len(plan) and not bad and not sorries and not receipt['missing_required'])
receipt['status'] = 'PASS' if ok else 'FAIL'
Path('WINDOW_L65_SOURCE_RECEIPT.json').write_text(json.dumps(receipt, indent=1) + '\n')
for n in required: print(n, audits.get(n))
print('WINDOW_L65_SOURCE', receipt['status'], len(audits), 'axiom roots', len(plan), 'modules')
raise SystemExit(0 if ok else 1)
