"""Axiom audit of every log written by build.py; fail closed. Run from the repo root.

Every `#print axioms` result in every compiled module must use only propext, Classical.choice
and Quot.sound, no log may report a `sorry`, and the named roots below must all be audited.
Writes WINDOW_L65_SOURCE_RECEIPT.json. Not RH.
"""
import hashlib, json, os, re, subprocess
from pathlib import Path
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
required = ['AEGIS.CvSWindowL65V1.window_L65', 'AEGIS.CvSTraceCertL65V1.trace_premises_L65',
            'AEGIS.CvSActualMomentWindowJoinV1.window_of_actual_rows_moment',
            'AEGIS.CvSActualRowConsumerV1.hfin', 'AEGIS.CvSActualRowConsumerV1.hB',
            'AEGIS.CvSActualGramWindowV1.window_of_actual_rows',
            'AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin',
            'AEGIS.RHWindowL65ExhaustionV1.window_le_three_fifths',
            'AEGIS.RHWindowL65ExhaustionV1.final_sign_iff_windows_above_three_fifths',
            'AEGIS.RHWindowL65ExhaustionV1.rh_iff_windows_above_three_fifths',
            'AEGIS.CvSWindowL43V1.window_L43', 'AEGIS.CvSTraceCertL43V1.trace_premises_L43',
            'AEGIS.CvSRelRowHBL43V1.hB', 'AEGIS.CvSRelRowHBL43V1.K_ok',
            'AEGIS.CvSRelRowFormL43V1.midpoint_ge', 'AEGIS.CvSRelRowCheckL43V1.certL_ok',
            'AEGIS.RHWindowL43ExhaustionV1.window_le_two_thirds',
            'AEGIS.RHWindowL43ExhaustionV1.final_sign_iff_windows_above_two_thirds',
            'AEGIS.RHWindowL43ExhaustionV1.rh_iff_windows_above_two_thirds',
            'AEGIS.CvSWindowL118V1.window_L118', 'AEGIS.CvSTraceCertL118V1.trace_premises_L118',
            'AEGIS.CvSRelRowHBL118V1.hB', 'AEGIS.CvSRelRowHBL118V1.K_ok',
            'AEGIS.CvSRelRowFormL118V1.midpoint_ge', 'AEGIS.CvSRelRowCheckL118V1.certL_ok',
            'AEGIS.CvSTauR1PrimeL118V1.tau_mem_R1', 'AEGIS.CvSTauFarL118V1.tau_abs_le_far',
            'AEGIS.CvSDiagL118V1.diag_mem',
            'AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths',
            'AEGIS.RHWindowL118ExhaustionV1.final_sign_iff_windows_above_eleven_sixteenths',
            'AEGIS.RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths',
            'AegisMath.Windows.window_le_eleven_sixteenths',
            'AegisMath.Windows.final_sign_iff_windows_above_eleven_sixteenths',
            'AegisMath.Windows.rh_iff_windows_above_eleven_sixteenths',
            'AegisMath.Criterion.final_sign_iff_rh', 'AegisMath.Criterion.no_zero_re_gt_half_of_final_sign',
            'AegisMath.MomentKiller.exists_momentKiller_packet', 'AegisMath.MomentKiller.exists_momentKiller_eq',
            'AegisMath.Obstructions.no_common_positive_width',
            'AegisMath.Obstructions.vonMangoldt_weights_do_not_imply_operator_nonnegative',
    'AEGIS.RHWindowL118ActualFineGramJoinV1.actual_signed_fine_gram_on_l118_window',
    'AEGIS.RHWindowL118ActualFineGramJoinV1.rh_iff_remaining_windows_actual_sharp_signed_budget',
    'AEGIS.RHWindowL118ActualFineGramJoinV1.every_actual_finite_gram_sharp_signed_budget_on_l118_window',
    'AEGIS.RHWindowL118ActualFineGramJoinV1.actual_krein_two_block_signed_budget_on_l118_window',
    'AEGIS.RHWindowL118ActualFineGramJoinV1.actual_fine_log_free_pairs_and_complete_signed_budget_on_l118_window']
plan = json.loads(Path('.lake/real_plan.json').read_text())
state = json.loads(Path('.lake/real_status.json').read_text())
audits, bad, sorries, missing_logs = {}, [], [], []
for mod in sorted(plan):
    log_path = Path('.lake/reallogs') / (mod + '.log')
    if not log_path.is_file():
        missing_logs.append(mod)
        continue  # FAIL CLOSED while still auditing available logs
    text = log_path.read_text()
    if re.search(r"declaration uses 'sorry'|sorryAx", text): sorries.append(mod)
    for name, ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        xs = sorted(x.strip() for x in ax.split(',') if x.strip())
        audits.setdefault(name, xs)
        if not set(xs) <= allowed: bad.append((mod, name, xs))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text): audits.setdefault(name, [])
out = lambda *a: subprocess.check_output(a, text=True).strip()
# Hosted workflow checks out the PR *source* head, not the synthetic merge SHA.
# A green axiom audit from any other commit must not be accepted for this run.
checkout_sha = out('git', 'rev-parse', 'HEAD')
event_file = os.environ.get('GITHUB_EVENT_PATH')
expected_head = None
provenance_error = None
if os.environ.get('GITHUB_ACTIONS') == 'true':
    if not event_file or not Path(event_file).is_file():
        provenance_error = 'MISSING_GITHUB_EVENT'
    else:
        event = json.loads(Path(event_file).read_text())
        expected_head = (event.get('pull_request') or {}).get('head', {}).get('sha') or os.environ.get('GITHUB_SHA')
        if not expected_head:
            provenance_error = 'MISSING_TRIGGER_HEAD'
        elif expected_head != checkout_sha:
            provenance_error = f'HEAD_MISMATCH expected={expected_head} checkout={checkout_sha}'

receipt = {
    'commit': checkout_sha, 'expected_trigger_head': expected_head,
    'head_binding_status': 'PASS' if os.environ.get('GITHUB_ACTIONS') == 'true' and not provenance_error else ('NOT_CHECKED_LOCAL' if os.environ.get('GITHUB_ACTIONS') != 'true' else 'FAIL'),
    'head_binding_error': provenance_error, 'lean': out('lean', '--version'),
    'mathlib': out('git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'),
    'modules': len(plan), 'passed': sum(v == 'PASS' for v in state['status'].values()),
    'compile_seconds_total': round(sum(state['seconds'].values()), 1),
    'source_sha256': {m: hashlib.sha256(Path(r['path']).read_bytes()).hexdigest() for m, r in sorted(plan.items())},
    'axiom_audits': audits, 'unexpected_axioms': bad, 'sorry_modules': sorries,
    'missing_module_logs': sorted(missing_logs),
    'missing_required': [n for n in required if n not in audits],
    'required_roots': {n: audits.get(n) for n in required},
    'scope': 'Every module compiled from source in this run; no binary reuse. window_L65: for '
             'every compactly supported smooth g with the moment conditions and half-width r, '
             '2r <= 6/5, the Weil zero sum of its autocorrelation has nonnegative real part. '
             'One fixed window only. RHWindowL65ExhaustionV1: RH is equivalent to the arithmetic sign on '
             'the log windows L > 3/5; those windows are not proved. window_L43: the same for '
             '2r <= 4/3, from the relative row certificate Brow <= 52 Q_CvS at NP = 200. '
             'RHWindowL43ExhaustionV1: RH is equivalent to the arithmetic sign on the log windows '
             'L > 2/3; those windows are not proved. window_L118: the same for 2r <= 11/8, from '
             'Brow <= 58 Q_CvS at NP = 250. RHWindowL118ExhaustionV1: RH is equivalent to the '
             'arithmetic sign on the log windows L > 11/16; those windows are not proved. '
             'AegisMathCoreV1: aliases of kernel-checked theorems (windows, criterion, '
             'moment-killer, obstructions) under AegisMath; nothing new is proved there. Not RH.',
}
ok = (receipt['passed'] == len(plan) and not bad and not sorries and not receipt['missing_required'] and not missing_logs and not provenance_error)
receipt['status'] = 'PASS' if ok else 'FAIL'
Path('WINDOW_L65_SOURCE_RECEIPT.json').write_text(json.dumps(receipt, indent=1) + '\n')
for n in required: print(n, audits.get(n))
print('WINDOW_L65_SOURCE', receipt['status'], len(audits), 'axiom roots', len(plan), 'modules')
raise SystemExit(0 if ok else 1)
