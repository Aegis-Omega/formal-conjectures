"""Write research/rh/aegis_math/CATALOG.json. Run from the repo root.

Each entry carries one kind of evidence and is never promoted to another kind:
lean_kernel (checked by the Lean kernel in CI from source, axioms only propext,
Classical.choice, Quot.sound), numerical, literature, external_claim (reported, not replayed)
and open. Lean statements are read from the source files, so a renamed or moved theorem
stops this script instead of leaving a stale entry. Not RH.
"""
import json, re, subprocess
from pathlib import Path

CHECKED = 'fe117ae12374199b9102ea0c58e0689bab585a75'  # all 11 runs on this commit are green
RUNS = {
    'windows': ('rh-cvs-window-l65-source.yml', 41285866006),
    'moment_killer': ('rh-moment-killer-range-v1.yml', 41285865902),
    'snowflake': ('rh-snowflake-log23-globalization-v1.yml', 41285865788),
    'cofinal': ('rh-cofinal-actual-schur-v1.yml', 41285865947),
}
W118 = 'research/rh/checkpoints/20261031_window_l118/RHWindowL118ExhaustionV1.lean'
V13 = 'AegisRH/PR606/V13Scratch.lean'
MK = 'research/rh/moment_killer_v1/'
LAB = 'research/rh/checkpoints/20261101_lambda_lab_s1/README.md'

# (id, AegisMath alias or None, source theorem, file, run key, depends_on)
LEAN = [
    ('windows.window_le_eleven_sixteenths', 'AegisMath.Windows.window_le_eleven_sixteenths',
     'AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths', W118, 'windows', []),
    ('windows.final_sign_iff_windows_above_eleven_sixteenths',
     'AegisMath.Windows.final_sign_iff_windows_above_eleven_sixteenths',
     'AEGIS.RHWindowL118ExhaustionV1.final_sign_iff_windows_above_eleven_sixteenths', W118, 'windows',
     ['windows.window_le_eleven_sixteenths']),
    ('windows.rh_iff_windows_above_eleven_sixteenths', 'AegisMath.Windows.rh_iff_windows_above_eleven_sixteenths',
     'AEGIS.RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths', W118, 'windows',
     ['windows.final_sign_iff_windows_above_eleven_sixteenths', 'criterion.final_sign_iff_rh']),
    ('criterion.final_sign_iff_rh', 'AegisMath.Criterion.final_sign_iff_rh',
     'AEGIS.V13Scratch.final_sign_iff_rh_v13', V13, 'windows', []),
    ('criterion.no_zero_re_gt_half_of_final_sign', 'AegisMath.Criterion.no_zero_re_gt_half_of_final_sign',
     'AEGIS.V13Scratch.no_zero_re_gt_half_of_final_sign_v13', V13, 'windows', []),
    ('moment_killer.exists_momentKiller_packet', 'AegisMath.MomentKiller.exists_momentKiller_packet',
     'AEGIS.WeilMomentKillerPacketRangeV1.exists_momentKiller_packet', MK + 'WeilMomentKillerPacketRangeV1.lean',
     'moment_killer', ['moment_killer.exists_momentKiller_eq']),
    ('moment_killer.exists_momentKiller_eq', 'AegisMath.MomentKiller.exists_momentKiller_eq',
     'AEGIS.WeilMomentKillerRangeV1.exists_momentKiller_eq', MK + 'WeilMomentKillerRangeV1.lean',
     'moment_killer', []),
    ('obstructions.no_common_positive_width', 'AegisMath.Obstructions.no_common_positive_width',
     'AEGIS.RHWidthQuantifierObstructionV1.no_common_positive_width',
     'AEGISOverlay/RHWidthQuantifierObstructionV1.lean', 'snowflake', []),
    ('obstructions.vonMangoldt_weights_do_not_imply_operator_nonnegative',
     'AegisMath.Obstructions.vonMangoldt_weights_do_not_imply_operator_nonnegative',
     'AEGIS.RHEulerOperatorObstructionV1.vonMangoldt_weights_do_not_imply_operator_nonnegative',
     'AEGISOverlay/RHEulerOperatorObstructionV1.lean', 'snowflake', []),
    # Kernel-checked by their own workflows; not in the core root (hierarchical import, or
    # dependencies whose Compat/Source/PR606 copies differ).
    ('obstructions.not_uniformFineMixedBudget', None, 'AEGIS.RHUniformBudgetObstructionV1.not_uniformFineMixedBudget',
     'AEGISOverlay/RHUniformBudgetObstructionV1.lean', 'cofinal', []),
    ('obstructions.extra_mellin_zero_obstructs_universal_approximation', None,
     'AEGIS.RHTranslateSpectralObstructionV1.extra_mellin_zero_obstructs_universal_approximation',
     'AEGISOverlay/RHTranslateSpectralObstructionV1.lean', 'snowflake', []),
]

OTHER = [
    {'id': 'numerical.lambda_a_decay', 'kind': 'numerical', 'source': LAB,
     'statement': 'Ritz upper bounds for the lowest eigenvalue of the Weil form on [-a, a]: '
                  'lambda_a = 9.4e-7 (a = 0.5), 1.3e-12 (a = 11/16), <= 9.3e-42 (a = 2); on moment-zero '
                  'packets 1.7e-7 at a = 11/16 and <= 1.4e-36 at a = 2; decay approaching exp(-4 pi e^{2a}).',
     'limits': 'Upper bounds only; floating point at 200 digits, not interval-certified.'},
    {'id': 'numerical.simple_even_small_a', 'kind': 'numerical', 'source': LAB,
     'statement': 'For a = 0.3, 0.5, 0.6, 11/16 the lowest eigenvalue is simple (lambda2/lambda1 = 29 to 606) '
                  'and its eigenvector is even.', 'limits': 'Finite basis N = 32.'},
    {'id': 'numerical.family_budget_must_decay', 'kind': 'numerical', 'source': LAB,
     'statement': 'Fine moment-zero packets span the moment-zero subspace of [-a, a]; with bounded overlap a '
                  'family bound QW(sum g_i) >= c sum ||g_i||^2 with c independent of a would force lambda0_a >= c/2, '
                  'which the computed upper bounds exclude.',
     'limits': 'Argument written out in the README, not formalized; relies on the numerical upper bounds.',
     'depends_on': ['moment_killer.exists_momentKiller_packet', 'numerical.lambda_a_decay']},
    {'id': 'literature.yoshida_suzuki_continuity', 'kind': 'literature',
     'source': 'Suzuki, arXiv 2606.09096, Thm 1.3 and the remark after it; Yoshida 1992',
     'statement': 'lambda_a is continuous in a; RH holds iff the localized Weil form is nondegenerate for every a.'},
    {'id': 'literature.suzuki_small_a', 'kind': 'literature', 'source': 'Suzuki, arXiv 2606.09096, Thm 1.4',
     'statement': 'For sufficiently small a the lowest eigenvalue is positive and simple, with an even eigenfunction.'},
    {'id': 'literature.ccm_spectral_triples', 'kind': 'literature',
     'source': 'Connes, Consani, Moscovici, arXiv 2511.22755, Thm 1.1, Cor 3.8, Section 8',
     'statement': 'If the lowest eigenvalue is simple with even eigenvector, the Fourier transform of that '
                  'eigenvector has only real zeros; if lim mu_lambda = 0 then RH. Missing steps: simple-even for '
                  'all lambda, and the prolate approximation of the eigenvector.'},
    {'id': 'external.paid_resonance_log5', 'kind': 'external_claim',
     'source': 'reported 2026-11-01 by another system (aegis-nov1 workspace, PAID_RESONANCE_ADDENDUM.md); not in this repository',
     'statement': 'For two moment-zero packets of half-width 1/256 at distance log 5: '
                  '-Re B(p+q, p+q) >= (1 + 319/204800)(E_p + E_q).',
     'limits': 'No Lean replay; local pairwise bound, compatible with numerical.family_budget_must_decay only locally.'},
    {'id': 'open.windows_above_eleven_sixteenths', 'kind': 'open',
     'statement': 'forall L > 11/16, WindowArithmeticNonpositiveV1 L (equivalent to RH by '
                  'windows.rh_iff_windows_above_eleven_sixteenths).',
     'depends_on': ['windows.rh_iff_windows_above_eleven_sixteenths']},
    {'id': 'open.global_signed_budget', 'kind': 'open',
     'statement': 'A producer of the total signed budget of resonant interactions for arbitrary packet families; '
                  'its constant must decay at least like lambda0_a in the spread.',
     'depends_on': ['numerical.family_budget_must_decay']},
    {'id': 'open.official_rh', 'kind': 'open', 'source': 'FormalConjectures/Millennium/RiemannHypothesis.lean',
     'statement': 'RiemannHypothesis.riemannHypothesis; its axioms include sorryAx.'},
]

def git(*a):
    return subprocess.run(['git', *a], capture_output=True, text=True).stdout.strip()

def statement(path, full):
    short = full.rsplit('.', 1)[1]
    t = Path(path).read_text()
    m = re.search(r'^(?:theorem|lemma) ' + re.escape(short) + r'\b(.*?):=', t, re.S | re.M)
    if not m:
        raise SystemExit(f'STATEMENT_NOT_FOUND {full} {path}')
    return ' '.join(m.group(1).split())

CAT = Path('research/rh/aegis_math/CATALOG.json')
INDEX = Path('research/rh/aegis_math/INDEX.tsv')
INDEX_RUNS = {'rh-cofinal-actual-schur-v1.yml': 41285865947, 'rh-consolidated-v1.yml': 41285865807,
              'rh-cvs-actual-row-replay.yml': 41285865827, 'rh-cvs-window-l65-source.yml': 41285866006,
              'rh-feshbach-schur-v1.yml': 41285865808, 'rh-moment-killer-range-v1.yml': 41285865902,
              'rh-snowflake-log23-globalization-v1.yml': 41285865788}

def declared(path, full):
    prefix, short = full.rsplit('.', 1) if '.' in full else ('', full)
    t = Path(path).read_text()
    if not re.search(r'^(theorem|lemma) ' + re.escape(short) + r'\b', t, re.M):
        return False
    spaces = re.findall(r'^namespace ([A-Za-z0-9_.]+)', t, re.M)
    return prefix == '' or prefix in spaces or '.'.join(spaces).endswith(prefix)

entries = []
for eid, alias, src, path, run, deps in LEAN:
    blob = git('hash-object', path)
    then = git('rev-parse', f'{CHECKED}:{path}')
    if then and then != blob:
        raise SystemExit(f'SOURCE_CHANGED_SINCE_CHECK {path}')
    e = {'id': eid, 'kind': 'lean_kernel', 'name': alias, 'source_name': src, 'source': path, 'blob': blob,
         'workflow': RUNS[run][0], 'statement': statement(path, src)}
    if deps:
        e['depends_on'] = deps
    entries.append(e)

# INDEX.tsv: theorems covered by the fail-closed axiom audit of a green workflow, harvested from the
# workflow sources. Every row must be a theorem declared in that file under that namespace, with a
# readable statement, in a file byte-identical to the one the green run compiled; otherwise stop.
rows = [l.split('\t') for l in INDEX.read_text().splitlines() if l and not l.startswith('#')]
names = {e['source_name'] for e in entries}
for name, path, wf, area, role in rows:
    if name in names:
        raise SystemExit(f'INDEX_DUPLICATE {name}')
    names.add(name)
    if wf not in INDEX_RUNS or not Path(path).is_file() or not declared(path, name):
        raise SystemExit(f'INDEX_ROW_INVALID {name} {path} {wf}')
    if git('rev-parse', f'{CHECKED}:{path}') != git('hash-object', path):
        raise SystemExit(f'INDEX_SOURCE_CHANGED_SINCE_CHECK {path}')
    statement(path, name)
entries += OTHER
ids = {e['id'] for e in entries}
if len(ids) != len(entries):
    raise SystemExit('DUPLICATE_ID')
for e in entries:
    for d in e.get('depends_on', []):
        if d not in ids:
            raise SystemExit(f'UNKNOWN_DEPENDENCY {e["id"]} -> {d}')
out = {'schema': 'aegis-math-catalog/v1', 'core': 'research/rh/aegis_math/AegisMathCoreV1.lean',
       'kinds': ['lean_kernel', 'numerical', 'literature', 'external_claim', 'open'],
       'lean_kernel_means': 'the named workflow compiles the source from scratch and its fail-closed axiom audit '
                            '(a #print axioms line or a required-name list) covers the theorem; its run on '
                            'checked_commit passed and the file blob equals the one compiled there',
       'checked_commit': CHECKED, 'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
       'runs': dict(sorted({**dict(RUNS.values()), **INDEX_RUNS}.items())),
       'index': {'file': 'research/rh/aegis_math/INDEX.tsv', 'rows': len(rows), 'all_rows_verified': True},
       'entries': entries}
CAT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('CATALOG', len(entries), 'entries; INDEX', len(rows), 'rows verified')
