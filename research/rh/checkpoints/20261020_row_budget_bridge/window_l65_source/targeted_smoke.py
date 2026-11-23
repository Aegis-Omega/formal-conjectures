#!/usr/bin/env python3
"""Exact-head 5-module RH import smoke; no GitHub Actions dispatch, no RH claim.

Execute only in a clean checkout with pinned Lean 4.33.1 and Mathlib installed:
python3 research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source/targeted_smoke.py --head "$(git rev-parse HEAD)"
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

BASE = Path('research/rh/checkpoints/20261020_row_budget_bridge/window_l65_source')
ROOTS = (
    'FormalConjectures.Millennium.RHSnowflakeLog23',
    'FormalConjecturesUtil.FixedWindowLimitBridge',
    'AEGISOverlay.RHMultiGeneratorComplementarityV1',
    'WeilLogTransportCanonicalV1',
)
EXPECTED = set(ROOTS) | {'WeilMomentKillerConstructionV1'}
REQUIRED = {
    'RHSnowflakeLog23.irrational_log_two_div_log_three',
    'RHSnowflakeLog23.snowflake_shift_group_dense',
    'RHSnowflakeLog23.snowflake_nonnegative_of_continuous',
    'FormalConjecturesUtil.FixedWindowLimitBridge.nonneg_of_cofinal_nested_shifted_sections',
    'AEGIS.RHMultiGeneratorComplementarityV1.sinc_no_common_zero_of_irrational',
    'AEGIS.RHMultiGeneratorComplementarityV1.log23_momentSpline_no_common_zero',
    'AEGIS.RHMultiGeneratorComplementarityV1.order19_log23_continuous_spectral_bezout',
    'AEGIS.WeilLogTransportCanonicalV1.integral_mulPacket',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'


def run(*cmd, env=None):
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, env=env)
    if p.returncode:
        print(p.stdout[-6000:], file=sys.stderr)
        raise SystemExit(f'COMMAND_FAILED exit={p.returncode}: {cmd[0]}')
    return p.stdout


def audit(logs):
    out = {}
    for mod, text in logs.items():
        if re.search(r"\bsorryAx\b|declaration uses 'sorry'", text):
            raise ValueError('SORRY_AXIOM ' + mod)
        if mod != 'probe' and '\n[exit 0]' not in text:
            raise ValueError('MISSING_SUCCESS_EXIT ' + mod)
        for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
            values = sorted(x.strip() for x in raw.split(',') if x.strip())
            if not set(values) <= ALLOWED:
                raise ValueError('UNEXPECTED_AXIOMS ' + name + ' ' + str(values))
            if name in out and out[name] != values:
                raise ValueError('AXIOM_CONFLICT ' + name)
            out[name] = values
        for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
            out.setdefault(name, [])
    if REQUIRED - out.keys():
        raise ValueError('MISSING_AXIOM_ROOTS ' + str(sorted(REQUIRED - out.keys())))
    return {name: out[name] for name in sorted(REQUIRED)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--head', required=True, help='Exact 40-character checkout SHA')
    args = ap.parse_args()
    if not re.fullmatch('[0-9a-f]{40}', args.head):
        raise SystemExit('EXPECTED_FULL_HEAD_SHA')
    head = run('git', 'rev-parse', 'HEAD').strip()
    if head != args.head:
        raise SystemExit('HEAD_MISMATCH ' + head)
    run('git', 'diff', '--exit-code')
    run('git', 'diff', '--cached', '--exit-code')
    if '4.33.1' not in run('lean', '--version'):
        raise SystemExit('LEAN_VERSION_MISMATCH')
    if run('git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD').strip() != MATHLIB:
        raise SystemExit('MATHLIB_SHA_MISMATCH')
    ring = Path('.lake/ringout')
    if (ring.exists() and any(ring.iterdir())) or Path('.lake/real_status.json').exists():
        raise SystemExit('REQUIRES_SEPARATE_CLEAN_CHECKOUT; DO_NOT_OVERWRITE_OLD_RESULTS')

    run(sys.executable, str(BASE / 'plan.py'), *ROOTS)
    plan = json.loads(Path('.lake/real_plan.json').read_text())
    if set(plan) != EXPECTED:
        raise SystemExit('INCORRECT_SMOKE_DAG ' + str(sorted(plan)))
    for module in ROOTS[:2]:
        if plan[module]['origin'] != 'local-formal-source':
            raise SystemExit('WRONG_FORMAL_SOURCE ' + module)
    for module, dep in {
        'AEGISOverlay.RHMultiGeneratorComplementarityV1':
            'FormalConjectures.Millennium.RHSnowflakeLog23',
        'WeilLogTransportCanonicalV1': 'WeilMomentKillerConstructionV1',
    }.items():
        if dep not in plan[module]['deps']:
            raise SystemExit('IMPORT_EDGE_MISSING ' + module + ' -> ' + dep)

    # Reuse the exact existing source-aware compiler, one worker, no --resume.
    run(sys.executable, '-u', str(BASE / 'build.py'),
        str(Path('.lake/build/lib/lean').resolve()), '1')
    statuses = json.loads(Path('.lake/real_status.json').read_text())['status']
    if statuses != {module: 'PASS' for module in EXPECTED}:
        raise SystemExit('NOT_ALL_MODULES_PASS ' + str(statuses))
    logs = {}
    for module in EXPECTED:
        target = Path('.lake/reallogs') / (module + '.log')
        if not target.is_file():
            raise SystemExit('MISSING_LEAN_LOG ' + module)
        logs[module] = target.read_text()

    # The original transport source has no #print axioms: use an imported
    # terminal theorem as an additional actual kernel/axiom probe.
    probe = ring / 'pr92_probe.lean'
    probe.write_text(
        'import WeilLogTransportCanonicalV1\n'
        '#print axioms AEGIS.WeilLogTransportCanonicalV1.integral_mulPacket\n'
    )
    env = os.environ.copy()
    env['LEAN_PATH'] = str(ring.resolve()) + ':' + run(
        'lake', 'env', 'printenv', 'LEAN_PATH').strip()
    logs['probe'] = run('lean', '-DwarningAsError=true', str(probe), env=env)
    roots = audit(logs)

    receipt = {
        'status': 'PASS',
        'scope': 'FIVE_MODULE_IMPORT_SMOKE_ONLY_NOT_RH',
        'head': head,
        'lean': run('lean', '--version').strip(),
        'mathlib': MATHLIB,
        'source_sha256': {
            m: hashlib.sha256(Path(plan[m]['path']).read_bytes()).hexdigest()
            for m in sorted(EXPECTED)
        },
        'required_axiom_roots': roots,
        'compiled_modules': sorted(EXPECTED),
    }
    output = Path('.lake/RH_PR92_TARGETED_SMOKE_RECEIPT.json')
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print('PR92_TARGETED_SMOKE PASS', head, 'modules=5', 'axiom_roots=8')
    print('RECEIPT', output)


if __name__ == '__main__':
    main()
