"""Resolve the from-source module DAG of one or more root modules (default CvSWindowL65V1). Run from
the repo root.

Every source is taken where the existing replay scripts take it, with the same hash checks:
ACTUAL_INPUT_SOURCES.zip (run_ci_actual_inputs.py), FULL_TABLE_SOURCES.zip (run_ci_full_table.py),
krein_ring_closure.json (build_krein_ring.py, git blob pinned), the explicit `lean -o "$RING/..."`
lines of the two workflows, and the moment, join and K3 sources. Two sources for one module name
that differ beyond the license header abort; otherwise the first one listed is compiled.
Writes .lake/real_plan.json for build.py. No artifact is downloaded.
"""
import json, zipfile, hashlib, re, sys, subprocess
from pathlib import Path
repo = Path.cwd()
B = Path('research/rh/checkpoints/20261020_row_budget_bridge')
dig = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = {}   # module -> (path, strict, rootdir or None, origin)
def code(b):  # source without the license comment and blank lines
    t = re.sub(r'/-(?:(?!-/).)*?(?:Copyright|Licensed under)(?:(?!-/).)*?-/', '', b.decode(), flags=re.S)
    return [l.rstrip() for l in t.splitlines() if l.strip()]
def put(mod, path, strict, root, origin):
    path = Path(path)
    if mod in src and src[mod][0] != path:
        prev = src[mod]
        if code(prev[0].read_bytes()) != code(path.read_bytes()):
            raise SystemExit(f'SOURCE_CONFLICT {mod} {prev[0]} {path}')
        return
    src.setdefault(mod, (path, strict, root, origin))
# 1. actual-input zip (official extraction + hash checks of run_ci_actual_inputs.py)
d = B/'actual_input_execution'; out = Path('.lake/actual-input-sources'); out.mkdir(parents=True, exist_ok=True)
m = json.loads((d/'ACTUAL_INPUT_SOURCE_MANIFEST.json').read_text()); arc = d/'ACTUAL_INPUT_SOURCES.zip'
assert dig(arc) == m['archive_sha256']
with zipfile.ZipFile(arc) as z:
    for n in z.namelist():
        assert Path(n).name == n
        if n.endswith('.lean'): (out/n).write_bytes(z.read(n))
    sj = hashlib.sha256(z.read('EXACT_SOURCE_BRIDGE_INPUTS.json')).hexdigest()
for a in m['sources']: assert dig(out/a['name']) == a['sha256'], a['name']
for n, o in m.get('unchanged_existing_source_copies', {}).items():
    assert dig(out/n) == o['sha256'], n  # the archived copy is what gets compiled
    live = (repo/o['original_path']).read_bytes()
    if hashlib.sha256(live).hexdigest() != o['sha256']:  # only a license-header edit is tolerated
        assert code(live) == code((out/n).read_bytes()), 'EXISTING_BASIS_SOURCE_CHANGED ' + n
        print('HEADER_ONLY_DRIFT', n)
assert sj == json.loads((B/'full_table_execution/SOURCE_BINDING_NEXT_INPUTS.json').read_text())['sha256']
for p in sorted(out.glob('*.lean')): put(p.stem, p, True, out, 'actual-zip')
# 2. full-table zip (run_ci_full_table.py)
d = B/'full_table_execution'; out = Path('.lake/full-table-source'); out.mkdir(parents=True, exist_ok=True)
m = json.loads((d/'SOURCE_MANIFEST.json').read_text()); arc = d/'FULL_TABLE_SOURCES.zip'
assert dig(arc) == m['archive_sha256']
with zipfile.ZipFile(arc) as z:
    for n in z.namelist():
        assert Path(n).name == n
        if n.endswith('.lean'): (out/n).write_bytes(z.read(n))
for r in m['sources']: assert dig(out/r['path']) == r['sha256'], r['path']
put('CvSPackedIntervalDotV1', B/'packed_execution/CvSPackedIntervalDotV1.lean', True, B/'packed_execution', 'full-extra')
put('CvSRowBudgetAlgebraV1', 'research/rh/checkpoints/20261020_row_budget/CvSRowBudgetAlgebraV1.lean', True, Path('research/rh/checkpoints/20261020_row_budget'), 'full-extra')
for p in sorted(out.glob('*.lean')): put(p.stem, p, True, out, 'full-zip')
# 3. krein ring closure (build_krein_ring.py, with blob checks)
cl = json.loads(Path('research/rh/feshbach_lean_v1/tools/krein_ring_closure.json').read_text())
stage = Path('.lake/ringstage'); stage.mkdir(parents=True, exist_ok=True)
for rec in cl['modules']:
    p = Path(rec['path'])
    blob = subprocess.run(['git', 'hash-object', str(p)], capture_output=True, text=True, check=True).stdout.strip()
    assert blob == rec['blob'], rec
    if p.suffix == '.src':
        s = stage/(rec['module'] + '.lean'); s.write_bytes(p.read_bytes()); p = s
    put(rec['module'], p, False, None, 'closure')
# 4. explicit workflow lines
for wf in ['.github/workflows/rh-cvs-actual-row-replay.yml', '.github/workflows/rh-feshbach-schur-v1.yml']:
    t = Path(wf).read_text()
    for strict, mod, path in re.findall(r'lean (-DwarningAsError=true )?-o "\$RING/([A-Za-z0-9_]+)\.olean" ([^\s]+\.lean)', t):
        put(mod, path, bool(strict), None, 'wf')
    for block in re.findall(r'for m in ([^;]+); do\s*\n\s*lean -o "\$RING/\$m\.olean" "([^"]+)/\$m\.lean"', t):
        for mod in block[0].replace('\\', ' ').split():
            put(mod, f'{block[1]}/{mod}.lean', False, None, 'wf-loop')
# 5. moment / join / K3 scripts
for mod in ['CvSMomentTraceV1', 'CvSMomentWindowBridgeV1', 'CvSActualMomentWindowJoinV1', 'CvSWindowL65V1']:
    put(mod, B/(mod + '.lean'), True, None, 'script')
for r in json.loads(Path('research/rh/feshbach_lean_v1/tools/krein_trace_modules.json').read_text())['modules']:
    put(r['name'], f"research/rh/feshbach_lean_v1/{r['name']}.lean", True, None, 'k3json')
put('CvSHplusBoundsV1', 'research/rh/feshbach_lean_v1/CvSHplusBoundsV1.lean', True, None, 'k3')
# 5b. the window 2r <= 4/3: the relative row certificate, the window and its exhaustion join
for mod in ['CvSRelRowAlgebraV1', 'CvSRelRowHarmV1', 'CvSRelRowDataL43V1', 'CvSRelRowCertL43V1',
            'CvSRelRowCheckL43V1', 'CvSRelRowPsdL43V1', 'CvSRelRowFormL43V1', 'CvSRelRowBoxL43V1',
            'CvSRelRowErrL43V1', 'CvSRelRowQL43V1', 'CvSRelRowKtL43V1', 'CvSRelRowOutL43V1',
            'CvSRelRowTailL43V1', 'CvSRelRowInvL43V1', 'CvSRelRowInL43V1', 'CvSRelRowHBL43V1']:
    put(mod, f'research/rh/feshbach_lean_v1/{mod}.lean', True, None, 'l43')
for mod in ['CvSWindowL43V1', 'RHWindowL43ExhaustionV1']:
    put(mod, f'research/rh/checkpoints/20261026_window_l43/{mod}.lean', True, None, 'l43')
# 6. window exhaustion and the V13 RH bridge, for names no earlier source provides. The ported
# copies differ on purpose, so the first directory wins, in the order of
# aegis-pr606-fork-replay-v1.yml: Compat, then Source, then the PR606 port.
for d, origin in [('AegisRH/PR606/Compat', 'pr606-compat'), ('AegisRH/PR606/Source', 'pr606-source'),
                  ('AegisRH/PR606', 'pr606'), ('AegisRH/SmallWindow', 'small-window')]:
    for p in sorted(Path(d).glob('*.lean')): src.setdefault(p.stem, (p, False, None, origin))
put('RHWindowL65ExhaustionV1', B/'RHWindowL65ExhaustionV1.lean', True, None, 'script')
ext = ('Mathlib', 'Lean', 'Std', 'Batteries', 'Aesop', 'Qq', 'Init', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient')
prov = ('Lc', 'Hadamard', 'FunctionsOfOneComplexVariable')
def imports(p):
    t = re.sub(r'/-.*?-/', '', p.read_text(), flags=re.S)
    return re.findall(r'^import\s+([A-Za-z0-9_.]+)', t, flags=re.M)
need, todo, deps, missing = set(), sys.argv[1:] or ['CvSWindowL65V1'], {}, set()
while todo:
    mod = todo.pop()
    if mod in need: continue
    if mod not in src: missing.add(mod); continue
    need.add(mod); ds = []
    for i in imports(src[mod][0]):
        if i.split('.')[0] in ext + prov or i.startswith('FormalConjectures'): continue
        ds.append(i); todo.append(i)
    deps[mod] = ds
if missing: raise SystemExit('MISSING_SOURCE ' + ' '.join(sorted(missing)))
print('PLAN', len(need), 'modules')
from collections import Counter
print(Counter(src[x][3] for x in need))
json.dump({mod: {'path': str(src[mod][0]), 'strict': src[mod][1], 'root': str(src[mod][2]) if src[mod][2] else None,
                 'origin': src[mod][3], 'deps': deps[mod]} for mod in need}, open('.lake/real_plan.json', 'w'), indent=1)
ext_used = set()
for mod in need:
    for i in imports(src[mod][0]):
        if i.split('.')[0] in prov or i.startswith('FormalConjectures'): ext_used.add(i)
print('provider/FC imports', sorted(ext_used))
