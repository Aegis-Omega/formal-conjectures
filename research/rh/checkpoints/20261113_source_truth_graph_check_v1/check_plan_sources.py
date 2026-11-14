"""For every module of a lab build plan (`.lake/real_plan.json`, written by
../20261020_row_budget_bridge/window_l65_source/plan.py), compare the compiled source with every
same-name `.lean` file in the git tree at REV: identical bytes, a difference only in the licence
header and `import` lines, or a different body. Run from the repository root after plan.py.
usage: python3 check_plan_sources.py .lake/real_plan.json REV"""
import collections
import json
import subprocess
import sys

plan, rev = json.load(open(sys.argv[1])), sys.argv[2]
out = subprocess.run(['git', 'ls-tree', '-r', rev], capture_output=True, text=True, check=True).stdout
tree = {l.split('\t')[1]: l.split()[2] for l in out.splitlines()}
by = collections.defaultdict(list)
for path in tree:
    if path.endswith('.lean'):
        by[path.rsplit('/', 1)[-1][:-5]].append(path)


def body(b):
    t = b.decode()
    if t.startswith('/-\nCopyright'):
        t = t.split('-/\n', 1)[1]
    return '\n'.join(l for l in t.strip().split('\n') if not l.startswith('import ')).strip()


origins = collections.Counter(v['origin'] for v in plan.values())
print('plan modules', len(plan), 'by origin', dict(sorted(origins.items())))
kinds, hard = collections.Counter(), collections.OrderedDict()
for m, v in sorted(plan.items()):
    mine = open(v['path'], 'rb').read()
    for c in by.get(m, []):
        other = subprocess.run(['git', 'cat-file', '-p', tree[c]], capture_output=True, check=True).stdout
        k = 'identical' if other == mine else 'header/import only' if body(other) == body(mine) else 'body differs'
        kinds[k] += 1
        if k == 'body differs':
            hard.setdefault((m, v['path']), []).append(c)
print('same-name pairs (compiled source, tree copy):', dict(kinds))
print('modules compiled from a source whose body differs from a same-name tree copy:', len(hard))
for (m, a), cs in hard.items():
    print(f'  {m} | compiled {a} | differs from {", ".join(cs)}')
