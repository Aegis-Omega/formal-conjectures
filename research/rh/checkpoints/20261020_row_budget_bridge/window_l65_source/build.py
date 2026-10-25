"""Compile .lake/real_plan.json from source into .lake/ringout, in parallel topological order.

Usage: python3 build.py EXTRA_LEAN_PATH [WORKERS] [--resume]. Run from the repo root.
Each module is compiled after all its imports passed, with the flags the existing replay uses for
it (-DwarningAsError=true and -R where they apply). A module killed by a signal (out of memory)
is retried alone, at most twice. A failed module blocks its dependants. --resume keeps modules
that passed in an earlier local run of this script. Logs go to .lake/reallogs/<Module>.log,
status to .lake/real_status.json.
"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
from functools import lru_cache
from pathlib import Path
args = [a for a in sys.argv[1:] if a != '--resume']
plan = json.loads(Path('.lake/real_plan.json').read_text())
ring = Path('.lake/ringout').resolve(); ring.mkdir(parents=True, exist_ok=True)
logs = Path('.lake/reallogs'); logs.mkdir(exist_ok=True)
sp = Path('.lake/real_status.json')
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join([str(ring), args[0], subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()])
workers = int(args[1]) if len(args) > 1 else 3
users = {m: [] for m in plan}
for m, r in plan.items():
    for d in r['deps']: users[d].append(m)
@lru_cache(None)
def height(m):  # longest chain of dependants; start those first
    return 1 + max((height(u) for u in users[m]), default=0)
status, seconds, kills = {}, {}, {}
if '--resume' in sys.argv and sp.exists():
    old = json.loads(sp.read_text()); old_status = old.get('status', old)
    for m, v in old_status.items():
        if v == 'PASS' and m in plan and (ring/(m + '.olean')).is_file() and (logs/(m + '.log')).is_file():
            status[m] = 'PASS'; seconds[m] = old.get('seconds', {}).get(m, 0)
    print('RESUME', len(status), 'modules kept', flush=True)
def run(mod):
    r = plan[mod]
    cmd = ['lean'] + (['-DwarningAsError=true'] if r['strict'] else []) + (['-R', r['root']] if r['root'] else []) + ['-o', str(ring/(mod + '.olean')), r['path']]
    t = time.monotonic(); p = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logs/(mod + '.log')).write_text(' '.join(cmd) + '\n' + p.stdout + f'\n[exit {p.returncode}]\n')
    return mod, p.returncode, ': error' not in p.stdout, time.monotonic() - t
pending, running, solo = set(plan) - set(status), {}, []
with ThreadPoolExecutor(workers) as pool:
    while pending or running or solo:
        for m in [m for m in pending if any(status.get(d) in ('FAIL', 'BLOCKED') for d in plan[m]['deps'])]:
            pending.discard(m); status[m] = 'BLOCKED'
        if solo:  # drain, then rerun the killed module alone
            if not running: m = solo.pop(0); running[pool.submit(run, m)] = m
        else:
            ready = sorted((m for m in pending if all(status.get(d) == 'PASS' for d in plan[m]['deps'])), key=lambda m: (-height(m), m))
            for m in ready[:max(0, workers - len(running))]:
                pending.discard(m); running[pool.submit(run, m)] = m
        if not running:
            if pending: raise SystemExit('DEADLOCK ' + ' '.join(sorted(pending)[:10]))
            continue
        done, _ = wait(running, return_when=FIRST_COMPLETED)
        for f in done:
            m, code, clean, s = f.result(); del running[f]; seconds[m] = round(s, 1)
            if code < 0 and kills.get(m, 0) < 2:
                kills[m] = kills.get(m, 0) + 1; solo.append(m); print('KILLED', m, code, 'retry alone', flush=True); continue
            status[m] = 'PASS' if code == 0 and clean else 'FAIL'
            print(status[m], m, seconds[m], f'{sum(v == "PASS" for v in status.values())}/{len(plan)}', flush=True)
            sp.write_text(json.dumps({'status': status, 'seconds': seconds, 'killed': kills}, indent=0))
bad = sorted(m for m, v in status.items() if v != 'PASS')
print('REAL_BUILD', 'PASS' if not bad else 'FAIL', len(plan) - len(bad), '/', len(plan), ' '.join(bad[:20]))
raise SystemExit(1 if bad else 0)
