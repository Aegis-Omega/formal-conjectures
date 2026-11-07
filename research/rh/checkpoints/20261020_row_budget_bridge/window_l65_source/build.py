"""Compile .lake/real_plan.json from source into .lake/ringout, in parallel topological order.

Usage: python3 build.py EXTRA_LEAN_PATH [WORKERS] [--resume]. Run from the repo root.
Each module is compiled after all its imports passed, with the flags the existing replay uses for
it (-DwarningAsError=true and -R where they apply). A module killed by a signal (out of memory)
is retried alone, at most twice. No new module starts while less than 6 GB is available, and below
2.5 GB the youngest running compile is killed (and so retried alone), so that several large kernel
checks at once cannot take the runner down. A failed module blocks its dependants. --resume keeps
modules that passed in an earlier local run of this script. Logs go to .lake/reallogs/<Module>.log,
status to .lake/real_status.json.
"""
import json, os, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
from functools import lru_cache
from pathlib import Path
args = [a for a in sys.argv[1:] if a != '--resume']
plan = json.loads(Path('.lake/real_plan.json').read_text())
ring = Path('.lake/ringout').resolve(); ring.mkdir(parents=True, exist_ok=True)
def olean_for(mod):
    return ring / (mod.replace('.', '/') + '.olean')
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
        if v == 'PASS' and m in plan and olean_for(m).is_file() and (logs/(m + '.log')).is_file():
            status[m] = 'PASS'; seconds[m] = old.get('seconds', {}).get(m, 0)
    print('RESUME', len(status), 'modules kept', flush=True)
procs, plock = {}, threading.Lock()  # module -> (process, start time) of the running compiles
def avail_kb():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'): return int(line.split()[1])
    return 1 << 40
def guard():  # keep the machine away from the kernel OOM killer
    while True:
        time.sleep(1)
        if avail_kb() < 2_500_000:
            with plock:
                if len(procs) < 2: continue
                mod, (p, _) = max(procs.items(), key=lambda kv: kv[1][1])
            print('MEMGUARD', mod, avail_kb(), flush=True); p.kill(); time.sleep(10)
threading.Thread(target=guard, daemon=True).start()
def run(mod):
    r = plan[mod]
    obj = olean_for(mod)
    obj.parent.mkdir(parents=True, exist_ok=True)
    cmd = ['lean'] + (['-DwarningAsError=true'] if r['strict'] else []) + (['-R', r['root']] if r['root'] else []) + ['-o', str(obj), r['path']]
    t = time.monotonic(); p = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    with plock: procs[mod] = (p, t)
    out, _ = p.communicate()
    with plock: procs.pop(mod, None)
    (logs/(mod + '.log')).write_text(' '.join(cmd) + '\n' + out + f'\n[exit {p.returncode}]\n')
    return mod, p.returncode, ': error' not in out, time.monotonic() - t
pending, running, solo = set(plan) - set(status), {}, []
with ThreadPoolExecutor(workers) as pool:
    while pending or running or solo:
        for m in [m for m in pending if any(status.get(d) in ('FAIL', 'BLOCKED') for d in plan[m]['deps'])]:
            pending.discard(m); status[m] = 'BLOCKED'
        if solo:  # drain, then rerun the killed module alone
            if not running: m = solo.pop(0); running[pool.submit(run, m)] = m
        else:
            ready = sorted((m for m in pending if all(status.get(d) == 'PASS' for d in plan[m]['deps'])), key=lambda m: (-height(m), m))
            free = workers - len(running) if not running or avail_kb() >= 6_000_000 else 0
            for m in ready[:max(0, free)]:
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
