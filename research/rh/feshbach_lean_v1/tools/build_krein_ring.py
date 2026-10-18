"""Compile the krein_ring_v1 source closure from sources, in topological order.

Usage: python3 build_krein_ring.py CLOSURE_JSON OUT_DIR LOG_FILE

Every module's source blob is checked against the pinned closure before it is compiled.
`.lean.src` snapshot files are staged as `.lake/ringstage/<Module>.lean`, inside the package root.
LEAN_PATH must already contain OUT_DIR first, then the provider and Mathlib paths.
"""
import json
import pathlib
import subprocess
import sys

closure = json.loads(pathlib.Path(sys.argv[1]).read_text())
out = pathlib.Path(sys.argv[2]).resolve()
log = pathlib.Path(sys.argv[3])
out.mkdir(parents=True, exist_ok=True)
stage = pathlib.Path('.lake/ringstage')
stage.mkdir(parents=True, exist_ok=True)
assert closure['schema'] == 'aegis.rh.krein_ring.closure.v1', closure['schema']

with log.open('w') as lf:
    for rec in closure['modules']:
        src = pathlib.Path(rec['path'])
        blob = subprocess.run(['git', 'hash-object', str(src)], capture_output=True, text=True,
                              check=True).stdout.strip()
        if blob != rec['blob']:
            raise SystemExit(f"SOURCE_BLOB_MISMATCH {rec['module']} {blob} != {rec['blob']}")
        if src.suffix == '.src':
            staged = stage / (rec['module'] + '.lean')
            staged.write_bytes(src.read_bytes())
            src = staged
        target = out / (rec['module'].replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        r = subprocess.run(['lean', '-o', str(target), str(src)], capture_output=True, text=True)
        text = r.stdout + r.stderr
        lf.write(f"=== {rec['module']} ({rec['path']})\n{text}\n")
        lf.flush()
        if r.returncode != 0 or ': error' in text:
            print(text[:4000])
            raise SystemExit(f"COMPILE_FAILED {rec['module']}")
        print('OK', rec['module'], flush=True)
print('KREIN_RING_BUILT', len(closure['modules']))
