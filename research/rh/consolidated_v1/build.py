#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Compile the consolidated RH development from committed sources.

Every module comes from exactly one file listed in manifest.json, pinned by SHA-256.
Modules are compiled in import order (independent modules in parallel) into one output
directory, and the axioms of the headline theorems are audited.

usage: build.py OUT_DIR LOG_FILE [JOBS]   (run from the repository root, inside `lake env`)
"""
import concurrent.futures as cf
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADLINE = [
    "AEGIS.RHConsolidatedV1.rh_iff_all_windows",
    "AEGIS.RHConsolidatedV1.windows_below_21_40",
    "AEGIS.RHConsolidatedV1.rh_iff_windows_from_21_40",
    "AEGIS.RHConsolidatedV1.consolidated",
]


def imports(path):
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*(?:public\s+)?import\s+(.+)", line.split("--", 1)[0])
        if m:
            out += m.group(1).split()
    return out


def main():
    out, log = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    entries = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    mods = {e["module"]: e for e in entries}
    bad = [e["path"] for e in entries
           if hashlib.sha256(Path(e["path"]).read_bytes()).hexdigest() != e["sha256"]]
    if bad:
        sys.exit("SHA-256 mismatch: " + ", ".join(bad))
    deps = {m: [d for d in imports(Path(e["path"])) if d in mods] for m, e in mods.items()}
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=f"{out}:{os.environ.get('LEAN_PATH', '')}")
    done, started, failed = set(), set(), []
    logs = {}
    if os.environ.get("RHC_RESUME") == "1":  # local restarts only; CI always builds from scratch
        done = {m for m in mods if (out / (m.replace(".", "/") + ".olean")).exists()}
        started = set(done)

    def compile_one(m):
        e = mods[m]
        rel = m.replace(".", "/") + ".lean"
        assert e["path"].endswith(rel), (m, e["path"])
        root = e["path"][: -len(rel)] or "."
        olean = out / (m.replace(".", "/") + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        t = time.time()
        r = subprocess.run(["lean", "-R", root, "-o", str(olean), e["path"]],
                           env=env, capture_output=True, text=True)
        return m, r.returncode, r.stdout + r.stderr, time.time() - t

    with cf.ThreadPoolExecutor(jobs) as ex:
        running = {}
        while len(done) < len(mods) and not failed:
            for m in mods:
                if m not in started and all(d in done for d in deps[m]):
                    started.add(m)
                    running[ex.submit(compile_one, m)] = m
            fin, _ = cf.wait(running, return_when=cf.FIRST_COMPLETED)
            for f in fin:
                del running[f]
                m, rc, text, secs = f.result()
                logs[m] = text
                print(f"{'OK  ' if rc == 0 else 'FAIL'} {m} {secs:.0f}s", flush=True)
                if rc != 0 or re.search(r"(?m)^[^:\n]*:\d+:\d+: error", text):
                    failed.append(m)
                else:
                    done.add(m)
        for f in cf.as_completed(running):
            m, rc, text, secs = f.result()
            logs[m] = text

    log.write_text("".join(f"== {m}\n{logs.get(m, '')}" for m in mods), encoding="utf-8")
    if failed:
        for m in failed:
            print(logs[m])
        sys.exit(f"compile failed: {failed}")

    text = log.read_text(encoding="utf-8")
    if "sorryAx" in text or re.search(r"declaration uses 'sorry'", text):
        sys.exit("sorry found")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    for name, axs in reports:
        extra = {a.strip() for a in axs.split(",") if a.strip()} - ALLOWED
        if extra:
            sys.exit(f"{name} uses non-standard axioms: {sorted(extra)}")
    named = {name for name, _ in reports}
    missing = [h for h in HEADLINE if h not in named]
    if missing:
        sys.exit(f"headline theorems not reported: {missing}")
    print(f"{len(mods)} modules compiled; {len(reports)} axiom reports, all within {sorted(ALLOWED)}")
    for h in HEADLINE:
        print(f"  {h}: OK")


if __name__ == "__main__":
    main()
