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

usage: build.py OUT_DIR LOG_FILE [JOBS [STAGE]]   (run from the repository root, inside `lake env`)

STAGE splits the build so CI can spread it over several runners:
  all          every module (the default)
  base         every module that does not import an L = 21/20 batch certificate
  shard:K/N    the K-th of N shards of the batch certificates (K = 0 .. N-1)
  final        the modules that import the batch certificates, then the headline audit
A stage expects the .olean files of the earlier stages in OUT_DIR.

A batch certificate peaks at about 9 GiB while it is kernel-checked, so at most
RHC_HEAVY_JOBS of them (default 1) are compiled at the same time.
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
BATCH = re.compile(r"RHKreinL105Batch(\d+)")  # the decide +kernel cells of the L = 21/20 certificate


def imports(path):
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*(?:public\s+)?import\s+(.+)", line.split("--", 1)[0])
        if m:
            out += m.group(1).split()
    return out


def stage_targets(stage, mods, deps):
    batch = {m for m in mods if BATCH.match(m)}
    after = set()  # modules importing a batch certificate, directly or not
    grew = True
    while grew:
        grew = False
        for m in mods:
            if m not in batch and m not in after and any(d in batch or d in after for d in deps[m]):
                after.add(m)
                grew = True
    if stage == "all":
        return set(mods)
    if stage == "base":
        return set(mods) - batch - after
    if stage == "final":
        return after
    s = re.fullmatch(r"shard:(\d+)/(\d+)", stage)
    if not s or not int(s[1]) < int(s[2]):
        sys.exit(f"unknown stage {stage!r}")
    families = sorted({BATCH.match(b)[1] for b in batch})  # 007 and its parts 007p0.. stay together
    mine = set(families[int(s[1])::int(s[2])])
    return {b for b in batch if BATCH.match(b)[1] in mine}


def main():
    out, log = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    stage = sys.argv[4] if len(sys.argv) > 4 else "all"
    heavy = int(os.environ.get("RHC_HEAVY_JOBS", "1"))
    entries = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    mods = {e["module"]: e for e in entries}
    bad = [e["path"] for e in entries
           if hashlib.sha256(Path(e["path"]).read_bytes()).hexdigest() != e["sha256"]]
    if bad:
        sys.exit("SHA-256 mismatch: " + ", ".join(bad))
    deps = {m: [d for d in imports(Path(e["path"])) if d in mods] for m, e in mods.items()}
    targets = stage_targets(stage, mods, deps)
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=f"{out}:{os.environ.get('LEAN_PATH', '')}")
    has_olean = lambda m: (out / (m.replace(".", "/") + ".olean")).exists()
    done, failed = set(mods) - targets, []
    missing = sorted({d for m in targets for d in deps[m] if d in done and not has_olean(d)})
    if missing:
        sys.exit(f"stage {stage}: missing .olean of earlier stages: {missing}")
    logs = {}
    if os.environ.get("RHC_RESUME") == "1":  # local restarts only; CI always builds from scratch
        done |= {m for m in targets if has_olean(m)}
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
                    if BATCH.match(m) and sum(bool(BATCH.match(r)) for r in running.values()) >= heavy:
                        continue
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

    log.write_text("".join(f"== {m}\n{logs.get(m, '')}" for m in mods if m in targets),
                   encoding="utf-8")
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
    print(f"stage {stage}: {len(targets)} modules compiled; {len(reports)} axiom reports, "
          f"all within {sorted(ALLOWED)}")
    if stage in ("all", "final"):
        named = {name for name, _ in reports}
        missing = [h for h in HEADLINE if h not in named]
        if missing:
            sys.exit(f"headline theorems not reported: {missing}")
        for h in HEADLINE:
            print(f"  {h}: OK")


if __name__ == "__main__":
    main()
