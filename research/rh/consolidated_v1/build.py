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
import shutil
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


def sha256_file(path: Path) -> str:
    """Hash large kernel binaries with bounded memory, not read_bytes()."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def verified_olean(out: Path, module: str, source_sha: str, context_sha: str) -> bool:
    """Accept an object only if bytes, source identity and build context match."""
    olean = out / (module.replace(".", "/") + ".olean")
    digest_file = Path(str(olean) + ".sha256")
    source_file = Path(str(olean) + ".source.sha256")
    context_file = Path(str(olean) + ".context.sha256")
    return (olean.is_file() and olean.stat().st_size > 0
            and digest_file.is_file() and source_file.is_file()
            and context_file.is_file()
            and source_file.read_text().strip() == source_sha
            and context_file.read_text().strip() == context_sha
            and digest_file.read_text().strip()
                == sha256_file(olean))


def resumable_modules(mods, deps, has_olean):
    """Admit only transitive, source-identical cached import closures."""
    trusted = set()
    remaining = set(mods)
    while remaining:
        newly_trusted = {
            m for m in remaining
            if has_olean(m) and all(d in trusted for d in deps[m])
        }
        if not newly_trusted:
            break
        trusted.update(newly_trusted)
        remaining.difference_update(newly_trusted)
    return trusted


def missing_upstream_oleans(mods, deps, targets, has_olean):
    """Identify stage imports whose transitive prerequisite closures are not valid."""
    done = set(mods) - set(targets)
    prior_deps = {m: [d for d in deps[m] if d in done] for m in done}
    trusted_prior = resumable_modules(done, prior_deps, has_olean)
    required_prior = {d for m in targets for d in deps[m] if d in done}
    return sorted(required_prior - trusted_prior)


def main():
    out, log = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    stage = sys.argv[4] if len(sys.argv) > 4 else "all"
    heavy = int(os.environ.get("RHC_HEAVY_JOBS", "1"))
    entries = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    mods = {e["module"]: e for e in entries}
    if len(mods) != len(entries):
        sys.exit("RHC_DUPLICATE_MANIFEST_MODULE")
    bad = [e["path"] for e in entries
           if hashlib.sha256(Path(e["path"]).read_bytes()).hexdigest() != e["sha256"]]
    if bad:
        sys.exit("SHA-256 mismatch: " + ", ".join(bad))
    deps = {m: [d for d in imports(Path(e["path"])) if d in mods] for m, e in mods.items()}
    targets = stage_targets(stage, mods, deps)
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=f"{out}:{os.environ.get('LEAN_PATH', '')}")
    # Match the exact Lean/Mathlib/provider environment across independent jobs.
    # An .olean checksum by itself cannot prove that its imports are compatible.
    context_sha = hashlib.sha256(
        Path("lean-toolchain").read_bytes()
        + Path("lake-manifest.json").read_bytes()
        + (HERE / "li-provider.patch").read_bytes()
        + os.environ.get("LI_PROVIDER_SHA", "").encode()
    ).hexdigest()
    def has_olean(m):
        return verified_olean(out, m, mods[m]["sha256"], context_sha)
    done, failed = set(mods) - targets, []
    # A direct import is unsafe if a transitive upstream .olean has drifted.
    missing = missing_upstream_oleans(mods, deps, targets, has_olean)
    if missing:
        sys.exit(f"stage {stage}: stale or missing transitive .olean closure: {missing}")
    logs = {}
    if os.environ.get("RHC_RESUME") == "1":  # local restarts only; CI always builds from scratch
        # A changed earlier dependency invalidates all transitive dependents,
        # even when their own source and object bytes still match old stamps.
        done |= resumable_modules(mods, deps, has_olean) & targets
    started = set(done)

    def compile_one(m):
        e = mods[m]
        rel = m.replace(".", "/") + ".lean"
        assert e["path"].endswith(rel), (m, e["path"])
        root = e["path"][: -len(rel)] or "."
        olean = out / (m.replace(".", "/") + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        stamp = Path(str(olean) + ".sha256")
        source_stamp = Path(str(olean) + ".source.sha256")
        context_stamp = Path(str(olean) + ".context.sha256")
        for artifact in (olean, stamp, source_stamp, context_stamp):
            artifact.unlink(missing_ok=True)
        t = time.time()
        r = subprocess.run(["lean", "-R", root, "-o", str(olean), e["path"]],
                           env=env, capture_output=True, text=True)
        success = r.returncode == 0 and olean.is_file() and olean.stat().st_size > 0
        if success:
            stamp.write_text(sha256_file(olean) + "\n")
            source_stamp.write_text(e["sha256"] + "\n")
            context_stamp.write_text(context_sha + "\n")
        else:
            for artifact in (olean, stamp, source_stamp, context_stamp):
                artifact.unlink(missing_ok=True)
        return (m, 0 if success else r.returncode or 1,
                r.stdout + r.stderr + ("" if success else "\nMISSING_OR_FAILED_OLEAN " + m),
                time.time() - t)

    with cf.ThreadPoolExecutor(jobs) as ex:
        running = {}
        while len(done) < len(mods) and not failed:
            for m in mods:
                if m not in started and all(d in done for d in deps[m]):
                    if BATCH.match(m) and sum(bool(BATCH.match(r)) for r in running.values()) >= heavy:
                        continue
                    started.add(m)
                    running[ex.submit(compile_one, m)] = m
            if not running:
                blocked = sorted(set(mods) - done)
                sys.exit("RHC_IMPORT_DAG_STALLED: " + ", ".join(blocked))
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

    # Source and binary integrity must hold for EVERY module claimed by this stage.
    # Imported stages have their own checkpoint and .olean SHA-256 sidecars.
    for m in targets:
        if not has_olean(m):
            sys.exit("MISSING_OR_HASH_DRIFT_OLEAN " + m)
    records = []
    for m, e in mods.items():
        if has_olean(m):
            olean = out / (m.replace(".", "/") + ".olean")
            records.append({
                "module": m, "source": e["path"], "source_sha256": e["sha256"],
                "olean": str(olean.relative_to(out)),
                "olean_sha256": Path(str(olean) + ".sha256").read_text().strip()
            })
    if stage in ("all", "final") and len(records) != len(mods):
        sys.exit(f"RHC_CHECKPOINT_INCOMPLETE {len(records)}/{len(mods)}")
    stage_name = stage.replace(":", "-").replace("/", "-")
    receipt = {
        "schema": "aegis.rh.consolidated_olean_checkpoint.v1",
        "stage": stage, "module_count": len(records),
        "manifest_source_sha256": hashlib.sha256((HERE / "manifest.json").read_bytes()).hexdigest(),
        "lean_toolchain": Path("lean-toolchain").read_text().strip(),
        "mathlib_sha": os.environ.get("MATHLIB_SHA"),
        "build_context_sha256": context_sha,
        "modules": records, "rh_unconditional": None,
        "axiom_admission": "HEADLINE_PROBES_ONLY" if stage in ("all", "final") else "NOT_ASSESSED"
    }
    checkpoint = out / ("rhc-checkpoint-" + stage_name + ".json")
    checkpoint.write_text(json.dumps(receipt, indent=2) + "\n")
    if stage == "final":
        final_dir = out / "rhc-final"
        final_dir.mkdir(exist_ok=True)
        for m in targets:
            rel = Path(m.replace(".", "/") + ".olean")
            dest = final_dir / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(out / rel, dest)
            for suffix in (".sha256", ".source.sha256", ".context.sha256"):
                shutil.copyfile(Path(str(out / rel) + suffix),
                                Path(str(dest) + suffix))
        shutil.copyfile(checkpoint, final_dir / "rhc-checkpoint-final.json")
    print("RHC_ALL_STAGE_OLEANS_CHECKPOINTED", stage, len(records), "/", len(mods))


if __name__ == "__main__":
    main()
