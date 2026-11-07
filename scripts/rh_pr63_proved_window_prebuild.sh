#!/usr/bin/env bash
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
# Reuse PR606 exact import closure; compile the already-proved 693/2000 window
# into the same module search path without weakening the official RH target.
set -euo pipefail
ROOT="$(pwd)"
OUT="$1"
WINDOW_SHA="2c3d041b633147ec97c7ef753aa9d157a47bb9f5"
WBASE="$ROOT/.aegis-window/sovereign-omega-v2/formal/bridges/lean"
BASE="$ROOT/.aegis-base/sovereign-omega-v2/formal/bridges/lean"
SRC="$ROOT/AegisRH/PR606/Source"
COMPAT="$ROOT/AegisRH/PR606/Compat"
LOCAL="$ROOT/AegisRH/PR606"
if [[ -v RH_WINDOW_SRC_OVERRIDE ]]; then SRC="$RH_WINDOW_SRC_OVERRIDE"; fi
if [[ -v RH_WINDOW_COMPAT_OVERRIDE ]]; then COMPAT="$RH_WINDOW_COMPAT_OVERRIDE"; fi
OVERLAY="$ROOT/AEGISOverlay"
WIN="$ROOT/AegisRH/SmallWindow"
WORKTMP="/tmp"
if [[ -n "$RUNNER_TEMP" ]]; then WORKTMP="$RUNNER_TEMP"; fi
ORDER="$WORKTMP/rh-pr63-proved-window-closure.order"
AUDIT="$WORKTMP/rh-pr63-proved-window-axioms.lean"
LOG="$WORKTMP/rh-pr63-proved-window-axioms.log"
test "$(git -C "$ROOT/.aegis-window" rev-parse HEAD)" = "$WINDOW_SHA"
test -f "$OUT/RHRestrictedWeilCriterionV13.olean"
test -f "$WIN/RHSmallWindowCanonicalJoinV1.lean"
test -f "$OVERLAY/RHWindow693Over2000V1.lean"
mkdir -p "$OUT"

python3 - "$BASE" "$WBASE" "$SRC" "$COMPAT" "$LOCAL" "$OVERLAY" "$WIN" "$ORDER" "$OUT" <<'PY'
from pathlib import Path
import hashlib
import sys
base, wbase, src, compat, local, overlay, win, orderpath, out = map(Path, sys.argv[1:])
roots=(base, wbase, src, compat, local, overlay, win)
groups=[{p.stem:p for p in r.glob("*.lean")} for r in roots]
allmods=set().union(*(set(g) for g in groups))
def chosen(n):
    # PR606 fork closure selects Compat before Source.  The proved-window
    # replay must not silently shadow the same theorem with a different LOCAL
    # proof body: reuse the exact source-locked PR606 compatibility module.
    if n == "WeilZeroTwoPointV11":
        source = compat / (n + ".lean")
        if not source.is_file():
            raise SystemExit("RH_WINDOW_TWO_POINT_COMPAT_MISSING")
        payload = source.read_bytes()
        blob = hashlib.sha1(f"blob {len(payload)}\\0".encode() + payload).hexdigest()
        if blob != "416eb252794a2b0b550c796330a08a946aeabed4":
            raise SystemExit("RH_WINDOW_TWO_POINT_COMPAT_SOURCE_DRIFT:" + blob)
        return source
    for group in reversed(groups):
        if n in group: return group[n]
    raise SystemExit(f"RH_WINDOW_SOURCE_MISSING:{n}")
done=set()
active=set()
order=[]
def visit(n):
    if n in done: return
    if n in active: raise SystemExit(f"RH_WINDOW_IMPORT_CYCLE:{n}")
    active.add(n)
    for ln in chosen(n).read_text(encoding="utf-8").splitlines():
        ln=ln.split("--",1)[0].strip()
        if not ln.startswith("import "): continue
        for dep in ln[7:].split():
            if dep in allmods:
                visit(dep)
            elif dep.startswith("AEGISOverlay.") and dep.split(".",1)[1] in allmods:
                visit(dep.split(".",1)[1])
            elif dep.split(".")[0] in {"Mathlib", "Lean", "Std", "Aesop", "Batteries", "Qq", "Lc", "Hadamard", "FormalConjectures"}:
                continue
            elif dep.split(".")[0] in allmods:
                visit(dep.split(".")[0])
            else:
                raise SystemExit(f"RH_WINDOW_IMPORT_UNRESOLVED:{n}:{dep}")
    active.remove(n)
    done.add(n)
    order.append(n)
visit("RHSmallWindowCanonicalJoinV1")
# A cached .olean is safe only with a matching source stamp. Rebuild all later
# modules in topological order after the first dirty source (conservative
# dependency invalidation, including modules restored from older CI caches).
pending=[]
dirty=False
for n in order:
    source=chosen(n)
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    olean=out / (n+".olean")
    stamp=out / (n+".source.sha256")
    olean_stamp=out / (n+".olean.sha256")
    valid=(olean.is_file() and olean.stat().st_size>0 and stamp.is_file()
           and stamp.read_text(encoding="ascii").strip()==digest
           and olean_stamp.is_file()
           and olean_stamp.read_text(encoding="ascii").strip()
             == hashlib.sha256(olean.read_bytes()).hexdigest())
    if dirty or not valid:
        dirty=True
        pending.append((n,source,digest))
orderpath.write_text("\n".join(f"{n}\t{p}\t{digest}" for n,p,digest in pending)+"\n",encoding="utf-8")
Path(str(orderpath)+".all.tsv").write_text(
    "\n".join(f"{n}\t{chosen(n)}\t{hashlib.sha256(chosen(n).read_bytes()).hexdigest()}" for n in order)+"\n",
    encoding="utf-8")
print(f"RH_PROVED_WINDOW_BUILD_COUNT={len(pending)}")
print(f"RH_PROVED_WINDOW_CACHE_VERIFIED_COUNT={len(order)-len(pending)}")
for n,p,digest in pending: print("RH_PROVED_WINDOW_SOURCE",n,str(p),digest)
PY
BASE_LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$OUT:$WIN:$OVERLAY:$LOCAL:$COMPAT:$SRC:$WBASE:$BASE:$ROOT/.li/.lake/build/lib/lean:$BASE_LEAN_PATH"
while IFS="$(printf '\t')" read -r name file digest; do
    test -n "$name" || continue
    test -n "$digest"
    echo "RH_PROVED_WINDOW_COMPILE $name $file"
    actual="$(sha256sum "$file" | cut -d ' ' -f 1)"
    if [ "$actual" != "$digest" ]; then
        echo "RH_WINDOW_SOURCE_CHANGED_DURING_BUILD:$name" >&2
        exit 1
    fi
    rm -f "$OUT/$name.olean" "$OUT/$name.source.sha256" "$OUT/$name.olean.sha256"
    lean -o "$OUT/$name.olean" "$file"
    test -s "$OUT/$name.olean"
    printf '%s\n' "$digest" > "$OUT/$name.source.sha256"
    sha256sum "$OUT/$name.olean" | awk '{print $1}' > "$OUT/$name.olean.sha256"
done < "$ORDER"

cat > "$AUDIT" <<'LEAN'
import RHSmallWindowCanonicalJoinV1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.window_one_over_64_of_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.universal_zero_quadratic_of_above_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.riemannHypothesis_of_above_693_over_2000_v1
LEAN
lean "$AUDIT" > "$LOG" 2>&1
python3 "$ROOT/scripts/verify_rh_overlay_axioms.py" "$AUDIT" "$LOG"
# A checkpoint is valid only after the complete closure and terminal axiom audit.
python3 - "$ORDER.all.tsv" "$OUT" "$ROOT" "$WINDOW_SHA" <<'PY'
import hashlib, json, pathlib, subprocess, sys
orderfile, out, root = map(pathlib.Path, sys.argv[1:4])
window_sha = sys.argv[4]
records = []
for line in orderfile.read_text(encoding="utf-8").splitlines():
    module, source_str, source_sha = line.split("\t")
    source = pathlib.Path(source_str)
    olean = out / (module + ".olean")
    src_stamp = out / (module + ".source.sha256")
    bin_stamp = out / (module + ".olean.sha256")
    if not all(p.is_file() for p in (source, olean, src_stamp, bin_stamp)):
        raise SystemExit("RH_WINDOW_CHECKPOINT_MISSING:" + module)
    actual_source = hashlib.sha256(source.read_bytes()).hexdigest()
    actual_olean = hashlib.sha256(olean.read_bytes()).hexdigest()
    if (not olean.stat().st_size or actual_source != source_sha
        or src_stamp.read_text().strip() != source_sha
        or bin_stamp.read_text().strip() != actual_olean):
        raise SystemExit("RH_WINDOW_CHECKPOINT_DRIFT:" + module)
    records.append({"module": module,
        "source": str(source.relative_to(root)),
        "source_sha256": source_sha, "olean_sha256": actual_olean,
        "olean": str(olean.relative_to(root))})
if not records or len({r["module"] for r in records}) != len(records):
    raise SystemExit("RH_WINDOW_CHECKPOINT_INCOMPLETE")
receipt = {"schema": "aegis.rh.window_olean_checkpoint.v1",
           "head": subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),
           "window_provider_head": window_sha,
           "module_count": len(records), "modules": records,
           "terminal_axioms": "ALL_STANDARD_AXIOMS_ONLY",
           "rh_unconditional": None, "admission": "OPEN"}
target = out / "rh-proved-window-checkpoint-v1.json"
target.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8")
print("RH_PROVED_WINDOW_ALL_OLEANS_SOURCE_BOUND",len(records))
print("RH_PROVED_WINDOW_CHECKPOINT",target)
PY
echo 'RH_PROVED_WINDOW_IMPORT=PASS; LARGE_WINDOW_PREMISE=NOT_ASSUMED'
