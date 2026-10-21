"""Compile source-exact moment-augmented fixed-window theorem; fail closed on axes."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path.cwd()
source = root / "research/rh/checkpoints/20261020_row_budget_bridge/CvSMomentWindowBridgeV1.lean"
target = root / ".lake/ringout/CvSMomentWindowBridgeV1.olean"
names = (
    "admissible_augmented_orthogonal",
    "window_nonneg_of_augmented_trace",
    "window_of_certificate_augmented_trace",
    "actualTraceBasis_continuous",
)
expected = {"AEGIS.CvSMomentWindowBridgeV1." + name for name in names}
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
command = ["lean", "-DwarningAsError=true", "-o", str(target), str(source)]
started = time.monotonic()

def output(args):
    return subprocess.check_output(args, text=True).strip()

receipt = {
    "repository": "tarikskalic33/formal-conjectures",
    "scope": "Finite low-block and original cross/Schur bounds are unchanged. "
             "Only the trial-distance trace has two additional exponential moments. "
             "Pointwise Krein certificate and augmented trace integral remain premises. "
             "Not an unconditional Riemann Hypothesis theorem.",
    "required_roots": sorted(expected),
    "allowed_axioms": sorted(allowed_axioms),
    "command": command,
    "status": "FAIL",
}
try:
    receipt["commit"] = output(["git", "rev-parse", "HEAD"])
    receipt["lean"] = output(["lean", "--version"])
    receipt["mathlib"] = output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"])
    receipt["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    receipt["source_blob"] = output(["git", "hash-object", str(source)])
    if receipt["mathlib"] != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise RuntimeError("MATHLIB_PIN_MISMATCH")
    if "4.33.1" not in receipt["lean"]:
        raise RuntimeError("LEAN_PIN_MISMATCH")
    if re.search(r"\b(?:sorry|sorryAx|admit)\b", source.read_text()):
        raise RuntimeError("FORBIDDEN_SOURCE_PLACEHOLDER")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.unlink(missing_ok=True)  # Invalidate this new candidate only; never touch green binaries.
    run = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    compiler_output = run.stdout
    (root / "moment-window-replay.log").write_text(compiler_output)
    receipt["exit_code"] = run.returncode
    receipt["compiler_output"] = compiler_output
    audits = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", compiler_output):
        if name in audits:
            raise RuntimeError("DUPLICATE_AXIOM_ROOT:" + name)
        audits[name] = [item.strip() for item in axioms.split(",") if item.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", compiler_output):
        if name in audits:
            raise RuntimeError("DUPLICATE_AXIOM_ROOT:" + name)
        audits[name] = []
    receipt["axiom_audits"] = audits
    receipt["missing_roots"] = sorted(expected - audits.keys())
    receipt["extra_roots"] = sorted(audits.keys() - expected)
    receipt["unexpected_axioms"] = sorted({ax for axs in audits.values()
                                           for ax in axs if ax not in allowed_axioms})
    valid = (run.returncode == 0 and audits.keys() == expected and
             all(set(axs) <= allowed_axioms for axs in audits.values()) and
             target.is_file() and target.stat().st_size > 0)
    if valid:
        receipt["binary_sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
        receipt["status"] = "PASS"
except Exception as error:
    receipt["failure"] = type(error).__name__ + ":" + str(error)
finally:
    receipt["seconds"] = time.monotonic() - started
    (root / "MOMENT_WINDOW_KERNEL_RECEIPT.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    )
    print(receipt.get("compiler_output", ""))
    print("MOMENT_WINDOW_KERNEL_" + receipt["status"],
          len(receipt.get("axiom_audits", {})), "audits")
raise SystemExit(0 if receipt["status"] == "PASS" else 1)
