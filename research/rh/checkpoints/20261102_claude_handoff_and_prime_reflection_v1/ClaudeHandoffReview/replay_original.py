"""Replay the pinned original in an empty cache directory; save its exact witness.
No claim that the original formatting is a directed rational upper bound.
"""
from pathlib import Path
import hashlib
import json
import runpy
import shutil
import sys
import time
import argparse
import flint
from flint import arb, fmpq, fmpq_poly, ctx

root = Path(__file__).parent
parser = argparse.ArgumentParser()
parser.add_argument("a_num", type=int)
parser.add_argument("a_den", type=int)
args = parser.parse_args()
if (args.a_num, args.a_den) not in ((3, 4), (1, 1), (5, 4), (3, 2)):
    raise ValueError("not one of the pinned handoff replay inputs")
out = root / f"replay_a{args.a_num}_{args.a_den}_K40"
out.mkdir(exist_ok=False)
sources = [
    (root / "certify.py", "facfaa4990b6b0339adee5c291ddf4278ad5af67ddfaf2afedc6717c5e569cc9"),
    (root / "qwhp.py", None),
]
identities = []
for src, expected in sources:
    data = src.read_bytes()
    sha = hashlib.sha256(data).hexdigest()
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if expected is not None and sha != expected:
        raise ValueError("source digest mismatch")
    if src.name == "qwhp.py" and blob != "ca36a73b8a8fa8078a1b7d7a0e3736d1b05b94fa":
        raise ValueError("qwhp source blob mismatch")
    shutil.copyfile(src, out / src.name)
    identities.append(dict(file=src.name, sha256=sha, git_blob=blob))
import os
os.chdir(out)
sys.path.insert(0, str(out))
sys.argv = [str(out / "certify.py"), str(args.a_num), str(args.a_den), "40"]
start = time.monotonic()
g = runpy.run_path(str(out / "certify.py"))
R = g["R"]
if not R.is_finite() or not g["den"] > 0:
    raise ValueError("nonfinite quotient or nonpositive norm")
for moment in (g["m1"], g["m2"]):
    if not moment.contains(0):
        raise ValueError("reported moment enclosure excludes zero")
psi = sum((g["dq"][k] * g["bump"] * g["P"][k] for k in range(g["K"])), fmpq_poly([0]))
v = sum((g["c"][j] * g["P"][j] for j in range(g["N"])), fmpq_poly([0]))
if v != psi * fmpq(1, 4) - psi.derivative().derivative() / (g["aq"] ** 2):
    raise ValueError("exact differential identity mismatch")
if any(psi(x) != 0 or psi.derivative()(x) != 0 for x in (fmpq(-1), fmpq(1))):
    raise ValueError("potential boundary conditions fail")
if v == 0:
    raise ValueError("zero trial witness")
norm_poly = (v * v).integral()
norm = g["aq"] * (norm_poly(fmpq(1)) - norm_poly(fmpq(-1)))
if norm <= 0:
    raise ValueError("nonpositive exact norm")
def rat(x):
    return [str(x.p), str(x.q)]
def coeffs(p):
    return [rat(p[i]) for i in range(p.degree() + 1)]
witness = dict(schema="AEGIS_EXACT_POLYNOMIAL_RAYLEIGH_WITNESS_V1", a=rat(g["aq"]),
               variable="y=x/a", operator="1/4 - d2/dx2", potential=coeffs(psi),
               trial=coeffs(v), exact_norm_squared=rat(norm),
               source_identities=identities, rh_proven=False)
(out / "EXACT_WITNESS.json").write_text(json.dumps(witness, indent=2) + "\n")
s = R.upper().str(6, radius=False)
report = dict(schema="AEGIS_ORIGINAL_ARB_REPLAY_V1", seconds=time.monotonic()-start,
              python_flint=flint.__version__, arb_precision=ctx.prec,
              source_identities=identities, inputs=dict(a=f"{args.a_num}/{args.a_den}", K=40),
              quotient_ball=R.str(70), original_formatted_upper=s,
              formatted_upper_below_trial_ball=bool(arb(s) < R),
              exact_potential_and_moments_checked=True,
              exact_norm_squared=rat(norm),
              finite_prime_indices=[n for n, _ in g["primes"]],
              independent_direct_evaluation="PENDING", lean_kernel_run=False, rh_proven=False)
(out / "ORIGINAL_REPLAY_RECEIPT.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2), flush=True)
