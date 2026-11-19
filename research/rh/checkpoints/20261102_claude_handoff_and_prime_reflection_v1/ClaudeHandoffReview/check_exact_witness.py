"""Independent direct-arithmetic evaluation of an exact clamped polynomial witness.

No eigenproblem, qwhp import, Legendre matrix, pickle cache, or float decision.
Its analytic meaning is proved in DIRECT_WITNESS_SOUNDNESS.md, not in Lean.
"""
from pathlib import Path
from math import factorial, isqrt
import hashlib
import json
import re
import sys
import time
import argparse
import flint
from flint import arb, acb, ctx, fmpq, fmpq_poly

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result

def rational(pair):
    require(isinstance(pair, list) and len(pair) == 2, "rational pair required")
    require(all(isinstance(s, str) and re.fullmatch(r"-?\d{1,20000}", s) for s in pair),
            "invalid integer representation")
    require(int(pair[1]) > 0, "positive denominator required")
    return fmpq(int(pair[0]), int(pair[1]))

def polynomial(items):
    require(isinstance(items, list) and 1 <= len(items) <= 81, "polynomial degree outside checked resource scope")
    return fmpq_poly([rational(x) for x in items])

def ball(x):
    return arb(x.p) / x.q

def evaluate(poly, z):
    value = acb(0) if isinstance(z, acb) else arb(0)
    for i in range(poly.degree(), -1, -1):
        value = value * z + ball(poly[i])
    return value

def prime_power_base(n):
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            remainder = n
            while remainder % p == 0:
                remainder //= p
            return p if remainder == 1 else None
    return n

def main():
    start = time.monotonic()
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--panels', type=int, default=1)
    args = parser.parse_args()
    require(1 <= args.panels <= 1024, "integration partition outside resource scope")
    source, output = args.source, args.output
    require(not output.exists(), "refusing to overwrite a receipt")
    raw = source.read_bytes()
    data = json.loads(raw, object_pairs_hook=unique_object)
    require(data.get("schema") == "AEGIS_EXACT_POLYNOMIAL_RAYLEIGH_WITNESS_V1", "unsupported schema")
    require(data.get("variable") == "y=x/a" and data.get("operator") == "1/4 - d2/dx2", "normalization mismatch")
    a = rational(data["a"])
    require(0 < a <= fmpq(3, 2), "radius outside checked resource scope")
    psi = polynomial(data["potential"])
    v = polynomial(data["trial"])
    require(v != 0, "zero witness")
    require(v == psi / 4 - psi.derivative().derivative() / (a * a), "exact differential identity fails")
    require(all(psi(x) == 0 and psi.derivative()(x) == 0 for x in (fmpq(-1), fmpq(1))),
            "clamped endpoint conditions fail")
    norm_primitive = (v * v).integral()
    exact_norm = a * (norm_primitive(fmpq(1)) - norm_primitive(fmpq(-1)))
    require(exact_norm > 0 and exact_norm == rational(data["exact_norm_squared"]), "exact norm mismatch")

    # Direct Taylor/antiderivative correlation, independent of the Legendre table.
    t = fmpq_poly([0, 1]); endpoint = fmpq_poly([1, -1])
    correlation = fmpq_poly([0]); derivative = v
    for k in range(v.degree() + 1):
        primitive = (v * derivative).integral()
        correlation += (primitive(endpoint) - primitive(fmpq(-1))) * (t ** k) / factorial(k)
        derivative = derivative.derivative()
    require(a * correlation[0] == exact_norm, "correlation norm identity fails")
    require(correlation(fmpq(2)) == 0, "correlation support endpoint fails")
    regularized = fmpq_poly([correlation[i] for i in range(1, correlation.degree() + 1)])

    ctx.prec = 800
    A = ball(a); E = ball(exact_norm); I = acb(0, 1)
    exponential_cutoff = (2 * A).exp()
    floor_ball = exponential_cutoff.floor()
    cutoff_integer = floor_ball.unique_fmpz()
    require(cutoff_integer is not None, "prime cutoff not isolated")
    cutoff = int(cutoff_integer)
    require(arb(cutoff) < exponential_cutoff and exponential_cutoff < arb(cutoff + 1),
            "prime cutoff interval touches an integer")
    settings = dict(rel_tol=arb(2) ** -700, abs_tol=arb(2) ** -700,
                    deg_limit=100, eval_limit=100000, depth_limit=40, use_heap=True)
    def integrate(callback, end):
        # Adjacent exact-rational panel endpoints cover the full segment.
        return sum((acb.integral(callback, end * j / args.panels,
                                 end * (j + 1) / args.panels, **settings)
                    for j in range(args.panels)), acb(0))
    first = integrate(lambda z, analytic:
                      evaluate(regularized, z) * (A * z / 2).exp() / (I * A * z).sinc(),
                      arb(2))
    nu = integrate(lambda z, analytic:
                   (z / 4).exp() * (I * z / 4).sinc() / (4 * (I * z).sinc()),
                   2 * A)
    require(first.is_finite() and nu.is_finite() and first.imag.contains(0) and nu.imag.contains(0),
            "nonfinite or inconsistent analytic integral")
    prime = arb(0); indices = []; prime_terms = []
    for n in range(2, cutoff + 1):
        p = prime_power_base(n)
        if p is not None:
            indices.append(n)
            term = 2 * A * arb(p).log() / arb(n).sqrt() * evaluate(correlation, arb(n).log() / A)
            prime += term
            prime_terms.append(dict(n=n, base=p, normalized_contribution=(term/E).str(50)))
    constant = (4 * arb.pi()).log() + arb.const_euler() + A.tanh().log()
    Q = -constant * E - A * first.real - 2 * E * nu.real - prime
    quotient = Q / E
    require(quotient.is_finite(), "nonfinite Rayleigh quotient")

    # This endpoint is exact dyadic data; the final rational is explicitly rounded UP.
    upper = quotient.upper().fmpq()
    scale = 10 ** 80
    numerator = (int(upper.p) * scale + int(upper.q) - 1) // int(upper.q) + 1
    safe_upper = fmpq(numerator, scale)
    require(upper < safe_upper and quotient < ball(safe_upper), "directed upper bound fails")
    report = dict(schema="AEGIS_DIRECT_ARB_WITNESS_RECEIPT_V1",
                  input_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  python_flint=flint.__version__, arb_precision=ctx.prec,
                  integration=dict(rel_tol="2^-700", abs_tol="2^-700", deg_limit=100,
                                   eval_limit=100000, depth_limit=40, use_heap=True,
                                   panels=args.panels, regularized_integral_ball=first.str(40),
                                   nu_integral_ball=nu.str(40),
                                   integrands="meromorphic with removable zero already cancelled"),
                  exact_polynomial_boundary_and_norm_checks=True,
                  prime_cutoff_certified_integer=cutoff, prime_power_indices=indices,
                  exact_norm_squared=[str(exact_norm.p), str(exact_norm.q)],
                  normalized_archimedean=((-constant*E-A*first.real-2*E*nu.real)/E).str(60),
                  normalized_prime_sum=(prime/E).str(60), prime_terms=prime_terms,
                  quotient_ball=quotient.str(80),
                  exact_dyadic_upper=[str(upper.p), str(upper.q)],
                  rigorous_rational_upper=[str(safe_upper.p), str(safe_upper.q)],
                  seconds=time.monotonic()-start,
                  mathematical_scope="upper bound for the exact two-moment Rayleigh infimum only",
                  methods_not_used=["eigenproblem", "Legendre matrix", "pickle", "float decisions"],
                  analytic_soundness="ordinary proof; no Lean soundness term",
                  lean_kernel_run=False, rh_proven=False)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
