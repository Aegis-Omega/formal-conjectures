"""Independent diagnostic of the recovered Coq -> PR523 prime identity.

The ordinary proof is ACTUAL_PRIME_SOURCE_COMPOSITION.md. These finite
high-precision quadratures detect sign/scale/complex-carrier errors; they
are NOT a rigorous enclosure, kernel replay, or universal sign proof.
No historical program is imported or executed.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

ROOT = Path('/workspace/aegis-nov3-proof-attempt')
SRC = Path('/workspace/aegis-nov3-history-intake/source')
mp.mp.dps = 80


def check(ok, label):
    if not ok:
        raise RuntimeError(label)


def mpf(q):
    return mp.mpf(q.numerator) / q.denominator


def prime_base(q):
    """Exact von Mangoldt support, by integer trial division."""
    n = q
    for p in range(2, q + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return p if n == 1 else None
    raise RuntimeError('invalid q')


def run():
    source_files = [
        SRC / '02dba9c7dbff4e1b904231499e6b6ba0c4bac0d0.v',
        SRC / 'e66051154a36132b4f2c828f8babe69764860cca.v',
        Path('/workspace/aegis-nov2/FiniteSource523/WeilFiniteSourceCalculusV1.lean'),
    ]
    sources = []
    for p in source_files:
        data = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if p.parent == SRC:
            check(blob == p.stem, 'historical Git source identity')
        sources.append(dict(path=str(p), bytes=len(data), git_blob=blob,
                            sha256=hashlib.sha256(data).hexdigest()))

    # Three genuinely different complex actual CvS atom coefficients.
    atoms = {-1: (F(1), F(2)), 0: (F(-3, 2), F(1, 3)),
             1: (F(2, 5), F(-7, 4))}
    beta = {m: [F(0), F(0)] for m in range(-2, 3)}
    for n, coeff in atoms.items():
        for m, a in [(n, F(1, 2)), (n-1, F(-1, 4)), (n+1, F(-1, 4))]:
            for k in range(2):
                beta[m][k] += a * coeff[k]
    for k in range(2):
        check(sum(v[k] for v in beta.values()) == 0, 'clamped value')
        check(sum(m*v[k] for m, v in beta.items()) == 0, 'clamped derivative')

    cases = []
    for Lq, qs in [(F(3, 2), list(range(2, 5))),
                  (F(5, 2), list(range(2, 13)))]:
        L = mpf(Lq)
        coeff = {m: -((2*mp.pi*m/L)**2 + mp.mpf(1)/4)
                 * mp.mpc(mpf(v[0]), mpf(v[1])) for m, v in beta.items()}
        def h(x):
            return mp.fsum(c*mp.exp(2j*mp.pi*m*x/L) for m, c in coeff.items())
        for q in qs:
            ell = mp.log(q)
            check(ell < L, 'explicit active prime range')
            p = prime_base(q)
            lam = mp.log(p) if p else mp.mpf(0)
            alpha, omega = -lam/mp.sqrt(q), 1-ell/L
            # Direct physical-space compact overlap, no source entry formula.
            corr = mp.quad(lambda x: h(x+ell)*mp.conj(h(x)), [0, L-ell])
            physical = -2*lam/mp.sqrt(q)*mp.re(corr)
            def entry(m, n):
                def source(x):
                    return alpha/mp.pi*mp.sin(2*mp.pi*omega*x)
                return (mp.diff(source, m) if m == n else
                        (source(m)-source(n))/(m-n))
            source_value = L*mp.fsum(
                (mp.re(cm)*mp.re(cn)+mp.im(cm)*mp.im(cn))*entry(m,n)
                for m,cm in coeff.items() for n,cn in coeff.items())
            error = abs(physical-source_value)
            check(error < mp.mpf('1e-60'), 'source/physical prime identity diagnostic')
            cases.append(dict(L=str(Lq), q=q, prime_base=p,
                              abs_error=mp.nstr(error, 8),
                              physical_value=mp.nstr(physical, 35)))

    # This exact small geometry refutes the specified universal sparse
    # reconstruction premise, not RH or its certified local sparse theorem.
    same_atom_impossible = F(1, 64) > F(2, 256)
    different_atoms_impossible = F(65,32) > F(3,128)
    check(same_atom_impossible and different_atoms_impossible,
          'sparse two-point geometry')

    result = dict(schema='AEGIS_RECOVERED_PRIME_JOIN_DIAGNOSTIC_V1',
                  status='FINITE_QUADRATURE_DIAGNOSTIC_PASS',
                  precision_decimal_digits=80,
                  exact_rational_clamping_checked=True,
                  sources=sources, cases=cases,
                  kernel_replay='NOT_RUN',
                  rigorous_interval_certificate=False,
                  full_form_sign_proved=False, rh_proven=False)
    target = ROOT / 'integration' / 'PRIME_JOIN_DIAGNOSTIC.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'], cases=len(cases),
                          receipt=str(target), rh_proven=False)))


if __name__ == '__main__':
    run()
