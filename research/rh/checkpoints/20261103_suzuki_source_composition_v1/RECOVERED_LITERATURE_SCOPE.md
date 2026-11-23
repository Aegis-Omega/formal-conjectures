# Later signed bounds: recovered source, finite scope

This is an additional primary-source recovery, not an RH proof and not
an independent validation of somebody else's numerical certificate.

R. A. Mittermeier, *A Zero-Side Positivity Certificate for Suzuki's
Screw Function through X = 2*10^29: Window Means and One-Sided
Criteria*, companion v2, 2026-10-21, DOI 10.5281/zenodo.23544568.
The earlier concept-record URL 10.5281/zenodo.23481974 resolved to
v2 metadata. The actual downloaded file identities are:

* PDF: 695101 bytes; SHA-256
  `3e1e5042de02808da11a956916a994ec2c769fd83067eca00e5ba02a0f26859c`.
* Reproduction ZIP: 69451 bytes; SHA-256
  `a2df7435fac43fc5af80c9b3aacfbf6655d041d7541785aa71f5bcb6fd23ba90`.

Both publisher MD5 values agree. ZIP CRC and all 42 entries of the
inner SHA-256 manifest were checked directly, without executing the
archive's programs. These checks establish byte identities only.

Read: Theorem 4.2 and its Landau argument; the README and claim ledger;
the finite-tail discussion in Section 6, including Proposition 6.6;
and `src/zero_density_tail.py`. The full certificate, the 3000 zero
intervals, the MPFR cell computations and the hypotheses of the external
zero-density theorem have NOT been independently replayed/audited here.

The source claims unconditional Psi(t)>0 for 0<t<=67.5, with separate
longer finite ranges for averages. Its claim ledger explicitly keeps
the infinite tail open. The full stated hypotheses include published
finite-height RH verification, explicit zero counts and zero-density
bounds. The source distinguishes those inputs from RH assumed at all
heights. These distinctions are retained, not collapsed into a boolean.

Theorem 4.2(ii) already allows a weaker-looking signed producer:
for every epsilon>0, an eventual bound

    Psi(t)>=-C_epsilon*exp(epsilon*t).

This is an existing sufficient theorem, not a new criterion discovered
here. Its proof adds a positive exponential and applies Landau's
one-sign Laplace theorem; no individual unknown zero is assumed real.
That arithmetic lower bound is not proved unconditionally in the paper.

The paper also explains why its finite-height numerical route cannot
by itself prove that producer. Its positive graded-tail envelope has
positive exponential rates (including a term with rate 1/2), whereas
the listed on-line-zero contribution is bounded. Increasing the list
at a fixed verified height does not remove that growth. This does not
prove that the actual omitted zero sum grows with that envelope: the
envelope has discarded cancellations. It only prevents using that
particular bound as the missing global sign proof.

The existing unconditional estimate
`abs(Psi(t)) <= C*exp(t/2-c*sqrt(t))` also fails to supply the displayed
producer for epsilon<1/2: the ratio of its envelope to exp(epsilon*t)
is `C*exp((1/2-epsilon)*t-c*sqrt(t))`, which diverges. This tests the
estimate, not the truth of the desired statement. The same exponential
loss was already recorded in the AEGIS arithmetic route; it is not a
new generic falsification or a reason to repeat finite certificates.

No arbitrary code from this archive was run and no new hundreds-of-
cells task was started. The recovered proof and exact source identities
are preserved for reuse when an actual global cancellation estimate
is available.
