# Independent review of the direct eleven-window composition

2026-11-03. Verdict: no mathematical error found. The direct argument
correctly removes the polarization factor2 on the stated independent-shape
family and proves the written margin1203957/1136000. This is an ordinary
mathematical/source review, not a compilation or axiom audit of a new
actual-B Lean adapter. The previous weaker composition remains valid.

## Actual support and reciprocal normalization

For i<j, let p=T_i u and q=T_j v, with fine centers a+s_i,a+s_j and
d=s_j-s_i. Each half-width is1/256, so the support of the actual
`logCrossV28 p q` is contained in

    [-d-1/128,-d+1/128].

The orientation is first-support minus second-support. It is not the
positive interval centered at d. Since d>=log(33/16)>log2>1/128,
every forward integer sample, including the center sample at1, is zero.
For a reciprocal sample, the necessary condition is precisely
`abs(log(m)-d)<=1/128`.

The existing identity C(t)=exp(t/2)mixed(p,q,exp(t)) gives

    C(-log m)=m^(-1/2)mixed(p,q,1/m),
    (1/m)mixed(p,q,1/m)=m^(-1/2)C(-log m).

Thus the coefficient charged by the von Mangoldt sum is
Lambda(m)/sqrt(m). No reciprocal factor, square root, or factor2 is
missing. The existing generic distinct-packet mean theorem bounds
the correlation by(E(u)+E(v))/2, because the actual half-density
translations preserve both individual energies.

## The old arithmetic certificates really are shape-independent

The three `.lean.src` bytes have exactly the advertised Git blobs:
7175f243640df980d9c2effc610cbb6748ffc29b,
6f0ce19532bb422649d764a0bea930e3756a8c59,
c1771ca493a3292d962b77332437c2de3a693ac2.

Their scalar arithmetic was also reviewed separately by the actual
tool-spawned agent `/root/analytic_audit/direct_eleven_prime_windows`,
which read the statements/proofs and checked rational envelopes and
integer factorizations without executing archived code.

For gaps1--8, the declarations quantify only over positive m and the
inclusive logarithmic-window condition. They contain no mother-packet
assumption. Their candidate sets are empty for gaps1,2,3,5; otherwise
they are{18},{77},{158,159,160},{325,...,330}, all excluded as prime
powers by the source's exact von Mangoldt arguments.

Gap9 has precisely the possible integers671--680; all except673,677
have zero von Mangoldt value. In particular676 is not a prime power.
Both remaining primes are>=25^2 and have log(m)<7, so each costs at
most7/25. Gap10 has precisely1383--1403; only1399 survives, with
1399>=37^2 and log1399<8, giving8/37. The envelope's strict upper
endpoint and inclusive original log condition cause no boundary loss.

The archived complete prime-sum theorems themselves are same-mother
statements. The new argument does not apply those declarations to
different mothers. It reuses their independent integer arithmetic,
scalar bounds and the generic support/correlation theorem. This
distinction is legitimate. All prime powers are handled; outside
the finite support window each actual term is zero. The source's
n+1 indexing corresponds to indices672,676,1398 for these survivors.

## Actual Arch bound, reverse pairs and rescaling

`distinct_fine_far_arch_norm_le` accepts arbitrary distinct p,q with
individual fine widths, the first packet's moment conditions and gap
at least log2. Its displayed proof calls the generic separated kernel
bound with the proved distinct-packet mean-energy envelope. All those
conditions hold here; neither shape equality nor a common translated
mother is required. The result is(E(u)+E(v))/200, namely1/100 times
the mean energy. The actual center term in B vanishes separately.

Adding the prime costs therefore gives exactly

    norm B(T_i u,T_j v)<=c_ij(E(u)+E(v))/2,
    c_9=14/25+1/100=57/100,
    c_10=8/37+1/100=837/3700,
    c_k=1/100 for1<=k<=8.

The actual Hermitian B identity handles i>j with the same symmetric
cost. The argument uses complex norms throughout, so arbitrary complex
shapes and subsequent coefficient phases cause no sign restriction.

Replacing u,v by ru,r^-1v with real r>0 preserves their exact source
domain, preserves B, and changes the upper bound to
c_ij(r^2 E(u)+r^-2 E(v))/2. Its infimum is
c_ij sqrt(E(u))sqrt(E(v)). If E(u)=0 use r increasing to infinity;
if E(v)=0 use r decreasing to zero. If both vanish the bound is zero
already. These are scalar limits of bounds on a fixed B value; no
continuity or limit interchange for B is assumed.

## Diagonal and weighted-consumer match

The existing diagonal theorem is universal in its mother argument and
can be applied separately to every h_i. Thus its constant5671/3200
and the derived square-root cross bound satisfy the existing
`weighted_gram_variable_energy` hypotheses with the original costs
c, original positive weights and original exact-cost maximum
S=25289/35500. The Gram coefficient convention is z_i conjugate(z_j),
matching the source's first-argument linearity.

On denominator1136000, the diagonal and row numerators are2013205
and809248. Their difference is1203957, confirming the printed exact
positive margin. No new Schur proof, weights or diagonal optimization
is needed.

For source attribution, the original RHActualElevenLattice module
provides the chosen costs/weights and its Q16 optimized-row theorem.
The exact-cost row ledger and maximum S used here come from the
earlier emitted standalone arithmetic certificate. These are distinct
proof surfaces; neither is a new analytic adapter replay.

## The stronger signed-sector corollary needs no new closure argument

The family is exactly the existing V_11(a): sums of independently
shaped legal mothers on the same eleven translated fine windows.
The disjoint-window energy identity is unchanged. Consequently the
positive-space lower bound may use

    mu_direct=1203957/1136000

in place of394709/1136000 everywhere in the existing scoped sector
composition. For eight arbitrary source packets in this SAME V_11(a),
the already justified linear closure and exact B expansion give

    2 Re B(U,cV)+mu_direct E(U+cV)
       <=-Re B(U,U)-Re B(cV,cV)

for every complex c. No physical sector orthogonality is introduced.
The existing strict-sign-to-refinement certificate construction also
continues unchanged, including its zero-packet branch. Its parameter
needs only a proved positive margin on the specified family.

This strengthens the scoped positive-family mixed-budget corollary
without changing its geometry or proving that every arbitrary legal
packet belongs to the family. It supplies no global RH conclusion.

No usage or tool limit prevented this bounded review. No archived
program was executed, no remote source or old checkpoint was changed,
and no new analytic Lean or transitive-kernel acceptance is claimed.
