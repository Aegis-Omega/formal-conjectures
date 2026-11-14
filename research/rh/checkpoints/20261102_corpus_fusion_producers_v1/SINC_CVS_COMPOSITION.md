# Exact sinc-to-CvS composition and cutoff stabilization

Ordinary source-bound derivation. No fresh Lean port of these adapters is
claimed. Existing `CvSAtomInversionV1.atom_sum` is reused, not reproved.
Source bytes and existing replay scopes are kept separate.

## 1. Correct the carrier by composing with the existing atom inversion

Let r>0,L=2r,K>=1 and

    H(x)=sum_(k=-K)^K c_k/(2r) exp(i k pi x/r) 1_[-r,r](x).

Its Fourier basis is the recovered sinc basis psi_k(t)=sinc(rt/pi-k), and
its exact energy is (1/L)sum|c_k|². Set

    d_k=(-1)^k c_k/L,
    omega_k=2pi k/L,
    a_k=-(omega_k²+1/4),
    beta_k=d_k/a_k.

All a_k are nonzero. On [0,L], the translated function H(y-r) is D0 Phi,
where Phi(y)=sum beta_k exp(i omega_k y). Phi and Phi' are periodic at the
endpoints. For sigma=+/-1/2, integration by parts gives EXACTLY

    integral_0^L exp(sigma y)H(y-r)dy
       =(exp(sigma L)-1)
          [sum i omega_k beta_k - sigma sum beta_k].

There is no interior term because sigma²=1/4. Both exponential factors
exp(sigma L)-1 are nonzero. Hence the two ACTUAL target moments vanish iff

    sum beta_k=0 and sum k beta_k=0.

These are precisely the two premises of the ALREADY PROVED finite
`AEGIS.CvSAtomInversionV1.atom_sum`, read in the pinned source copy
`/workspace/aegis-nov2-independent/HighMoment/CvSAtomInversionV1.lean`.
Define, exactly as its `alpha` definition,

    alpha_p=-4 sum_(j=0)^(p-1) (p-j) beta_(j-K), 1<=p<=2K-1.

Its actual conclusion gives the concrete reconstruction

    H(y-r)=sum_(p=1)^(2K-1) alpha_p momentAtom L (p-K)(y)

on the interval, followed by zero extension. The Fourier factors a_k are
the source `Ez` factors. Conversely every such actual atom sum satisfies
both moments by the source endpoint theorem. Thus the CORRECTLY constrained
finite sinc space and the actual CvS atom space are the SAME functions,
with an explicit finite coefficient transport, exact form and exact energy.

For K=70 this is exactly the actual 139-atom space already recovered.
For the older probe's default K=40 it is 79-dimensional, rather than its
80-dimensional one-evaluation-constrained space. The two constraint kernels
are different, not merely an interchangeable codimension count. The existing
source inversion supplies the finite algebra; the new ordinary adapter
supplies the actual Mellin-moment interpretation of the coefficients.

## 2. Prime-cutoff stabilization on the SAME compact-support carrier

Write Q_M for the complete Archimedean-minus-prime form with prime powers
through M. If log(M+1)>2r, then for EVERY H supported[-r,r],

    Q_P(H)=Q_M(H) for every P>=M.

Indeed C_H(log m)=0 when log m>=2r: the two L² support intervals intersect
only in a null set or are disjoint. Every additional prime term is exactly
zero. This is the compact-support mechanism already used in the recovered
source spectral/zero-side bridges. The same assertion holds for mixed
entries of two functions in the common interval. No numerical limit is
required and the endpoint correlation is zero, not an uncertain sample.

In the recovered positive-jump decomposition, put

    D_M(H)=Q_M(H)-(w(0)-A_M)||H||²,
    A_M=2sum_(m<=M) Lambda(m)/sqrt(m).

Then for P>=M above the support threshold,

    D_P(H)=D_M(H)+(A_P-A_M)||H||².

On ANY fixed nonzero subspace of this carrier, the exact infimum of
D_P(H)/||H||² rises by A_P-A_M, while the adverse scalar shifts by exactly
the same amount. Their signed difference is unchanged. Increasing the
cutoff cannot improve the actual signed budget after support is covered.
This is also true on the exact two-moment subspace; it does not prove
that unchanged budget is nonnegative.

## 3. Why the finite-frequency probe can drift despite that exact theorem

The old probe integrates only t in[-T,T]. Such a frequency truncation is not
the exact angular inner product of the original compactly supported basis.
Inactive prime correlations may therefore fail to vanish numerically. This
does not contradict cutoff stabilization of the exact form.

Here is a rigorous frequency-tail bound, before ANY trapezoid or rounding
error. Assume T>=2pi K/r. For |t|>=T and |k|<=K,

    |psi_k(t)|<=2/(r|t|).

Therefore, for every j,k in the basis and every real shift d,

    |(1/(2pi)) integral_(|t|>T) cos(dt)psi_j(t)psi_k(t)dt|
       <=4/(pi r² T).

If |d|>=2r its full integral is exactly zero, so the same bound controls
the spurious truncated integral. Let A_inactive=2sum c_m over the extra
prime powers with log m>=2r. Their total matrix-entry contamination is at
most

    4 A_inactive/(pi r² T).

There are D=2K+1 basis functions, and their exact Gram is I/(2r). By
(sum|c_k|)²<=D sum|c_k|², the resulting Rayleigh error is at most

    8 D A_inactive/(pi r T).

This controls ONLY the omitted frequency tails. The source's trapezoid and
floating errors require their own bounds. It is not a certificate for an
old observed eigenvalue. It explains why increasing the arithmetic cutoff
at fixed frequency resolution can change a numerical model even when the
exact compact-support form is unchanged.

For the complete multiplier, the independently checked bound
|w(t)|<=6+log|t| for |t|>=1 gives, when T>=max(1,2pi K/r), the full
mixed-entry frequency-tail bound

    4[7+A_M+log T]/(pi r² T).

This includes every retained prime power; alternatively its prime shifts
can be integrated exactly in physical coordinates and only the Archimedean
tail paid. The bound follows by integrating (6+A_M+log t)/t², with both
frequency tails and the angular factor retained.

The finite-difference basis in the high-moment manuscript improves the
power of T separately for every pair by killing boundary jets. It does
not discard the one common jump direction or its cross terms. These
transport and tail facts make the old sinc laboratory and actual CvS
geometry mathematically comparable after all stated corrections; neither
the old one-constraint spectrum nor the corrected finite spectrum is by
itself a universal sign theorem.
