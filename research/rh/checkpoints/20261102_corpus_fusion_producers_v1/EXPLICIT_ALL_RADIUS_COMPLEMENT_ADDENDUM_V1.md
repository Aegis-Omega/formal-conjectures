# An explicit dimension selector for the balanced positive complement

NEW ordinary proof addendum,2026-11-02. No global positivity or RH claim. This gives a completely explicit replacement for the existential dimension choice in the high-moment complement theorem. It does not change the original manuscript or its receipts.

Let R>=1 be an INTEGER, H supported in[−R,R], and let the full prime-power operator bound be

A_R=2∑_(2<=m<=exp(2R)) Λ(m)/sqrt(m).

Set the following positive integers:

a=8R*3^R,
K=a+8,
T=3^K,
A0=R(T+1),
B0=2RT*3^R,
J=max(2,3A0,B0(a+9)),
n=2J,
N_CvS=J−2.

Then every H satisfying the BALANCED weighted moments

M[±1/2,k](H)=0 for0<=k<J

obeys Q(H)>2||H||² unless H=0 (where equality0 holds). The actual balanced CvS low correction has2J−2 dimensions, J−1 of each parity, by the preceding addendum. All quantities are finite integers. Their size is enormous; this is not a practical certificate-generation cost claim.

Proof. Since Λ(m)<=logm<=2R and∑_(m=2)^M m^(−1/2)<=2sqrt(M),

A_R<=8R e^R<8R3^R=a.

For t>=2, put b=t/2 and M=floor b>=1 in the digamma series. The first M+1 positive reciprocal terms sum to H_(M+1)>log b. The subtracted Lorentzians satisfy

∑_(j=0)^M (j+1/4)/((j+1/4)²+b²)
 <=(M+1)(2M+1)/(4M²)<=3/2.

The remaining series is greater than−3/(4M), by the same integral-test lower tail used in the original exact checker. Thus

w(t)>log t−[log(2π)+γ+3/2+3/4] >log t−5,

using log(2π)<log8<21/10 and γ<3/5. Since log3>1,

w(T)>log T−5>K−5=a+3.

The Hermite remainder for order n yields

ε_n <= B0*A0^(2n)/(n!)².

Indeed e^R<3^R, π>1 and R sqrt(T²+1/4)<R(T+1)=A0. The elementary integral bound log(n!)>=n log n−n+1 gives n!>=(n/e)^n. Since e<3 and n=2J>=6A0,

ε_n < B0*(3A0/n)^(2n) <= B0*4^(−n).

Now4^n>=n+1>B0(a+9), because J>=B0(a+9). Therefore ε_n<1/(a+9). With w(0)>−6 and the complete prime operator bound A_R<a,

Q(H)>[(a+3)(1−ε_n)−6ε_n−a]||H||²
     =[3−(a+9)ε_n]||H||²>2||H||².

The zero function is the harmless equality case; the strict inequality is for nonzero H. This fixes the quantifiers explicitly:

forall integer R>=1, the stated computable J_R works for the corresponding2J_R-moment subspace.

Every finite real support radius is covered by choosing an integer R at least that radius. The moment order and low-space dimension grow with R. No fixed order, fixed basis, or uniform coercivity on the ORIGINAL two-moment class has been proved. In particular this does not conflict with a null sequence that avoids these increasingly restrictive high-moment kernels.

## What remains

All analytic high-complement constants are now explicitly produced from the support integer. The remaining content of this architecture is the signed finite low/complement Schur budget for the actual low space, for arbitrary R. The dimension selector does not produce that budget or prove that a full certificate search succeeds. Positivity of the two diagonal blocks alone does not control the mixed block.
