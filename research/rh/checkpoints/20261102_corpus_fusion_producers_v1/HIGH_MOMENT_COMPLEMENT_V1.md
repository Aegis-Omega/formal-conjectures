# High moments, the actual 139 CvS atoms, and a positive complement

Status: NEW ordinary mathematical derivation, not a Lean theorem or a kernel replay. RH is not proved. Exact rational arithmetic below checks only explicitly identified constants. Scope of source search: fourteen initial selected source files, followed by the three source crosschecks identified in §13 and the ledger, at Aegis-Omega/formal-conjectures PR92 commit f8cb6544e9451910fbf1ed5fa71e76a5fa1b747f. No claim of novelty or exhaustive corpus search.

## 1. Conventions and exact objects

Let D=d/dx, D0=D²−1/4, I=(-R,R), and

P(D)=(D−1/2)^p(D+1/2)^q, n=p+q, p,q>=1.

Write M[s,k](H)=∫ x^k e^(sx) H(x) dx. Original legality in centered logarithmic coordinates is M[-1/2,0]=M[+1/2,0]=0. The raw logarithmic operator in the source WeilMomentKillerRangeV1 is D²+D, with moments ∫g=∫e^x g=0. These are conjugate, not identical: H=e^(x/2)g and Φ=e^(x/2)ψ imply D0Φ=e^(x/2)(ψ''+ψ'). All shifts preserve the full set of moments up to each specified degree by the binomial formula.

Fourier convention: Hhat(ξ)=∫ H(x)e^(-iξx)dx; E=||H||²₂=(1/2π)∫|Hhat|². This is Mathlib's Fourier evaluated at ξ/(2π).

For compact logarithmic support and the two original moments, define the complete Weil quadratic form with the usual zero-positive sign by

Q(H)=(1/2π)∫ w(ξ)|Hhat(ξ)|²dξ − 2∑_{m>=2} Λ(m)/sqrt(m) Re C_H(log m),

w(ξ)=Re ψ(1/4+iξ/2)−log π,
C_H(t)=∫ H(x) conjugate(H(x−t)) dx.

The pole terms vanish by the original moments. The prime sum retains EVERY prime power; compact support makes it finite. We work on the form domain X(I): L² functions supported in the closed interval, with ∫log(2+|ξ|)|Hhat(ξ)|²dξ finite. Cc∞ is a subspace; zero-extended piecewise smooth bounded functions with finitely many jumps also belong. Statements about this ordinary Q require the explicit-formula identification with the repository's actual packet form; the selected sources give the source-specific bridge and hypotheses, not an unconditional RH theorem.

## 2. Exact compact-support range, including adjoint signs

**Theorem 1.** For H∈Cc∞(I), the following are equivalent:

(a) H=P(D)u for u∈Cc∞(I).
(b) M[-1/2,k](H)=0 for 0<=k<p, and M[+1/2,k](H)=0 for 0<=k<q.

The compact inverse preserves the convex hull of support. Necessity follows by integrating against the kernel of P(−D); the negative sign on the first exponential is essential.

For sufficiency, for λ=±1/2 and 1<=j<=its multiplicity define

R[λ,j]H(x)=e^(λx)/(j−1)! ∫_{−∞}^x (x−t)^(j−1)e^(−λt)H(t)dt.

The integral is zero on the left. On the right it is e^(λx) times a polynomial whose coefficients are precisely weighted moments of H up to degree j−1, and hence is zero. Differentiation gives (D−λ)R[λ,1]H=H and (D−λ)R[λ,j]H=R[λ,j−1]H. The partial fractions of 1/P(z) now give u by a finite linear combination of these compact inverses. The distribution identity P(D)u=H follows from the same rational identity; convolution with smooth H gives an ordinary smooth solution. A homogeneous constant-coefficient ODE has only exponential-polynomial solutions, so the compact solution is unique.

The same proof for compact L² H gives u∈H^n(R), supported in the same interval, satisfying P(D)u=H weakly. One can justify H^n regularity directly from the distribution identity: P(iξ) has no real zero and has growth |ξ|^n, so (1+|ξ|²)^(n/2)/|P(iξ)| is bounded. This is the relevant range class when subtracting the rough CvS atoms below, not Cc∞.

## 3. A smooth finite correction with exactly n−2 dimensions

Choose nonzero φ>=0 in Cc∞((-r,r)), r<R, and U=D0φ. Choose n−2 distinct centers c_j in (-R+r,R−r). All U_j(x)=U(x−c_j) are legal and retain support in I.

Twice integrating by parts gives, for σ=±1/2 and k>=1,

M[σ,k](D0 T_cφ)=∫ e^(σx)[2σk x^(k−1)+k(k−1)x^(k−2)]φ(x−c)dx.

This is e^(σc) times a polynomial of degree k−1 in c, with leading coefficient 2σk∫e^(σt)φ(t)dt !=0. Hence the matrix of EXTRA moments of U_j is an invertible triangular row transformation of evaluation of

e^(−c/2)c^l (0<=l<p−1), e^(+c/2)c^l (0<=l<q−1).

A real exponential polynomial with real characteristic roots and total multiplicity d has at most d−1 real zeros counting multiplicity, unless identically zero. Proof by induction: multiply by e^(−λx), differentiate, and apply Rolle with multiplicities; the differentiated exponential-polynomial space has dimension d−1. If the derivative vanishes identically the original function is a single exponential. The same argument works on every finite interval and then on R. This proves invertibility at any d distinct real centers; complex nullvectors split into real and imaginary ones.

Consequently the legal smooth space is the exact direct sum

W0(I)=span{U_j:1<=j<=n−2} ⊕ P(D)Cc∞(I).

There are no omitted mixed terms: this is an algebraic/domain decomposition, not positivity of the sum. The correction projection is bounded in L² on a fixed interval because every moment functional is bounded there and the fixed finite matrix is invertible.

## 4. The ACTUAL CvS 139 atoms also give a correction complement

The source CvSMomentBasisV1 defines, on [0,L],

Φ_a(x)=sin²(πx/L)e^(2πiax/L),
U_a=D0Φ_a, a=-69,...,69.

The actual atom used in the integral is the zero extension 1_[0,L] U_a. The source proves its two exponential moments vanish by Φ_a=Φ'_a=0 at BOTH endpoints. The Fourier weights (−1/4,1/2,−1/4) alone are not the legality argument. These atoms are modulations of a potential, not translates of one U. The zero-extended potential is C¹ and piecewise smooth, U_a is L² with possible jumps, and U_a belongs to X([0,L]) because its Fourier transform is O(1/|ξ|).

**Theorem 2.** For p=71,q=70, the 139-by-139 matrix of extra moments

M[-1/2,k](U_a), k=1,...,70;
M[+1/2,k](U_a), k=1,...,69

is invertible for EVERY L>0.

Proof. Suppose a combination U=D0Φ, Φ=sin²(πx/L)T(x), T=∑_{a=-69}^{69}c_a e^(2πiax/L), has all extra moments zero. The integration-by-parts triangular identities in §3 imply

∫ Φ(x)e^(−x/2)x^j dx=0, j=0,...,69;
∫ Φ(x)e^(+x/2)x^j dx=0, j=0,...,68.

The span V of these 139 real exponential polynomials is an extended Chebyshev space on R by the multiplicity proof above. The real and imaginary parts of Φ separately have these orthogonalities; the trig span is conjugation stable. A nonzero real trig polynomial T of degree <=69 has at most138 zeros (with multiplicity) in one period: multiply by e^(2πi69x/L) to obtain a nonzero polynomial of degree <=138 in e^(2πix/L). Thus it has at most138 sign changes on (0,L).

Let its m sign changes be x_1<...<x_m, m<=138. Select any nested real-root exponential-polynomial subspace of V of dimension m+1. Solving m homogeneous point conditions yields a nonzero F vanishing at the x_i. Its zero bound counting multiplicity forces all these roots to be simple, with no other roots in (0,L). Change its overall sign to agree with T. Then sin²(πx/L)T(x)F(x)>=0 throughout (0,L) and is positive on some open interval. Its integral is strictly positive, contradicting orthogonality to V. Thus T=0, proving injectivity and hence matrix invertibility. No numerical determinant is required.

As a result, on X([0,L]) intersected with the original two moment conditions there is a direct sum

H=∑_{a=-69}^{69} c_a U_a + V,
V∈X([0,L]), M[-1/2,k](V)=0 (k<=70), M[+1/2,k](V)=0 (k<=69).

The projection onto the atom span is defined by these moments and is generally OBLIQUE, not the source's L²-orthogonal projection. This distinction changes the mixed-term calculation. V=P(D)u for compact u∈H^141, not necessarily smooth. This is an actual source-object connection, beyond the coincidence 141−2=139. It does not identify this moment projection with the source's R_basis or its trace-minimizing coefficients.

## 5. Efficient Hermite remainder using ALL weighted moments

Let H satisfy the n conditions in Theorem1, centered in [-R,R]. Interpolate the entire function f_x(z)=e^(zx) in its spectral variable z at nodes −1/2 repeated p times and +1/2 repeated q times. Its Hermite interpolant, evaluated at z=−iξ, is a linear combination of x^k e^(−x/2), k<p, and x^k e^(+x/2), k<q. It integrates to zero against H.

The exact interpolation remainder is

f_x(z)−interpolant(z)=(z+1/2)^p(z−1/2)^q f_x[−1/2 (p times),+1/2 (q times),z].

The Hermite–Genocchi formula writes this last divided difference as the simplex integral of x^n exp(x∑t_j z_j), whose simplex volume is 1/n!. It follows first for distinct complex nodes from the fundamental theorem of calculus on line segments, then for repeated nodes by continuity. Every node has real part in [-1/2,1/2] when z=−iξ. Therefore

|remainder| <= e^(R/2) R^n (ξ²+1/4)^(n/2)/n!.

Crucially there is NO exp(R|ξ|) loss. Hölder and Plancherel give

(1/2π)∫_{−T}^T |Hhat(ξ)|²dξ <= ε_n(R,T) E,
ε_n=(2RT/π)e^R [R²(T²+1/4)]^n/(n!)².

This holds for all compact L² H with the stated moments, without smoothness. For fixed R,T, ε_n tends to zero as n grows.

## 6. Full Archimedean and prime control, with no omitted tails

From the convergent digamma series,

w(ξ)−w(0)=∑_{j>=0} [1/(j+1/4)−(j+1/4)/((j+1/4)²+(ξ/2)²)].

Every term is nonnegative and increasing with |ξ|. Thus w>=w(0), w(ξ)>=w(T) for |ξ|>=T, and w(T) tends to infinity (retain j+1/4<=T/2, where each term is at least 1/[2(j+1/4)]).

Equivalently w(ξ)−w(0)=∫_0∞ e^(t/2)(1−cos ξt)/sinh(t)dt. This identity follows by expanding 1/sinh(t) as a nonnegative exponential series and applying Tonelli to 1−cos. On the form domain the Archimedean quadratic identity follows from Plancherel and the same nonnegative Tonelli argument. It does not discard an Archimedean tail or exchange a conditionally convergent signed integral.

For support [-R,R], C_H(t)=0 when |t|>2R, and |C_H(t)|<=E. Hence the COMPLETE prime-power operator has the bound

|2∑ Λ(m)/sqrt(m) Re C_H(log m)| <= A_R E,
A_R=2∑_{2<=m<=e^(2R)} Λ(m)/sqrt(m).

Consequently

Q(H)>= [w(T)−A_R−(w(T)−w(0))ε_n(R,T)] E.

For each fixed support and prescribed δ>0, choose T with w(T)>A_R+2δ, then n large enough. This proves an unconditional positive finite-codimension complement on each fixed support. It does NOT control its finite-dimensional correction or their mixed terms.

## 7. Concrete complement at the actual CvS width L=6/5

Translate [0,6/5] to [-3/5,3/5]. All weighted moment sets are invariant under this translation. Set R=3/5,T=64,n=141,p=71,q=70.

The accompanying exact-rational checker proves:

* ε_141(3/5,64)<1/1000. It uses π>3 and exp(3/5)<2; its much smaller diagnostic decimal is not needed.
* w(64)>229/100.
* w(0)>−6.
* A_R=2(log2/sqrt2+log3/sqrt3)<9/4. No other prime power is active because exp(6/5)<4.

For the digamma inequalities it uses γ<3/5, logπ<23/20 and, for N=1024 or2,

w(2y) >= −3/5−23/20 +∑_{j=0}^{N−1}[1/(j+1)−(j+1/4)/((j+1/4)²+y²)] −(3/4)/(N−3/4).

Indeed each omitted summand is >=−(3/4)/(j+1/4)²; the integral test bounds their sum. This explicitly controls the infinite tail, rather than treating a truncated sum as an enclosure.

Elementary constants are independently reducible to rationals: γ<=H_32−log32 and log2>0.692 from the first three positive terms of 2atanh(1/3); log2<0.6932, log3<1.0987, and logπ<1.15 from finite positive exponential Taylor sums; sqrt2>1.4142 and sqrt3>1.7320 by squaring. The classical π<22/7 follows by integrating the positive function x^4(1−x)^4/(1+x²) on (0,1), whose integral is22/7−π. The elementary π>3 may equally be obtained from the alternating geometric integral for4atan(1), using enough terms. The checker uses exact Taylor geometric remainders for exp(3/5)<2.

We obtain, for EVERY residual V in the actual CvS moment complement,

Q(V) >= [ (229/100)(1−1/1000)−6/1000−9/4 ]||V||²₂
      = (3171/100000)||V||²₂ > (3/100)||V||²₂.

The equality arithmetic is (2.29−2.25)−0.00829=0.03171. This is a positive full-form complement, conditional only on the exact moment constraints, NOT on RH or on a new unproved sign assumption. No claim is made that the existing Lean trace complement is this complement.

## 8. Adversarial tests and remaining load-bearing task

1. Roots with the wrong adjoint sign are rejected by integration by parts.
2. Higher-order ranges are proper subspaces; the 139 correction is indispensable.
3. Trig coefficient constraints alone do not imply legal exponential moments; the source uses endpoint vanishing and D0.
4. CvS atoms have boundary jumps: all decompositions involving them use X(I)/compact H^141 potentials, not Cc∞.
5. The oblique moment complement is not the source's orthogonal complement. Reusing an orthogonal-complement cross bound without transport is invalid.
6. The compact-support prime cutoff includes all powers and endpoints. At L=6/5 exactly2,3 can contribute, and both are retained in the operator bound.
7. Arbitrary low and high positive blocks do not make the full form positive. A 2-by-2 counterexample is [[1,2],[2,1]], whose diagonal blocks are positive but eigenvalue−1 remains.
8. The finite-width result does not cover arbitrary supports, detectingPacket, or all legal packet functions.
9. CvSProjectedTransportL12V1.hTransport is a finite exact congruence for Q_CvS and R_basis. Its own coercivity consumers still require interval entries, R_basis surjectivity/norm bounds, and signed cross budgets. CvSActualWeilInteropV1 converts an ALREADY supplied packet zero-side sign into an actual mixed budget; it does not manufacture the missing sign.

**Initially proposed local obligation (SUPERSEDED by recovered source composition in §13):** for L=6/5, the signed low/high Schur inequality for the actual moment projection is:

Q(v) >= sup_{V in this141-moment complement, V!=0} |B_Q(v,V)|²/Q(V)
for every v in span{actual139 CvS atoms}.

That L² cross bound does exist for these actual atoms. Each U_a is piecewise smooth with finite jumps, hence Uhat_a=O(1/|ξ|). The digamma series, split at j≈|ξ|, gives w(ξ)=O(log(2+|ξ|)); therefore w Uhat_a∈L². The complete prime part is a finite sum of bounded translations at this width. Thus A U_a∈L², where A is the full Archimedean multiplier minus the finite prime-shift operator, and B_Q(v,V)=<1_I Av,V> for the form domain.

Let Π be the L² projection onto the nullspace of the141 weighted moments. It is the orthogonal complement of the141 exponential-polynomial functions (not the span of the139 CvS atoms). Then

|B_Q(v,V)|² <= ||Π(1_I Av)||²₂ ||V||²₂.

A concrete sufficient finite matrix inequality is therefore

Q(v) >= (100/3)||Π(1_I Av)||²₂ for every actual CvS low vector v.

The projection is explicitly computable from the positive Gram matrix of the141 real exponential-polynomial functions. If Y_a=1_I A U_a and F is this141-dimensional span, its cross-cost matrix is D_ab=<Y_a,Y_b>−<Proj_F Y_a,Proj_F Y_b>. Testing C−(100/3)D>=0, where C is the full actual low Gram matrix, is a genuine proof-or-falsification target. It may fail because the crude0.03 bound loses information; failure would reject this sufficient budget, not Q or RH. The exact complement-energy Schur norm is sharper and remains another target. No positivity of this finite matrix has been asserted or checked here. Arbitrary-width/globalization remains a separate requirement.

## 9. Source and trust ledger

All source copies are bound by SOURCE_MANIFEST.json, ADDITIONAL_SOURCE_MANIFEST.json and TRANSPORT_SOURCE_MANIFEST.json; Git blob identity was recomputed from bytes. The selected source files contain complete proof bodies for their stated conditional theorems; no fresh typecheck was performed here. Their existing reported checks must not be upgraded to fresh kernel evidence.

The new arguments in §§2–7 are ordinary proofs, not extracted Lean terms. high_moment_exact_bounds.py is a small rational checker for numerical constants. Its success is not a soundness theorem for §5, not a proof of all CvS premises, not a Lean axiom audit, and not RH. A complete source-bound ordinary proof and independent mathematical review are still distinct trust dimensions from the exact arithmetic receipt.

## 10. Stronger constants, preserving the original receipt

A separate source file high_moment_T85_extension.py preserves the original T64 result and checks:

* T=80: ε<10^(-10), w(80)>251/100, hence Q(V)>(1/4)||V||².
* T=85: ε<13/20000, w(85)>103/40, hence Q(V)>(31/100)||V||².

The second assertion follows from (103/40)(1−13/20000)−6(13/20000)−9/4 =255541/800000 >31/100. These are exact Fraction comparisons with the same controlled digamma tail. No coefficient solve or matrix conditioning enters. This improves the crude cross-budget factor from100/3 to100/31; it does not by itself establish any cross-budget inequality.

## 11. Physical operator, endpoint logarithms, and full prime shifts

For H zero-extended from [0,L], smooth on this closed interval before zero extension, set a(t)=e^(t/2)/sinh(t), t>0. For almost every x∈(0,L),

A_arch H(x)=w(0)H(x)+∫_0∞ a(t)[H(x)−(H(x+t)+H(x−t))/2]dt.

The individual first and second shifted terms must not be integrated separately at t=0: the displayed difference supplies the cancellation. A form-safe proof first truncates t to [ε,B], uses Plancherel on the bounded Fourier multiplier, and then passes to the nonnegative quadratic difference form; polarization gives the bilinear identity. For these piecewise smooth H the result also exists pointwise inside the interval and is in L², as the explicit formula below proves.

Define the exact tail

J(s)=∫_s∞ a(t)dt
    =log((1+e^(−s/2))/(1−e^(−s/2)))+2atan(e^(−s/2)), s>0.

This follows by u=e^(−t/2), giving4∫_0^(e^(−s/2))du/(1−u⁴). Then

A_arch H(x)=w(0)H(x)
 + (1/2)∫_0^x a(t)[H(x)−H(x−t)]dt
 + (1/2)∫_0^(L−x) a(t)[H(x)−H(x+t)]dt
 + (H(x)/2)[J(x)+J(L−x)].

Every inner difference integral is ordinary absolutely convergent: |H(x)−H(x±t)|<=||H'||∞ t and a(t)t is bounded at0. The entire infinite tail is retained in J. Since J(s)=−log s+log4+π/2+O(s),

A_arch H(x)=−(H(0)/2)log x+O(1) as x↓0,
A_arch H(x)=−(H(L)/2)log(L−x)+O(1) as x↑L.

These logarithmic endpoint singularities are in L²; dropping them changes the cross matrix.

For the actual finite Fourier representation H(x)=∑_k b_k e^(iω_k x), this becomes

A_arch H(x)=∑_k b_k e^(iω_k x) [w(0)+(J(x)+J(L−x))/2
 +(1/2)∫_0^x a(t)(1−e^(−iω_k t))dt
 +(1/2)∫_0^(L−x) a(t)(1−e^(+iω_k t))dt].

The actual CvS weights are b_k=β_k(−ω_k²−1/4), with β from the source sinSqWeight and ω_k=2πk/L. This expression covers the actual atom functions, not an invented smooth substitute.

The full prime operator on this interval is

A_prime H(x)=−∑_{2<=m<=e^L} Λ(m)/sqrt(m) [H(x+log m)+H(x−log m)],

where H on the right is zero outside [0,L]. At L=6/5 the sum is exactly m=2,3. These shifted samples have their actual indicator boundaries x=L−log m and x=log m; no periodic wraparound is permitted. For any finite L, all prime powers m in the cutoff are retained. This is a bounded operator in L². Thus A H= A_arch H+A_prime H provides an explicit physical cross-functional formula, including endpoint logs and every prime-power shift. It does not assume positivity of Q.

## 12. General actual-CvS complement for EVERY fixed support

The argument of §4 is not special to139: take the actual sin²-potential atoms with frequencies −N,...,N. Their span has dimension2N+1. Set p=N+2,q=N+1,n=2N+3. The higher-moment reduction yields exponent −1/2 with degrees0,...,N, and exponent+1/2 with degrees0,...,N−1: total2N+1. The same trig zero count and real-exponential Chebyshev sign test prove the correction matrix invertible for every L>0.

For any fixed L=2R and any desired δ>0, first choose finite T with w(T)>A_R+2δ. Next choose N large so ε_(2N+3)(R,T) is sufficiently small. This proves

∀R>0 ∀δ>0 ∃N, Q(V)>=δ||V||²

on the corresponding full high-moment complement, with an exact finite correction by the ACTUAL2N+1 CvS atoms. Neither a fixed N for all supports nor all-support positivity of Q is asserted. One crude bound making the prime part finite explicitly is A_R<=8R e^R, using Λ(m)<=log m and the integral bound for∑m^(−1/2). It is far from sharp but unconditional. Rational upper bounds for exp(R), factorials and the digamma tail yield a terminating search for the complement constants. This proves termination ONLY for the complement certificate, not for a full Schur/RH certificate generator.

## 13. Existing local positivity supersedes the proposed local sign search

After §8 was drafted, the parent recovered the exact-source theorem CvSWindowL43V1.window_L43 (PR92 current source), used without an RH premise in RHL43ActualWeightedGramV1. Its ordinary source endpoint covers every smooth legal packet with full logarithmic width<=4/3. No fresh kernel replay of that source was performed in this run. This stronger existing local result must be reused rather than re-proved.

For H∈X([0,6/5]) with both original moments zero, let η_ε be a nonnegative compact smooth unit-mass mollifier and H_ε=H*η_ε. The moments multiply:

M[σ,0](H*η_ε)=M[σ,0](H) M[σ,0](η_ε)=0.

For sufficiently small ε, its logarithmic support has width6/5+2ε<4/3. Moreover H_ε→H in the norm ∫log(2+|ξ|)|Hhat|², by Fourier dominated convergence, since |ηhat_ε|<=1 and ηhat_ε→1. Thus the full Q values converge; the prime shift operators are bounded and the Archimedean multiplier is bounded by a constant times log(2+|ξ|). The smooth inverse log lift g(y)=y^(−1/2)H_ε(log y) gives the legal repository packet. Applying the recovered local theorem and taking the limit yields Q(H)>=0 on this rough6/5 domain.

It follows directly, by applying this positivity to v+zV for all complex z, that |B_Q(v,V)|²<=Q(v)Q(V) for the low vectors and high-moment complement constructed here. Thus the EXACT local Schur sign from §8 is already supplied by composition with the recovered source theorem, at the level of ordinary mathematics and subject to exact source bridge verification. Its fresh formal domain transport/replay is PORT_PENDING, not a new unproved local sign. The cruder sufficient matrix C−(100/31)D may still fail and is unnecessary for local positivity.

The genuinely global mathematical content not supplied by these local results is the signed low/high Schur budget for arbitrary support L, or another unconditional producer of full Weil positivity. This paper does not claim that global inequality, or RH. The new useful construction is an explicit finite-codimension positive complement for every fixed L, compatible with the actual CvS modulated potential family, together with the full physical cross operator. At larger L it gives a precise way to attack the missing finite signed block, rather than inferring global positivity from local diagonal signs.

## 14. Endpoint-log part is rank one on the actual atom family

Put a=π/L and ω_n=2πn/L. The source potential is sin²(ax)e^(iω_nx), and for every integer n,

U_n(0)=U_n(L)=2a²,
U'_n(0)=U'_n(L)=6iω_n a².

Split the explicit J-tail part as a²[J(x)+J(L−x)] + (U_n(x)−2a²)[J(x)+J(L−x)]/2. The second summand is bounded because U_n−2a² vanishes at both endpoints. Thus the UNBOUNDED endpoint-log part is the SAME function a²[J(x)+J(L−x)] for every column n, modulo a bounded function. Its endpoint-log coefficient has rank one across the whole CvS atom span. For v=∑c_n U_n, Σc_n=0 removes both leading endpoint logarithms. This does not remove the bounded interior difference integrals or the prime shifts.

More generally U_n^(j)(0)=U_n^(j)(L) is a polynomial in n of degree j, with nonzero leading term a²(j+1)(j+2)(iω_n)^j. To see this, write

U_n^(j)(0)=(1/2)F_j(ω_n)−(1/4)F_j(ω_n−2a)−(1/4)F_j(ω_n+2a),
F_j(z)=(iz)^j((iz)²−1/4).

The centered second difference lowers polynomial degree by two, giving the stated leading term. Thus imposing the r discrete coefficient moments ∑n^k c_n=0, k<r, kills the first r endpoint jets of v. The zero extension is C^(r−1), and integration by parts yields vhat(ξ)=O(|ξ|^(−r−1)). A finite-difference basis of the coefficient vectors realizes this regularity flag without identifying it with exponential moment annihilation. These are two different constraint systems. This structure offers an exact way to isolate endpoint-log cost in a future cross-block calculation, not a new sign theorem.

## 15. Exact finite-difference basis and a mixed-Gram tail theorem

Let the actual CvS span have frequencies n=−N,...,N, and write

z=e^(i2πx/L), F(z)=∑_{n=−N}^N c_n z^(n+N),
Φ(x)=sin²(πx/L)∑c_n e^(i2πnx/L)=−(1/4)z^(−N−1)(z−1)²F(z),
v=D0Φ.

By §14, the triangular leading coefficients of the endpoint-jet polynomials are nonzero. Therefore, for0<=r<=2N,

v^(j)(0)=v^(j)(L)=0 for0<=j<r
 iff ∑ n^j c_n=0 for0<=j<r
 iff F is divisible by(z−1)^r.

The last equivalence follows because applying (z d/dz−N)^j to F at1 gives ∑n^j c_n; these operators are triangular combinations, with unit leading coefficients, of ordinary derivatives at1. Thus vanishing through order r−1 is exactly an r-fold zero at1. The polynomial basis F_r(z)=(z−1)^r, r=0,...,2N, is an exact triangular basis of all coefficient polynomials. Its source Fourier coefficients are finite binomial integers, not a numerical inverse matrix. Put

Φ_r=−(1/4)z^(−N−1)(z−1)^(r+2), v_r=D0Φ_r on[0,L], zero-extended.

The potential has endpoint zero of order r+2. Hence v_r and its derivatives through order r−1 vanish there; all these functions retain both legal exponential moments. For |t|>0, r+1 integrations by parts yield

|vhat_r(t)| <= C_r |t|^(−r−1),
C_r=|v_r^(r)(0)|+|v_r^(r)(L)|+∫_0^L |v_r^(r+1)(x)|dx.

There is no unproved boundary cancellation in this bound: the r-th derivative boundary term is explicitly paid. If v_r=∑b_{r,k}e^(iω_kx) on the interval, one elementary finite upper bound is

C_r <= 2∑|b_{r,k}||ω_k|^r + L∑|b_{r,k}||ω_k|^(r+1).

Exact sharper C_r may use the known endpoint polynomial instead. No claim of improved numerical conditioning is made; binomial coefficients may themselves grow rapidly.

For t>=1, the same digamma series gives w(t)<=log t+3. Indeed set J=ceil(t+1), b=t/2, a_j=j+1/4. The first J terms are bounded by H_J, and the remaining terms are at most

b²∑_{j>=J}a_j^(−3) <= b²/[2(J−3/4)²] <=1/8.

Discarding the negative constants −γ−logπ gives w(t)<=H_J+1/8 <=1+log(t+2)+1/8 <log t+3. Together with w(t)>=w(0)>−6, this proves |w(t)|<=6+log t for t>=1.

Consequently for T>=1 the full infinite Archimedean mixed-Gram tail is rigorously bounded by

|(1/2π)∫_{|t|>T} w(t)vhat_r(t) conjugate(vhat_s(t))dt|
 <= (C_r C_s/π) T^(−r−s−1)
    [(6+log T)/(r+s+1)+1/(r+s+1)²].

This follows by integrating t^(−r−s−2)(6+log t) exactly. It pays mixed terms for every pair, not just diagonal values. The bound also applies to the COMPLETE finite-support multiplier S_L(t)=w(t)−2∑_{2<=m<=e^L}Λ(m)/sqrt(m)cos(t log m), with6 replaced by6+A_(L/2), since every finite prime power is retained and the full cosine polynomial is bounded by A_(L/2). Alternatively those prime shifts may be integrated exactly using §11 and only the Archimedean tail estimated. No truncation of the prime band is authorized by this theorem.

This produces an exact coefficient-level interface for sound finite Gram tail control on the actual CvS span, across arbitrary finite L and N. It does not prove a low matrix positive, a signed row budget, or all-support Weil positivity. Its role is to remove an infinite-tail ambiguity before such a finite inequality is attempted.
