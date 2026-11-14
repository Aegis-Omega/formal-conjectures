# Balanced moment complement on actual CvS atoms

NEW ordinary proof addendum,2026-11-02. Does not modify the original high-moment manuscript or its receipts. No Lean replay or RH claim. It uses the source objects pinned in UNIFIED_SOURCE_MANIFEST.json at f8cb6544e9451910fbf1ed5fa71e76a5fa1b747f; the subsequently observed d7e6bc7602ccfe4bf5fb094ab595b36eb532d8d5 head leaves those selected mathematical source bodies unchanged according to the parent source comparison. The new λ-lab's numerical parity observation motivates checking the decomposition, not assuming its sign.

Let L>0 and I=[−L/2,L/2]. Define the centered, phase-corrected actual source atoms

V_n(x)=(-1)^n U_n^source(x+L/2)
      =D0[cos²(πx/L)e^(i2πnx/L)] inside I, zero outside,
D0=D²−1/4.

The phase is required: source U_n uses y∈[0,L], so translating its exponential produces(-1)^n. A global nonzero phase changes neither span nor legality. Put

C_n=(V_n+V_(−n))/2, n=0,...,N;
S_n=(V_n−V_(−n))/(2i), n=1,...,N+1.

They are real functions, respectively even and odd. The actual original2N+1-atom span is enlarged by ONE odd atom S_(N+1), giving low space L_N of dimension2N+2: N+1 even and N+1 odd directions. For N=69 this is the original139 atoms plus (U70−U−70)/(2i) after centering;70 is even, so its phase is+1.

**Theorem.** The legal logarithmic form domain on I splits uniquely as

H=v+V, v∈L_N,
M[±1/2,k](V)=0 for0<=k<=N+1.

The low projection and its complementary projection commute with reflection. In particular this is an exact parity-compatible decomposition. The high range is (D²−1/4)^(N+2)u for a compact H^(2N+4) potential, not necessarily a compact smooth potential when H or v has endpoint jumps.

Proof of the finite matrix statement. All low atoms are legal by the source endpoint integration-by-parts argument. Applying that argument to each extra moment k=1,...,N+1 converts the moment map by invertible triangular row operations into pairing the potential Φ with

E=span{x^k e^(−x/2),x^k e^(+x/2):0<=k<=N}.

This real-root exponential-polynomial space has dimension2N+2, and every nonzero member has at most2N+1 real zeros counting multiplicities, by the differentiated Rolle induction in the main manuscript. E is reflection invariant and splits into even and odd spaces E_+,E_− of dimension N+1 each. An explicit basis uses x^k cosh(x/2) for even k and x^k sinh(x/2) for odd k in E_+, and the opposite choices in E_−.

Every nonzero F∈E_+ has at mostN positive zeros, counting multiplicity, since positive zeros are mirrored. Every nonzero F∈E_− also has at mostN positive zeros, since0 is additionally a mandatory root. Thus each is an N+1-dimensional Chebyshev system on the positive half interval.

A low even potential is cos²(πx/L)P(cosθ), θ=2πx/L, with P of degree<=N. A low odd potential is cos²(πx/L)sinθ P(cosθ), again degree<=N. On0<x<L/2, cosθ is strictly decreasing and sinθ>0, while the envelope is positive. Thus any nonzero real potential in either parity block has at mostN sign changes on the half interval.

If it has m sign changes, prescribe a root of F∈E_± at each of them, and prescribe N−m further distinct positive roots OUTSIDE[0,L/2]. These are N homogeneous conditions on dimension N+1, so a nonzero solution exists. The positive-root count forces all its prescribed roots to be simple and excludes other positive roots. Its sign can therefore be chosen to match the potential throughout the half interval. Their product has strictly positive integral. By parity the full integral is twice the half integral, contradicting orthogonality to E_±. This proves injectivity in both blocks, and dimensions make each block invertible. Complex coefficients split into real and imaginary parts; the real low basis is stable under both. Therefore the full2N+2 extra-moment matrix is invertible.

The high kernel and low space are both reflection invariant. Uniqueness of the moment correction then proves projection/reflection commutation. The full Weil form commutes with reflection because its Archimedean symbol is even and all prime shifts occur symmetrically. Hence its low, high and mixed costs split into separate even and odd blocks. This does NOT prove the minimum lies in the even block, simplicity of any eigenvalue, either block's positivity, or the required global Schur budget.

## Concrete balanced142-moment complement at width6/5

Choose N=69, p=q=71, total order n=142. The Hermite divided-difference estimate of the original manuscript is unchanged except for the improved factorial exponent. With R=3/5,T=85,

ε_142 < 68*(260109/100)^142/(142!)² <1/10000.

The original exact digamma/prime constants give w(85)>103/40, w(0)>−6, A_R<9/4. Therefore

Q(V)>[(103/40)(9999/10000)−6/10000−9/4]||V||²
    =(129657/400000)||V||²>(8/25)||V||².

The companion exact-rational addendum checker verifies these constants. It checks arithmetic only, not the Hermite theorem or actual source transport. The local full positivity at width6/5 is already covered by source L43 plus the written rough-domain transport; this construction is useful because it extends as a parity-compatible finite correction for arbitrary support, with N allowed to grow.

Precision note for this addendum and the preserved original manuscript: every strict function inequality Q(V)>c||V||² is intended for V!=0. The universal coercivity statement uses Q(V)>=c||V||² and includes V=0. Strict inequalities between numerical constants remain strict. This zero-case clarification changes no source bytes or receipts of the original packet.
