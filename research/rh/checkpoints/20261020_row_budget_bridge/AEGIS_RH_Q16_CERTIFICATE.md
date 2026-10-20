# Exact arithmetic certificate

The PR89 Q16 data remain D=116142, conservative row=57430 and optimized row=46688. Exactly (116142-57430)/65536=7339/8192>0 and (116142-46688)/65536=34727/32768>0. The latter requires its optimized Schur hypotheses. These finite/local budgets are not a universal producer.

The new row experiment uses Q96 for interval operations and Q80 for the final matrix box. Every lower endpoint is floored and every upper endpoint is ceiled. Q96 to Q80 divides integer endpoints by 2^16 outward. Source projected intervals at Q64 are embedded at Q96 by multiplying endpoints by 2^32, exactly. The original rational R denominator is 2^40; its three-point second difference has denominator 2^42. Projection Lambda has denominator 2^48 and is merely a proposed exact witness.

For interval matrices, the exact midpoint-radius product uses m=floor((lo+hi)/2), r=max(m-lo,hi-m), central integer product A0*B0 and radius |A0|*rB+rA*|B0|+rA*rB. Divide by 2^96 outward. A symmetric hull takes the smaller lower and larger upper of the two orientations; this only widens bounds. Gram kernel entries are exact rational harmonic differences, with the proved rational diagonal upper bound.

The new 139x139 certificate factors the generated interval C=40*Q_projected-B_projected at NP=150, epsilon=1 and far |tau|<=13. Its exact integer shift is eps=1208196817027810721792, residual row budget eta=873002480980930375314. The kernel checks the packed factor against every interval and proves eps-eta=335194336046880346478>0. Its positive rational margin is this numerator divided by 2^80. Base, bound, all factor/interval entries and projection integers are in ROW_BUDGET_INPUTS.zip. Packing digit width is derived to exceed n^2*(2B)^2; no fixed-width overflow is assumed.

Float least squares, a float eigenvalue hint and Decimal Cholesky propose witnesses only. Python exact integers and then the Lean kernel decide their validity. The generator's interval model still needs formal correspondence to the actual source definitions before this certificate proves hB. This Q80 result is separate from the Q16 constants and the historical Hilbert H140 stress test.

## Verified bridge in this continuation

The arbitrary-precision outward dot/matrix product, congruence, interval hull, downward rescaling and exact upward embedding now have native Lean soundness proofs. The complete envelope has an explicit finite tableCheck premise. No positive margin was increased, no stored factor changed and no generated interval was narrowed. The monolithic computational attempt has status RESOURCE_TERMINATED_NOT_VERIFIED. Three smaller exact staged computations pass; this is not a claim for all output entries.

## Exact source input arithmetic at a1862b9b

The new source input layer retains arbitrary p, including Q96. Integer division uses lo/d rounded down and hi/d rounded up for d>0; for d<0 it divides by -d, reverses and negates endpoints. Its two soundness theorems pass natively. The pi enclosure is the established rational [314159265358979323846/10^20,314159265358979323847/10^20]. The frequency factor is enclosed by [-25*piHi^2*n^2/9-1/4,-25*piLo^2*n^2/9-1/4], then multiplied by the exact signed second difference w/2^42 with outward rounding. The factor L/pi is enclosed by [(6/5)/piHi,(6/5)/piLo], and its square uses the original interval multiplication. These five frequency-input roots pass natively. No Q16 or Q80 positivity margin or data was altered. The actual source-input application remains separately gated by its original-import CI.

## First complete Q80 output entry

The exact stored target is [230447228664518330681051593, 230447240865162189386044426], interpreted at scale 2^-80. Its complete original-envelope calculation now passes the native kernel through proved list-execution identities. Q00, X0, T, G, Z0 and LP2 are unchanged from the preserved CELL0_INPUTS.json. New GX0/GDX0 values are untrusted intermediate witnesses, each checked by the kernel. This establishes one closed output equality and does not enlarge the positivity margin or supply missing analytic input identifications. The mixed execution theorem covers two distinct columns without changing the interval operations or rounding.
