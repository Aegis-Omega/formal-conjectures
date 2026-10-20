# Exact arithmetic certificate

The PR89 Q16 data remain D=116142, conservative row=57430 and optimized row=46688. Exactly (116142-57430)/65536=7339/8192>0 and (116142-46688)/65536=34727/32768>0. The latter requires its optimized Schur hypotheses. These finite/local budgets are not a universal producer.

The new row experiment uses Q96 for interval operations and Q80 for the final matrix box. Every lower endpoint is floored and every upper endpoint is ceiled. Q96 to Q80 divides integer endpoints by 2^16 outward. Source projected intervals at Q64 are embedded at Q96 by multiplying endpoints by 2^32, exactly. The original rational R denominator is 2^40; its three-point second difference has denominator 2^42. Projection Lambda has denominator 2^48 and is merely a proposed exact witness.

For interval matrices, the exact midpoint-radius product uses m=floor((lo+hi)/2), r=max(m-lo,hi-m), central integer product A0*B0 and radius |A0|*rB+rA*|B0|+rA*rB. Divide by 2^96 outward. A symmetric hull takes the smaller lower and larger upper of the two orientations; this only widens bounds. Gram kernel entries are exact rational harmonic differences, with the proved rational diagonal upper bound.

The new 139x139 certificate factors the generated interval C=40*Q_projected-B_projected at NP=150, epsilon=1 and far |tau|<=13. Its exact integer shift is eps=1208196817027810721792, residual row budget eta=873002480980930375314. The kernel checks the packed factor against every interval and proves eps-eta=335194336046880346478>0. Its positive rational margin is this numerator divided by 2^80. Base, bound, all factor/interval entries and projection integers are in ROW_BUDGET_INPUTS.zip. Packing digit width is derived to exceed n^2*(2B)^2; no fixed-width overflow is assumed.

Float least squares, a float eigenvalue hint and Decimal Cholesky propose witnesses only. Python exact integers and then the Lean kernel decide their validity. The generator's interval model still needs formal correspondence to the actual source definitions before this certificate proves hB. This Q80 result is separate from the Q16 constants and the historical Hilbert H140 stress test.

## Verified bridge in this continuation

The arbitrary-precision outward dot/matrix product, congruence, interval hull, downward rescaling and exact upward embedding now have native Lean soundness proofs. The complete envelope has an explicit finite tableCheck premise. No positive margin was increased, no stored factor changed and no generated interval was narrowed. The monolithic computational attempt has status RESOURCE_TERMINATED_NOT_VERIFIED. Three smaller exact staged computations pass; this is not a claim for all output entries.
