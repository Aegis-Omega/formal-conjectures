## Full-table continuation

The complete ordered 139 by 139 output comparison now passes the native kernel, replacing the earlier first-column-only scope. `CvSFullTableClosureV1.full_table_contains` relates every checked entry to the original Q96 interval envelope, with no unproved output check. `real_envelope_mem` transfers all entries to Q80, retaining exactly six real input-membership families.

`CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs` composes the complete finite table with the original complex interval-box positivity theorem. For every complex vector v it gives

```
delta * sum_i ||v_i||^2 + budgetEnergy(z, tailMatrix(x,g,t,lp2), v)
  <= 40 * Re sum_ij v_i * conjugate(v_j) * q_ij

delta = 167597168023440173239 / 604462909807314587353088 > 0.
```

Its premises are symmetry of q and g and the explicit Q96 memberships of q, x, g, t, z and lp2 in the unchanged literal inputs. It has no output-table, matrix-positivity or RH premise. These memberships still need to be connected to the original CvS definitions; the theorem must not be described as an unconditional actual-CvS bound before that connection is proved.

All 139 input-column caches, 278 original Gram-column products and 19321 ordered output entries compiled. Signed packing includes bounds, lengths and carry control. The source JSON reconstructs byte-for-byte from the original stored Q48 projection and source tables without executing a floating fit. Existing first-column proofs now supply the weighted identities directly, avoiding an unnecessary global re-evaluation. Only proof composition changed; no interval endpoint changed.

The selected new graph has 12 roots, 19752 declarations and 984 located source modules. It has no missing dependency or proof cycle and only the standard three axioms. The 451 inductive/constructor metadata groups are separately condensed. The earlier 102-root graph and original-import CI receipts remain historical evidence in Git and the archived native graph; their scopes are not relabelled.

# Exact integer and interval certificates

## Q16.16 source budgets

The fixed scale is `Q=65536`, diagonal numerator `D=116142`, conservative row numerator `57430`, optimized row numerator `46688`. Exact rational identities are

```
(116142-57430)/65536 = 7339/8192 > 0,
(116142-46688)/65536 = 34727/32768 > 0.
```

The second requires the actual optimized Schur hypotheses. Neither is a universal mixed-budget producer. `RHActualElevenLatticeV1.q16_integer_certificate` checks the integer rounding budget. Its separate `q16_budget_exact` is literally

```
116142/65536 - 2*sum(k=1..10) q16Cost(k) = 641/32768.
```

It must not be confused with the sharper per-row margin obtained from `q16_row_bound`. The diagonal numerator is a conservative lower bound; upper mixed costs are rounded outward. The exact Q16 identities and the Q80 margin are independently checked in `packed_execution/ExactBudgetRegression.lean`.

## Unchanged Q96-to-Q80 finite certificate

The projected certificate is 139-dimensional; this differs from the Hilbert H140 stress test. The low Fourier dimension is 141 and the residual dimension is 301. The interval envelope uses Q96, the proposed projection uses exact Q48 rationals, and the stored final matrix uses Q80. An existing Q64 interval embeds exactly by multiplying its endpoints by 2^32. Q96 to Q80 divides the lower endpoint downwards and upper endpoint upwards by 2^16.

For intervals A,B use midpoint `floor((lo+hi)/2)` and radius `max(mid-lo,hi-mid)`. A dot has integer center `sum midA*midB` and radius `sum (abs(midA)*radB+radA*abs(midB)+radA*radB)`, then floors/ceils by 2^96. Hull takes the smaller lower and larger upper endpoint. Negative integer division reverses and negates endpoints as proved in `CvSIntervalDivideV1`. No floating estimate enters as a theorem.

The original factor certificate has

```
eps = 1208196817027810721792
eta =  873002480980930375314
eps - eta = 335194336046880346478 > 0
margin = (eps-eta)/2^80.
```

The base is `40564819207303340847894502572032` and factor bound is `15795288160149`. Full original numerical source `CvSRelativeRowCertificateL12V1` was recompiled: row_budget_check_true uses propext; row_budget_margin_positive uses no axioms. The complete packed soundness body, including its complex form, also compiles with standard axioms. Numerical matrix positivity remains conditional on correct enclosures of the actual entries.

The historical fourteen first-column batches checked 139 entries. The complete extension now checks all 19321 ordered entries, preserving every input number and outward direction, with original-import CI 39505154095 PASS. Missing weighted-column data and a false zero target are both rejected by kernel tests.

## Analytic input enclosures and packed reuse

The source pi interval is `[314159265358979323846/10^20,314159265358979323847/10^20]`. The frequency factor has endpoints `-25*piHi²*n²/9-1/4` and `-25*piLo²*n²/9-1/4`; signed w/2^42 multiplies this through the proved outward interval multiplication. L/pi is enclosed using the reversed positive pi endpoints. Original-import CI now validates the source application through actual sourceZ for M≥3 and an explicitly enclosed projection.

The new packed interval theorem uses four existing signed packed dot products, and proves exact equality to the old evaluator. For length n and component bound B the carry hypothesis is `n*n*(2*B*(2*B)) < base`; this prevents digit collisions. Signed values are shifted by B, and the original gramEntry correction removes both shift cross terms and n*B² exactly. This is arbitrary-precision Nat/Int arithmetic, without fixed-width overflow or native_decide.

The actual Z0 pilot has n=301, B=2^128 and base=2^280. Every component bound, the carry inequality, all six forward/reverse packed natural numbers and the resulting interval are kernel checked. The exact Q96 self-dot is

```
[90409755428085542605520956409, 90409777030268093176323279969] / 2^96.
```

A modified packed coefficient is rejected. The pilot takes 3.440 seconds; this verifies correctness and is not a measured full-matrix scaling claim. None of these constants is an enclosure of an arbitrary zeta-zero ordinate.

## Exact source normalization continuation

The actual cross kernel is 2*pi times the signed low-block kernel. The new source Q route checks containment of inverseTwoPi * dot96(X-column,Y-inner-column) in the stored Q interval. inverseTwoPi is lpInterval96 times rationalRange96(5/12,5/12); lp_mem and exact rational algebra prove membership of 1/(2*pi). No float or inward rounding is introduced. All19321 normalized numerical comparisons and a rejection of the unnormalized 00 entry pass the native kernel. Their actual analytic membership producer awaits targeted replay after the aggregate join failure in CI 39514026659.
