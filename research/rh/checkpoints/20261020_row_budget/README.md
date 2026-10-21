# Relative CvS row-budget certificate recovery

A new exact finite certificate for a 139-dimensional interval matrix passed Lean 4.33.1 kernel computation in 96.35 seconds. It uses the unchanged packed checker definitions. `row_budget_check_true` has only propext; `row_budget_margin_positive` has no axioms. See the machine receipt and full output.

The data were constructed for the proposed relative row budget at L = 6/5, NP = 150, epsilon = 1, far tau bound 13, kappa = 40. All 150 tau inputs come from the original and R1 Lean rational boxes. Q96 integer interval products round outward; the final interval matrix rounds outward to Q80. A rational projection is proposed by floating least squares, an eigenvalue hint proposes the shift, and Decimal Cholesky proposes an integer factor. Only exact integers and the Lean kernel decide acceptance.

The positive margin is 335194336046880346478 / 2^80. The interval arithmetic construction is an exact Python experiment. It is not yet a Lean proof that these intervals enclose the actual CvS residual/tail matrix. In particular this checkpoint does NOT prove the remaining hB premise, a whole window, or RH. The missing bridge is explicit: write the actual finite residual plus gramTail in source basis coordinates, then establish every output interval using source tau/diag/pi bounds and the uniform product lemmas.

The projection is specified in transformed source coordinates: residual rows are 2*pi*CvS*X - X*Lambda, with Lambda an exact Q48 rational witness. To use the original coefficients, surjectivity of R_basis provides c = R_basis v and lam c = R_basis (Lambda v). No correctness of the float projection is assumed.
