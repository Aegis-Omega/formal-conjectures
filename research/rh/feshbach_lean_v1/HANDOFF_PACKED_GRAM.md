# Handoff: packed Gram certificates → finishing the window certificate (for the next assistant)

Branch `proof/rh-feshbach-schur-v1`, dir `research/rh/feshbach_lean_v1`. Lean v4.33.1, Mathlib pinned
in the workflow. This is NOT a proof of RH: it is a Lean reduction of one window (L ≈ 1.2) of a
Weil-positivity certificate, and positivity for one window does not imply all windows.

## Rules (must keep)
- No `sorry`, `admit`, `axiom`, `native_decide` (adds `Lean.ofReduceBool`). Use `decide +kernel`.
- Every new theorem goes into the CI axiom audit (`.github/workflows/rh-feshbach-schur-v1.yml`);
  allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Do not modify existing proof files; add new files. Do not merge to main. Never claim RH.
- Run the same commands as CI locally before pushing.

## What exists
- `CvSRowTailV1.window_of_certificate_tail` (krein-ring job): the window certificate with only
  numerical hypotheses left: pointwise Krein inequality, trace integral, finitely many rows
  |m| ≤ NP plus `rowTail` (`hfin`), and the finite matrix inequality (`hlow`).
- `CvSPackedGramV1` (compile job, imports `critical_line_v1/RHFixIntervalV1`): sound kernel checker
  for positivity of a real symmetric matrix known only through `Iv` enclosures at scale 2^-q:
  `check b B n eps eta L I = true` (by `decide +kernel`) ⇒
  `quad_lower_complex : (eps-eta) Σ‖c_i‖² ≤ 2^q Re Σ c_i conj(c_j) A_ij`.
  L·Lᵀ uses packed (Kronecker) multiplication: `packDot_eq`. Example: `hilbert8_posDef`.
- `tools/packed_gram_cert.py N Q`: untrusted stdlib generator (Hilbert). CI checks H_140
  (q = 1508, λ_min ≈ 3.9e-212); locally the kernel took 143 s; n = 20/40/70: 1/4.9/18 s.
  H_140 is only a stress test of the checker, not a CvS/Weil matrix.
- These are the artifacts `H140_RECOVERY_REPORT.md` could not find; they are now in the repo.
  `quad_lower` uses `CvSResidualCertificateV1.residual_quadratic_le` (Codex) for the row-sum
  bound, so there is one Gershgorin lemma, not two.
- τ_k at L = 6/5 (krein-ring job): `CvSTauL12V1.source_integral_mem` (∫ h₊ S_k, arctan tail,
  `CvSArctanTailV1`, `CvSTauSourceV1`) and `CvSTauPrimeL12V1.tau_mem` (full τ_k for every prime
  cutoff M ≥ 3; only p = 2, 3 have nodes inside [0, 6/5]): boxes of width ≤ 2e-7 for
  k = 1..70, `tau_neg`/`tau_zero` for k ≤ 0. With `CvSRowTailV1.cvsEntry_off` this gives every
  off-diagonal entry of the L = 1.2 low block. Generators: `tools/gen_tau.py`,
  `tools/gen_tau_prime.py` (untrusted, reproduce the data exactly).

## Next steps (in order)
1. Enclosures of the matrix entries (the real wall): off-diagonal entries are done via τ_k (above).
   Still open: the diagonal `cvsEntry M L n n` (`hplus_diag_integral`: h₊(2πn/L) needs Re ψ,
   see `RHKreinDigammaSharpTailV1`/`RHEulerGammaSharpBaseV1`, plus the series
   Σ (1 − e^{−c_j L})(c_j² − ω²)/(c_j² + ω²)²) and the prime part of the diagonal. Generic notes
   (integrals ∫ h₊·cosB with digamma terms, τ_k, ppw = Λ(n)/√n weights, log, arctan). Check
   existing enclosure modules first (`critical_line_v1`: RHExpEnclosureV1, RHPi40V1/RHPi80V1 on
   the consolidated branch) before writing new ones. Needed: Taylor series with remainder and
   quadrature with explicit error.
2. Bridge `hlow` to `quad_lower_complex`: index the low frequencies by `Fin n`, build `A` from
   `cvsEntry` (symmetric by `CvSRowTailV1.cvsEntry_symm`), prove `Iv.Mem` from step 1.
3. `hfin`: rectangular generalisation of `check` (rows of length m ≠ n) and an interval Gram
   (mid ± rad: RmidᵀRmid plus |Rmid|ᵀrad + radᵀ|Rmid| + radᵀrad, all packed), then certify
   `Brow − Gram ≥ 0` with `check`.
4. Krein pointwise inequality and trace integral: same enclosure machinery.
5. Performance: the kernel costs ~1–4 ms per matrix entry (reduction steps, not GMP); fine up to
   n ≈ 140. Reduce steps per entry only if needed.

## Local commands
    export PATH=$HOME/.elan/bin:$PATH
    OUT=$(mktemp -d); export LEAN_PATH="$OUT:$(lake env printenv LEAN_PATH)"
    lean -o "$OUT/RHFixIntervalV1.olean" research/rh/critical_line_v1/RHFixIntervalV1.lean
    lean -o "$OUT/CvSResidualCertificateV1.olean" research/rh/feshbach_lean_v1/CvSResidualCertificateV1.lean
    lean -o "$OUT/CvSPackedGramV1.olean" research/rh/feshbach_lean_v1/CvSPackedGramV1.lean
    python3 research/rh/feshbach_lean_v1/tools/packed_gram_cert.py 140 1508 > /tmp/H140.lean
    lean /tmp/H140.lean
