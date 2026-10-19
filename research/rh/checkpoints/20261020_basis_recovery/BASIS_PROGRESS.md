# Exact source basis progress

The generic back-substitution theorem is uniform in the dimension and in every field. Three Frobenius lemmas control real matrices on complex vectors without analytic assumptions. All four compile natively with standard axioms only.

The unchanged source `certR` is upper triangular with nonzero diagonal (two kernel computations). The exact source declarations `rCoeff`, `R_basis` and `normSqCoeffs` yield five additional native checked basis lemmas in an extracted import context. Sequential elaboration resolves the earlier memory-killed exported-module attempt; this is not a full native replay of the analytic import graph.

`CvSProjectedBasisL12V1` applies these facts to the existing actual CvS consumers. Its three consumer declarations await full-context CI. No certificate integer or analytic definition was changed. `hRsurj` and `hRnorm` are discharged using the actual basis and its explicitly defined squared Frobenius budget.

The checked-source consumer still has the explicit instance `[Fact (CvSProjectedEntryL12V1.bigCheck = true)]`. There is no supplied instance and no claim of unconditional entry certification. The low-block consumer also retains the actual row budget and scalar Schur gap. These fixed-window results do not supply the universal producer required for RH.
