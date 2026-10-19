# Exact projected CvS transport

The transport is finite congruence, with the source convention
`v_i * conj(v_j) * A_ij`. Put `P(k,j) = atomWeight j k` and
`R(j,i) = rCoeff j i`. The source definitions give `X = P R` and
`R_basis v = R v`. The congruence therefore uses `R`, without transposition.
No symmetry, positivity, interval enclosure, or invertibility is needed
for this identity.

`CvSProjectedTransportL12V1.hTransport` identifies `projectedQ M v` with
`Q_CvS M (6/5) atomCenter (R_basis v)`. Its proof:

1. Reorders the four finite sums, preserving complex conjugation.
2. Converts the real coefficient matrix to complex coefficients.
3. Uses `iw(L,k)^2 = -(2*pi*k/L)^2` and the exact three-point atom support.
4. Associates `P (R v) = (P R) v`.
5. Reindexes `Fin 141` bijectively onto the actual support union `[-70,70]`.

Both forms use `cvsEntry` itself. The factor `2*pi` belongs to the separate
conversion from the matrix form to the analytic energy integral.

The two `_of_transport` consumers remove `hTransport` from the previous
coercivity and low-block Schur interfaces. They retain entry enclosure,
basis surjectivity, basis norm, trace gap, and mixed-row budget hypotheses.
They certify no window family or unconditional RH theorem.

The accompanying repair of `CvSProjectedSchurBridgeL12V1` opens the namespace
containing `Im` and makes multiplication commutativity explicit in the two
division inequalities. The mathematical statements are unchanged.
No bytes in the packed certificate or its `certR`, `certL`, or `certI` data
are changed.

## Validation scope at submission

Source baseline: `8a8e902e0baa48413ec24cb6c1e92b47fe391497`.
Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The four generic congruence lemmas pass native Lean with warnings as errors
and only `propext`, `Classical.choice`, and `Quot.sound`. An independent
reviewer reproduced that run. A parameterized native pilot of the complete
frequency/coefficient/congruence/reindexing proof passes for an arbitrary
real kernel, arbitrary real basis matrix, and arbitrary real angular
constant. This pilot is a separate algebra test, not the actual analytic
import context. The existing workflow now compiles that context and checks
all 14 added roots. Its exact-commit CI result is authoritative for the
concrete source composition; local pilot success is not a substitute.
