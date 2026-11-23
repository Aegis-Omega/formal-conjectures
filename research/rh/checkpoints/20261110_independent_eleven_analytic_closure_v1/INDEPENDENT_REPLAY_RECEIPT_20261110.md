# Independent from-source replay of the eleven-window closure (commit 22c6925)

Date: 2026-11-10. Evidence kind: `lean_kernel`. RH status: OPEN (unchanged).

This records a second, independent replay of the packet in this directory. The packet's own
README states that a full fresh replay of all imports had not finished; this run completed it.

## Input

- Packet: `AEGIS_PR92_Independent_Eleven_Kernel_20261110.zip`, 1,018,998 bytes,
  SHA-256 `014879d4bc7dc3e114666a9eb05c91d2f3ae87ff992793bc002a0109eaec5d6f` (matches the claim).
- `SHA256SUMS` inside the packet: all entries verified before compiling.
- Lean 4.33.1, githash `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (prebuilt cache; Mathlib itself was not rebuilt).

## Method

Every module of the packet's `BUILD_ORDER.txt` was compiled from source, in order, with the same
call as the packet's `replay.sh`:

    lean --trust=0 --threads=4 --memory=12288 --root=closure -o <lib>/<Module>.olean closure/<Module>.lean

No `.olean` from the packet or from any earlier run was reused for the 186 modules.

## Result

- Compiled: 186 / 186 modules. Wall time 1388 s. Slowest: `RHHatCoxClass693V13`, 498 s.
- Logs with `declaration uses 'sorry'`: 0. Logs with `error`: 0.
- `#print axioms` for `actual_independent_eleven_coercive`, `all_independent_eleven_mixed_bounds`
  and `norm_le_sqrt_energy_of_scaled_mean`: `[propext, Classical.choice, Quot.sound]`.
- `leanchecker --verbose RHIndependentElevenCompositionV1`: exit 0 (484 s).

## What this does and does not establish

Established: the theorem `AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive`,
with the type in `evidence/ACTUAL_FINAL_TYPE.txt`, is accepted by the Lean kernel from the packet's
sources with only the three standard axioms.

Not established: the Riemann Hypothesis. The catalog statement
`FormalConjectures/Millennium/RiemannHypothesis.lean` still contains `sorry`, and no unconditional
producer for the remaining universal hypotheses exists.
