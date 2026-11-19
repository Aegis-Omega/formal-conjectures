# Suzuki shift and resolvent proof attempts

This checkpoint continues the existing Suzuki lane. It preserves the earlier
source-composition audit and existing global RH consumers. It does not claim
a new RH equivalence or an unconditional RH proof.

## Mathematical results

1. For the actual arithmetic family in Suzuki 2206.03682v4, the exact first
   omega variation has an explicit finite-prime/integral expression. It is
   strictly positive for every real omega on a nonempty interval adjacent
   to zero. Thus the proposed descending-monotonicity proof of unshifted
   positivity fails for the actual object. The derivation and first-prime
   activation analysis are in `omega_attack/OMEGA_VARIATION_ATTACK.md`.
2. For the actual finite-a operators in Suzuki 2606.09096v3, an explicitly
   controlled admissible large-shift sequence has normalized Herglotz limit
   `i`. This differs from the zeta target even on its Euler-product half-plane.
   Near-ground shifts instead retain an inverse-amplified ground projection.
   See `resolvent_attack/RESOLVENT_SAFE_REGION_ATTACK.md`.
3. Inverting a positive arithmetic shift and discarding its positive old
   history gives a valid lower bound. For the actual Suzuki family that
   bound is eventually negative uniformly over every `a>=1/2`, including
   time-dependent choices of a. Its exact normalized leading term is
   `-exp(-2)`. Thus retaining the full
   historical cancellation is necessary for this inverse-transport attempt.
   The fixed-a derivation and its subsequent uniform strengthening are in
   `omega_attack/RECENT_HISTORY_INVERSE_OBSTRUCTION.md` and
   `omega_attack/UNIFORM_RECENT_HISTORY_OBSTRUCTION.md`.

These reject three particular proposed transitions. They do not exclude all
shift choices, all differential inequalities, or another AEGIS proof route.

## Verification

The two written arguments were reviewed separately. The first author's Arb
checker ran at 256 bits. Root replayed it at 384 bits and reproduced all five
strict signs and the first-prime one-sided slopes. This was a second execution
of the same checker; the analytic derivations were checked independently.
Neither analytic result has a Lean replay in this checkpoint.

`SOURCE_MANIFEST.json` identifies the primary-source bytes and source sections.
The PDFs are not copied into this archive. Obtain the exact cited versions and
verify their SHA-256 before replay. For the supplied interval checker, use
Python with `python-flint==0.9.0`, then run from the extracted archive:

    python3 omega_attack/omega_variation_enclosure_v1.py --source-pdf /path/to/2206.03682v4.pdf --precision 384 --output /new/path/replay.json

The checker refuses to overwrite an existing receipt and rejects the wrong
primary-source hash. It contains explicit exception gates; the finite series
tail is included with outward rounding. The checker proves only its reported
finite numerical statements. The analytic near-zero sign proof does not rely
on those samples.

## Existing work and continuation

The prior optimized-weight shape composition is already published at commit
`44b78e21321a9a96ca714e540e04ee46c84fc63e`, under
`research/rh/checkpoints/20261103_weighted_independent_shapes_reuse_v1/`.
It supplies the previously assumed mixed bound for the stated eleven-window
independent-shape family. It is not redone or used as unrestricted positivity.

The repository already has `research/rh/assembly/RHProofGraphExport.lean`.
This checkpoint adds a small AND/OR graph delta, not a replacement exporter or
an exhaustive census. `RH_FINAL_EVIDENCE.json` records one selected continuation
and keeps `rh_proven=false`. The complete AEGIS corpus is not declared exhausted.
