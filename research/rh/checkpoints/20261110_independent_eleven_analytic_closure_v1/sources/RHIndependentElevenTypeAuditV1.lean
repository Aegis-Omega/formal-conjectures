import RHIndependentElevenCompositionV1

/-!
Read-only final type and transitive axiom probes for the restricted
independent-eleven theorem. This file proves no additional mathematics
and makes no RH claim. Its output is evidence only when actually run
against the source-bound freshly compiled F module.
-/

set_option pp.universes true
set_option pp.fullNames true

#check @AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive
#print axioms AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive

#check @AEGIS.RHIndependentElevenCompositionV1.all_independent_eleven_mixed_bounds
#print axioms AEGIS.RHIndependentElevenCompositionV1.all_independent_eleven_mixed_bounds

#check @AEGIS.RHIndependentElevenCompositionV1.norm_le_sqrt_energy_of_scaled_mean
#print axioms AEGIS.RHIndependentElevenCompositionV1.norm_le_sqrt_energy_of_scaled_mean
