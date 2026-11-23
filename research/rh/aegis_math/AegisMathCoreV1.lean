/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Batteries.Tactic.Alias
import RHWindowL118ExhaustionV1
import WeilMomentKillerPacketRangeV1
import RHWidthQuantifierObstructionV1
import RHEulerOperatorObstructionV1

/-!
# AEGIS Math, core V1

One entry point, under stable names in the namespace `AegisMath`, for results on this branch
that the Lean kernel has checked. Every name below is an `alias` of an existing theorem: this
file proves nothing new and adds no hypothesis. `CATALOG.json` next to this file lists each
entry with its source module, its statement and the CI run that checked it, together with
results of other kinds (numerical, literature, external claims, open), kept apart by kind.

* `AegisMath.Windows`: every log window with `L ≤ 11/16` has the arithmetic sign, and RH is
  equivalent to the sign on the windows `L > 11/16`.
* `AegisMath.Criterion`: the final sign residual is equivalent to RH.
* `AegisMath.MomentKiller`: every two-moment-zero packet is an image of `1/4 − ∂²`.
* `AegisMath.Obstructions`: routes that provably do not work.

Not RH.
-/

namespace AegisMath

namespace Windows

alias window_le_eleven_sixteenths :=
  AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths
alias final_sign_iff_windows_above_eleven_sixteenths :=
  AEGIS.RHWindowL118ExhaustionV1.final_sign_iff_windows_above_eleven_sixteenths
alias rh_iff_windows_above_eleven_sixteenths :=
  AEGIS.RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths

end Windows

namespace Criterion

alias final_sign_iff_rh := AEGIS.V13Scratch.final_sign_iff_rh_v13
alias no_zero_re_gt_half_of_final_sign := AEGIS.V13Scratch.no_zero_re_gt_half_of_final_sign_v13

end Criterion

namespace MomentKiller

alias exists_momentKiller_packet := AEGIS.WeilMomentKillerPacketRangeV1.exists_momentKiller_packet
alias exists_momentKiller_eq := AEGIS.WeilMomentKillerRangeV1.exists_momentKiller_eq

end MomentKiller

namespace Obstructions

alias no_common_positive_width := AEGIS.RHWidthQuantifierObstructionV1.no_common_positive_width
alias vonMangoldt_weights_do_not_imply_operator_nonnegative :=
  AEGIS.RHEulerOperatorObstructionV1.vonMangoldt_weights_do_not_imply_operator_nonnegative

end Obstructions

end AegisMath

#print axioms AegisMath.Windows.window_le_eleven_sixteenths
#print axioms AegisMath.Windows.final_sign_iff_windows_above_eleven_sixteenths
#print axioms AegisMath.Windows.rh_iff_windows_above_eleven_sixteenths
#print axioms AegisMath.Criterion.final_sign_iff_rh
#print axioms AegisMath.Criterion.no_zero_re_gt_half_of_final_sign
#print axioms AegisMath.MomentKiller.exists_momentKiller_packet
#print axioms AegisMath.MomentKiller.exists_momentKiller_eq
#print axioms AegisMath.Obstructions.no_common_positive_width
#print axioms AegisMath.Obstructions.vonMangoldt_weights_do_not_imply_operator_nonnegative
