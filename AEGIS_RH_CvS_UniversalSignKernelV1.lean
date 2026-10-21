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

import AEGIS_RH_CvS_Finite_KernelProbeV1
import FormalConjecturesUtil.FixedWindowLimitBridge

open Filter Topology
open AEGIS.CvSProjectedSchurBridgeL12V1
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCvSUniversalSignKernelV1

/-- Convergence of nonnegative certified CvS forms transfers sign to
the real limit. The same-object convergence input remains explicit. -/
theorem universal_nonnegative_of_projected_sequence
    {G : Type*} (zeroSide : G → ℝ)
    (hrepresentation : ∀ g : G,
      ∃ (M : ℕ → ℕ) (v : ℕ → Fin 139 → ℂ),
        (∀ j, 3 ≤ M j) ∧
        Tendsto (fun j => projectedQ (M j) (v j))
          atTop (𝓝 (zeroSide g))) :
    ∀ g : G, 0 ≤ zeroSide g := by
  intro g
  obtain ⟨M, v, hM, hconv⟩ := hrepresentation g
  exact FormalConjecturesUtil.FixedWindowLimitBridge.nonneg_of_tendsto_lower_bound
    (a := fun j => projectedQ (M j) (v j))
    (lower := fun _ => (0 : ℝ))
    (A := zeroSide g)
    hconv tendsto_const_nhds
    (fun j => AEGIS.RHCvSKernelFiniteV1.certified_source_projectedQ_nonneg
      (M j) (hM j) (v j))

end AEGIS.RHCvSUniversalSignKernelV1

#print axioms AEGIS.RHCvSUniversalSignKernelV1.universal_nonnegative_of_projected_sequence
