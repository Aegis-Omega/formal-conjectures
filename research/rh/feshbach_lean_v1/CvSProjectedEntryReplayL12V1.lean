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

import CvSProjectedEntryFastL12V1

/-!
# Kernel replay of the projected L = 6/5 entry certificate

The five row chunks of `chunkCheck` are checked by the kernel one after another (`Elab.async false`
keeps one kernel cache alive at a time). This discharges `Fact (bigCheck = true)`, so
`projectedEntry_mem_certI` holds unconditionally. Not RH.
-/

open AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedEntryL12V1 AEGIS.CvSProjectedEntryFastL12V1

namespace AEGIS.CvSProjectedEntryReplayL12V1

set_option maxRecDepth 100000
set_option Elab.async false

theorem chunk0_true : chunkCheck 0 28 = true := by decide +kernel
theorem chunk1_true : chunkCheck 28 28 = true := by decide +kernel
theorem chunk2_true : chunkCheck 56 28 = true := by decide +kernel
theorem chunk3_true : chunkCheck 84 28 = true := by decide +kernel
theorem chunk4_true : chunkCheck 112 27 = true := by decide +kernel

theorem bigCheck_true : bigCheck = true :=
  bigCheck_of_rows (rows_ok_of_chunks chunk0_true chunk1_true chunk2_true chunk3_true chunk4_true)

instance bigCheck_fact : Fact (bigCheck = true) := ⟨bigCheck_true⟩

/-- Every projected entry lies in its `certI` interval (L = 6/5, all `M ≥ 3`). -/
theorem projectedEntry_mem_certI {M : ℕ} (hM : 3 ≤ M) :
    ∀ i j : Fin 139, (AEGIS.CvSPackedGramV1.Im certI i.val j.val).Mem certQ
      (projectedEntry M i j) :=
  projectedEntry_mem_certI_of_check hM

/-- The packed lower bound with its interval hypothesis discharged. -/
theorem projected_lower_L12 {M : ℕ} (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    ((certEps - certEta : ℤ) : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤
      2 ^ certQ * (∑ i, ∑ j,
        c i * (starRingEnd ℂ) (c j) * (projectedEntry M i j : ℂ)).re :=
  projected_lower_L12_of_check hM c

end AEGIS.CvSProjectedEntryReplayL12V1

#print axioms AEGIS.CvSProjectedEntryReplayL12V1.bigCheck_true
#print axioms AEGIS.CvSProjectedEntryReplayL12V1.projectedEntry_mem_certI
#print axioms AEGIS.CvSProjectedEntryReplayL12V1.projected_lower_L12
