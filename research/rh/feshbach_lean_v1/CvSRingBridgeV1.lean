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
import CvSQuadV1
import RHKreinZetaBridgeV3

/-!
# The CvS matrix for the `krein_ring_v1` symbol `ScertM` (CvS step 5.5, ring tree)

`RHKreinZetaBridgeV3.ScertM M t = Psi t − log π − ∑_{j<M} ppw j · cos(t log(j+1))` is
`CvSQuadV1.qsym M ppw`, because `Psi t − log π = h₊(t)`. So for a trigonometric polynomial
`G = ∑_{n ∈ F} v_n e_n` on `[0, L]`,

`(1/4π) ∫ ScertM M (|𝓕G(t/2π)|² + |𝓕G(−t/2π)|²) = ∑_{n,m} v_n conj(v_m) M_nm`,

`M_nm = (1/2π) (∫ h₊ · cosB_nm − π ∑_{j<M} ppw j · B_nm(min(log(j+1), L)))`, with the archimedean
integrals given by `CvSQuadV1.hplus_cosB_diag` and `CvSQuadV1.hplus_cosB_off`.
-/

open MeasureTheory Complex Set Real
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace AEGIS.CvSRingBridgeV1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSPrimeBlockV1 AEGIS.CvSMassV1 AEGIS.CvSQuadV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3 AEGIS.WeilCriticalLineKreinFormV1

theorem psi_sub_log_eq_hplus (t : ℝ) : Psi t - Real.log Real.pi = hplus t := by
  have hz : zt t = (1 / 4 : ℂ) + (t : ℂ) * I / 2 := by
    unfold zt; push_cast; ring
  rw [Psi, hz, hplus]

theorem scertM_eq_qsym (M : ℕ) : ScertM M = qsym M ppw := by
  funext t
  rw [ScertM, qsym, ← psi_sub_log_eq_hplus]

/-- **The CvS matrix for `ScertM`.** -/
theorem scertM_quad_trigPoly {L : ℝ} (hL : 0 < L) (F : Finset ℤ) (v : ℤ → ℂ) (M : ℕ) :
    (((1 / (4 * Real.pi)) * ∫ t, ScertM M t *
        (Complex.normSq (𝓕 (trigPoly L F v) (t / (2 * Real.pi))) +
          Complex.normSq (𝓕 (trigPoly L F v) (-t / (2 * Real.pi))))) : ℝ) =
      ∑ n ∈ F, ∑ m ∈ F, v n * conj (v m) *
        (((1 / (2 * Real.pi)) * ((∫ t, hplus t * cosB L n m t) -
          ∑ j ∈ Finset.range M, ppw j *
            (Real.pi * blockFn L n m (min |Real.log ((j + 1 : ℕ) : ℝ)| L))) : ℝ) : ℂ) := by
  rw [scertM_eq_qsym, quad_trigPoly hL F v _ (qsym_cosB_integrable hL M ppw)]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [qsym_cosB_integral hL M ppw n m]

end AEGIS.CvSRingBridgeV1

#print axioms AEGIS.CvSRingBridgeV1.psi_sub_log_eq_hplus
#print axioms AEGIS.CvSRingBridgeV1.scertM_eq_qsym
#print axioms AEGIS.CvSRingBridgeV1.scertM_quad_trigPoly
