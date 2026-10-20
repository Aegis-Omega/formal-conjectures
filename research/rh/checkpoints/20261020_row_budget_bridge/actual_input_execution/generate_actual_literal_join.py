from pathlib import Path
w=Path(__file__).resolve().parent
s='/- Actual-source input integration candidate. Requires original-import kernel replay. -/\nimport CvSActualRowInputL12V1\nimport CvSProjectedSymmetryV1\nimport CvSSourceProductAllV1\nimport CvSSourceQAllV1\nimport CvSFullBudgetJoinV1\n'
for prefix,count in [('CvSAnalyticERows',31),('CvSAnalyticXColumns',14),('CvSAnalyticGRows',15)]:s+=''.join(f'import {prefix}{i}\n' for i in range(count))
s+='import CvSAnalyticScalarInputsV1\nimport Mathlib.Tactic.FinCases\n'
s+='''open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSActualLiteralInputsV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSActualRowInputL12V1 AEGIS.CvSSourceProductAllV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSListIntervalDotV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSSourceQNormalizeV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem E_source (r : Fin 301) (k : Fin 141) :
    (eRow r).values.getD k.val ⟨0, 0⟩ = kernelBox 96 (rowIndex r) k := by
  fin_cases r
'''
for r in range(301):s+=f'  · exact AEGIS.CvSAnalyticERows{r//10}.row{r} k\n'
s+='''theorem X_source (k : Fin 141) (i : Fin 139) :
    (inputColumn i).x.values.getD k.val ⟨0, 0⟩ = xBox k i := by
  fin_cases i
'''
for i in range(139):s+=f'  · exact AEGIS.CvSAnalyticXColumns{i//10}.column{i} k\n'
s+='''theorem G_source (k l : Fin 141) :
    (AEGIS.RowBudgetListCell0Pilot.G.getD k.val []).getD l.val ⟨0, 0⟩ =
      AEGIS.CvSRationalIntervalV1.rationalRange 96
        (gramRat 150 (signedFreq k) (signedFreq l)) (gramRat 150 (signedFreq k) (signedFreq l)) := by
  fin_cases k
'''
for k in range(141):s+=f'  · exact AEGIS.CvSAnalyticGRows{k//10}.row{k} l\n'
s+='''/-- Staged interval products coincide with the already-proved actual source box formulas. -/
theorem Y_source (r : Fin 301) (i : Fin 139) : Y r i = sourceYBox 96 (rowIndex r) i := by
  rw [Y_entry, listDot_eq_dot 96 _ _ (eRow r).length_eq (inputColumn i).x.length_eq]
  change dot 96 (fun k => (eRow r).values.getD k.val ⟨0, 0⟩)
    (fun k => (inputColumn i).x.values.getD k.val ⟨0, 0⟩) =
    dot 96 (kernelBox 96 (rowIndex r)) (fun k => xBox k i)
  congr 1
  · funext k; exact E_source r k
  · funext k; exact X_source k i

theorem inner_source (k : Fin 141) (i : Fin 139) : inner k.val i =
    dot 96 (xBox k) (fun j => lambdaBox j i) := by
  rw [inner_entry, listDot_eq_dot 96 _ _ (xRow k).length_eq (lambdaColumn i).length_eq]
  change dot 96 (fun j => (xRow k).values.getD j.val ⟨0, 0⟩)
    (fun j => lambdaBox j i) = dot 96 (xBox k) (fun j => lambdaBox j i)
  congr 1
  funext j
  exact (x_transpose k j).trans (X_source k j)

theorem Z_source (r : Fin 301) (i : Fin 139) :
    (inputColumn i).z.values.getD r.val ⟨0, 0⟩ = zBox lambdaBox r i := by
  rw [Z_entry]
  unfold zBox
  split_ifs with hr
  · rw [Y_source, inner_source (⟨r.val - 80, by omega⟩ : Fin 141) i]
  · exact Y_source r i

theorem X_mem (k : Fin 141) (i : Fin 139) :
    ((inputColumn i).x.values.getD k.val ⟨0, 0⟩).Mem 96 (transformedCoeff k i) := by
  rw [X_source]
  exact transformedCoeff_mem 96 k i

theorem Y_mem (M : ℕ) (hM : 3 ≤ M) (r : Fin 301) (i : Fin 139) :
    (Y r i).Mem 96 (AEGIS.CvSActualCrossRowL12V1.sourceY M (rowIndex r) i) := by
  rw [Y_source]
  have hm : (rowIndex r).natAbs ≤ 150 := by
    unfold rowIndex
    have hr := r.isLt
    omega
  exact sourceY_mem 96 hM (rowIndex r) hm i

theorem Z_mem (M : ℕ) (hM : 3 ≤ M) (r : Fin 301) (i : Fin 139) :
    ((inputColumn i).z.values.getD r.val ⟨0, 0⟩).Mem 96 (sourceZ M lambdaReal r i) := by
  rw [Z_source]
  exact sourceZ_mem M hM lambdaReal lambdaBox lambda_mem r i

theorem G_mem (k l : Fin 141) :
    ((AEGIS.RowBudgetListCell0Pilot.G.getD k.val []).getD l.val ⟨0, 0⟩).Mem 96
      (AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l)) := by
  rw [G_source]
  exact gramUp_mem 96 150 (signedFreq k) (signedFreq l)

theorem T_mem (M : ℕ) (hM : 3 ≤ M) (k : Fin 141) :
    (AEGIS.RowBudgetStagedDotPilot.T.getD k.val ⟨0, 0⟩).Mem 96
      (AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k)) := by
  rw [AEGIS.CvSAnalyticScalarInputsV1.tau_source]
  have hk : (signedFreq k).natAbs ≤ 150 := by
    have h := k.isLt
    unfold signedFreq
    omega
  exact AEGIS.CvSTauSigned150L12V1.signed_tau_interval 96 hM (signedFreq k) hk

theorem LP_mem : AEGIS.RowBudgetListCell0Pilot.LP2.Mem 96 (((6/5 : ℝ)/Real.pi)^2) := by
  rw [AEGIS.CvSAnalyticScalarInputsV1.lp_source]
  exact AEGIS.CvSFrequencyIntervalV1.lp_squared_mem 96

/-- The actual cross kernel includes 2*pi; it must not be identified with signedEntry. -/
theorem sourceKernel_signed (M : ℕ) (k l : Fin 141) :
    AEGIS.CvSActualCrossRowL12V1.sourceKernel M (signedFreq k) (signedFreq l) =
      2 * Real.pi * signedEntry M k l := by
  unfold AEGIS.CvSActualCrossRowL12V1.sourceKernel signedEntry
  rw [AEGIS.CvSRowTailV1.cvsEntry_symm M (by norm_num : (0 : ℝ) < 6/5)
    (signedFreq l) (signedFreq k)]
  ring

theorem projectedEntry_as_Y (M : ℕ) (i j : Fin 139) :
    (∑ k : Fin 141, transformedCoeff k i *
      AEGIS.CvSActualCrossRowL12V1.sourceY M (signedFreq k) j) =
      2 * Real.pi * projectedEntry M i j := by
  simp only [AEGIS.CvSActualCrossRowL12V1.sourceY, projectedEntry, sourceKernel_signed,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem Q_mem (M : ℕ) (hM : 3 ≤ M) (i j : Fin 139) :
    (AEGIS.CvSFullTableClosureV1.Q i j).Mem 96 (projectedEntry M i j) := by
  apply mem_of_contains 96 (AEGIS.CvSSourceQAllV1.checked i j)
  apply normalize_mem
  rw [evalDot_eq (by decide : 0 < 141) (by decide : 141 ≤ 301),
    listDot_eq_dot 96 _ _ (inputColumn i).x.length_eq (AEGIS.CvSSourceQAllV1.vector j).length_eq]
  rw [← projectedEntry_as_Y M i j]
  apply dot_mem 96 _ _ (fun k => transformedCoeff k i)
    (fun k => AEGIS.CvSActualCrossRowL12V1.sourceY M (signedFreq k) j) (fun k => X_mem k i)
  intro k
  rw [AEGIS.CvSSourceQAllV1.vector_source]
  have h := Y_mem M hM (⟨k.val + 80, by omega⟩ : Fin 301) j
  have he : rowIndex (⟨k.val + 80, by omega⟩ : Fin 301) = signedFreq k := by
    unfold rowIndex signedFreq
    omega
  rw [he] at h
  exact h

/-- All literal source memberships discharged; a quantitative bound on the actual finite CvS residual. -/
theorem actual_budgetEnergy_margin (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    AEGIS.CvSStrictRowBudgetV1.margin * (∑ i, ‖v i‖^2) +
      AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy (sourceZ M lambdaReal)
        (AEGIS.CvSRealTailMatrixV1.tailMatrix transformedCoeff
          (fun k l => AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l))
          (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k)) (((6/5 : ℝ)/Real.pi)^2)) v ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (projectedEntry M i j : ℂ)).re := by
  exact AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs
    (projectedEntry M) transformedCoeff
    (fun k l => AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l))
    (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k))
    (sourceZ M lambdaReal) (((6/5 : ℝ)/Real.pi)^2)
    (AEGIS.CvSProjectedSymmetryV1.projectedEntry_symm M)
    (fun k l => gramUp_symm 150 (signedFreq k) (signedFreq l))
    (Q_mem M hM) X_mem G_mem (T_mem M hM) (Z_mem M hM) LP_mem v
end AEGIS.CvSActualLiteralInputsV1
'''
for n in ['E_source','X_source','G_source','Y_source','inner_source','Z_source','X_mem','Y_mem','Z_mem','G_mem','T_mem','LP_mem','sourceKernel_signed','projectedEntry_as_Y','Q_mem','actual_budgetEnergy_margin']:
 s+=f'#check @AEGIS.CvSActualLiteralInputsV1.{n}\n#print axioms AEGIS.CvSActualLiteralInputsV1.{n}\n'
(w/'CvSActualLiteralInputsV1.lean').write_text(s)
print('Generated original-import actual source budget candidate. NOT_KERNEL_VERIFIED.')
