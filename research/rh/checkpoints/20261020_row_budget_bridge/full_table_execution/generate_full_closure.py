from pathlib import Path
w=Path(__file__).resolve().parent
s='/- Complete finite table: every ordered pair, original envelope, original target boxes. -/\nimport CvSFullCachedTableV1\nimport CvSCachedGramV1\nimport RowBudgetListCell0Pilot\n'
s+=''.join(f'import CvSCachedProduct{i}\nimport CvSCachedOutput{i}\n' for i in range(139))
s+='import Mathlib.Tactic.FinCases\n'
s+='''open scoped BigOperators
namespace AEGIS.CvSFullTableClosureV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSRowBudgetEnvelopeV1 AEGIS.CvSCachedColumnV1
open AEGIS.CvSCachedEnvelopeJoinV1 AEGIS.CvSFullCachedTableV1
open AEGIS.RowBudgetListCell0Pilot AEGIS.RowBudgetStagedDotPilot
open AEGIS.CvSListIntervalDotV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def columns (i : Fin 139) : Column := column i.val
'''
s+='def qColumns : List (List Iv) := ['+', '.join(f'AEGIS.CvSCachedOutput{i}.q' for i in range(139))+']\n'
s+='''def Q (i j : Fin 139) : Iv := (qColumns.getD j.val []).getD i.val ⟨0, 0⟩
def target (i j : Fin 139) : Iv :=
  AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals i.val j.val

theorem weighted_exact : ∀ i (k : Fin 141),
    (T.getD k.val ⟨0, 0⟩).mul 96 ((columns i).x.values.getD k.val ⟨0, 0⟩) =
      (columns i).dx.values.getD k.val ⟨0, 0⟩ := by decide +kernel
'''
for name,field,src in [('gram_exact','gx','x'),('gram_weighted_exact','gdx','dx')]:
 s+=f'''theorem {name} (j : Fin 139) : (columns j).{field}.values =
    G.map (fun row => listDot 96 row (columns j).{src}.values) := by
  fin_cases j
'''
 for i in range(139):s+=f'  · exact AEGIS.CvSCachedProduct{i}.{field}_exact\n'
s+='''theorem checked (i j : Fin 139) : contains (target i j)
    (downscale 16 (value (Q i j) LP2 (columns i).x (columns i).dx
      (columns i).z (columns j).z (columns j).gx (columns j).gdx)) = true := by
  fin_cases j
'''
for j in range(139):s+=f'  · exact AEGIS.CvSCachedOutput{j}.all_rows i\n'
s+='''/-- All 19,321 ordered entries of the original finite envelope are enclosed. -/
theorem full_table_contains (i j : Fin 139) : contains (target i j)
    (downscale 16 (envelope 96 Q (coeff columns)
      (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩) (residual columns) LP2 i j)) = true := by
  rw [envelope_eq_cached columns Q G T LP2 G_length G_rows
    weighted_exact gram_exact gram_weighted_exact]
  exact checked i j

/-- The complete finite comparison transfers any original Q96 entry membership. -/
theorem full_table_mem (i j : Fin 139) (v : ℝ)
    (hv : (envelope 96 Q (coeff columns)
      (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩) (residual columns) LP2 i j).Mem 96 v) :
    (target i j).Mem 80 v :=
  mem_of_contains 80 (full_table_contains i j) (downscale_mem 80 16 hv)

/-- Only input memberships remain; the entire output-table check is discharged. -/
theorem real_envelope_mem
    (q : Fin 139 → Fin 139 → ℝ) (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ)
    (z : Fin 301 → Fin 139 → ℝ) (lp2 : ℝ)
    (hQ : ∀ i j, (Q i j).Mem 96 (q i j))
    (hX : ∀ k i, (coeff columns k i).Mem 96 (x k i))
    (hG : ∀ k l : Fin 141, ((G.getD k.val []).getD l.val ⟨0, 0⟩).Mem 96 (g k l))
    (hT : ∀ k : Fin 141, (T.getD k.val ⟨0, 0⟩).Mem 96 (t k))
    (hZ : ∀ r i, (residual columns r i).Mem 96 (z r i))
    (hLP : LP2.Mem 96 lp2) :
    ∀ i j, (target i j).Mem 80
      (40 * q i j - (∑ r, z r i * z r j) -
        lp2 * (2 * (∑ k, ∑ l, (t k * x k i) * (t l * x l j) * g k l) +
          338 * (∑ k, ∑ l, x k i * x l j * g k l))) := by
  intro i j
  exact full_table_mem i j _ (envelope_mem 96 Q (coeff columns)
    (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
    (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩) (residual columns) LP2
    q x g t z lp2 hQ hX hG hT hZ hLP i j)
end AEGIS.CvSFullTableClosureV1
'''
for n in ['weighted_exact','gram_exact','gram_weighted_exact','checked','full_table_contains','full_table_mem','real_envelope_mem']:
 s+=f'#check @AEGIS.CvSFullTableClosureV1.{n}\n#print axioms AEGIS.CvSFullTableClosureV1.{n}\n'
(w/'CvSFullTableClosureV1.lean').write_text(s)
print('Full-table closure source generated; not yet kernel verified')

# Reuse the independently checked weighted columns instead of re-evaluating their full table.
import runpy
runpy.run_path(str(w / "reuse_first_column_weights.py"))
