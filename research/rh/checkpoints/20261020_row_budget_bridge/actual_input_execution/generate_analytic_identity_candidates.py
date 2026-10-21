"""Finite literal/source identities for original-import CI. Candidates until replayed."""
from pathlib import Path
w=Path(__file__).resolve().parent
head='''open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSActualRowInputL12V1 AEGIS.CvSProjectedPackedCertificateL12V1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
for b,start in enumerate(range(0,301,10)):
 ns=f'CvSAnalyticERows{b}';s='/- Exact source identity candidates; require original CvS import replay. -/\nimport CvSActualRowInputL12V1\n'+f'import CvSSourceERows{b}\n'+head+f'namespace AEGIS.{ns}\n'
 for r in range(start,min(start+10,301)):
  s+=f'''theorem row{r} : ∀ k : Fin 141,
    AEGIS.CvSSourceERows{b}.row{r}.values.getD k.val ⟨0, 0⟩ =
      kernelBox 96 (rowIndex ⟨{r}, by decide⟩) k := by decide +kernel
#print axioms row{r}
'''
 s+=f'end AEGIS.{ns}\n';(w/(ns+'.lean')).write_text(s)
for b,start in enumerate(range(0,139,10)):
 ns=f'CvSAnalyticXColumns{b}';s='/- Actual transformed coefficient source identity candidates. -/\nimport CvSActualRowInputL12V1\n'+''.join(f'import CvSCachedInput{i}\n' for i in range(start,min(start+10,139)))+head+f'namespace AEGIS.{ns}\n'
 for i in range(start,min(start+10,139)):
  s+=f'''theorem column{i} : ∀ k : Fin 141,
    AEGIS.CvSCachedInput{i}.x.values.getD k.val ⟨0, 0⟩ = xBox k ⟨{i}, by decide⟩ := by decide +kernel
#print axioms column{i}
'''
 s+=f'end AEGIS.{ns}\n';(w/(ns+'.lean')).write_text(s)
for b,start in enumerate(range(0,141,10)):
 ns=f'CvSAnalyticGRows{b}';s='/- Actual rational harmonic Gram-majorant source identity candidates. -/\nimport CvSActualRowInputL12V1\nimport RowBudgetListCell0Pilot\n'+head+f'namespace AEGIS.{ns}\n'
 for k in range(start,min(start+10,141)):
  s+=f'''theorem row{k} : ∀ l : Fin 141,
    (AEGIS.RowBudgetListCell0Pilot.G.getD {k} []).getD l.val ⟨0, 0⟩ =
      AEGIS.CvSRationalIntervalV1.rationalRange 96
        (gramRat 150 (signedFreq ⟨{k}, by decide⟩) (signedFreq l))
        (gramRat 150 (signedFreq ⟨{k}, by decide⟩) (signedFreq l)) := by decide +kernel
#print axioms row{k}
'''
 s+=f'end AEGIS.{ns}\n';(w/(ns+'.lean')).write_text(s)
for b,start in enumerate(range(0,139,10)):
 ns=f'CvSAnalyticQColumns{b}';s='/- Original Q64-to-Q96 projected-entry input identity candidates. -/\nimport CvSActualRowInputL12V1\n'+''.join(f'import CvSCachedOutput{i}\n' for i in range(start,min(start+10,139)))+head+f'namespace AEGIS.{ns}\n'
 for i in range(start,min(start+10,139)):
  s+=f'''theorem column{i} : ∀ j : Fin 139,
    AEGIS.CvSCachedOutput{i}.q.getD j.val ⟨0, 0⟩ =
      upscale 32 (AEGIS.CvSPackedGramV1.Im certI j.val {i}) := by decide +kernel
#print axioms column{i}
'''
 s+=f'end AEGIS.{ns}\n';(w/(ns+'.lean')).write_text(s)
s='/- Fixed normalization and signed-tau source identity candidates. -/\nimport CvSActualRowInputL12V1\nimport RowBudgetStagedDotPilot\nimport RowBudgetListCell0Pilot\n'+head+'''namespace AEGIS.CvSAnalyticScalarInputsV1

theorem tau_source : ∀ k : Fin 141,
    AEGIS.RowBudgetStagedDotPilot.T.getD k.val ⟨0, 0⟩ = tauBox 96 (signedFreq k) := by decide +kernel

theorem lp_source : AEGIS.RowBudgetListCell0Pilot.LP2 =
    AEGIS.CvSFrequencyIntervalV1.lpSquaredInterval 96 := by decide +kernel
end AEGIS.CvSAnalyticScalarInputsV1
#print axioms AEGIS.CvSAnalyticScalarInputsV1.tau_source
#print axioms AEGIS.CvSAnalyticScalarInputsV1.lp_source
'''
(w/'CvSAnalyticScalarInputsV1.lean').write_text(s)
print('Generated original-import analytic identity candidates; NONE claimed kernel verified')
