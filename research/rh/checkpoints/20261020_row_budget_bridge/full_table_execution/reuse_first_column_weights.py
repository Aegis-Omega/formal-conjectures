from pathlib import Path
w=Path(__file__).resolve().parent;p=w/'CvSFullTableClosureV1.lean';s=p.read_text();a=s.index('theorem weighted_exact');b=s.index('theorem gram_exact',a)
r='''theorem weighted_exact : ∀ i (k : Fin 141),
    (T.getD k.val ⟨0, 0⟩).mul 96 ((columns i).x.values.getD k.val ⟨0, 0⟩) =
      (columns i).dx.values.getD k.val ⟨0, 0⟩ := by
  intro i k
  fin_cases i
'''
for i in range(139):
 ns=f'AEGIS.RowBudgetFirstColumnBatch{i//10}'
 mem='Or.inl True.intro'
 for _ in range(i%10):mem='Or.inr ('+mem+')'
 r+=f'''  · have hm : {ns}.entry{i} ∈ {ns}.entries := by
      simp only [{ns}.entries, List.mem_cons]
      exact {mem}
    have hw : AEGIS.CvSFirstColumnCheckerV1.wellFormed {ns}.entry{i} :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp {ns}.checked {ns}.entry{i} hm)).1
    exact hw.2.2.2 k
'''
p.write_text(s[:a]+r+s[b:])
