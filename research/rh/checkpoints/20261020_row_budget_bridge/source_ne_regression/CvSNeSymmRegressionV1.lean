/- Reproduce and repair the negative-equality branch elaboration from a1862b9b. -/
import CvSFrequencyIntervalV1
namespace AEGIS.CvSNeSymmRegressionV1

theorem reverse_ne (n m : ℤ) (h : ¬ n = m) : m ≠ n := by
  fail_if_success exact h.symm
  exact Ne.symm h

noncomputable def gram (H : ℤ → ℝ) (NP : ℕ) (n m : ℤ) : ℝ :=
  if n = m then 1 / ((NP : ℝ) - n + 1 / 2) + 1 / ((NP : ℝ) + n + 1 / 2)
  else (H (NP - m) - H (NP - n) + (H (NP + n) - H (NP + m))) / ((n : ℝ) - m)

/-- The repaired source Gram symmetry argument works for every real H. -/
theorem gram_symm (H : ℤ → ℝ) (NP : ℕ) (n m : ℤ) : gram H NP n m = gram H NP m n := by
  by_cases h : n = m
  · subst m
    rfl
  · simp only [gram, if_neg h, if_neg (Ne.symm h)]
    rw [show (m : ℝ) - n = -((n : ℝ) - m) by ring, div_neg, ← neg_div]
    congr 1
    ring

end AEGIS.CvSNeSymmRegressionV1
#print axioms AEGIS.CvSNeSymmRegressionV1.reverse_ne
#print axioms AEGIS.CvSNeSymmRegressionV1.gram_symm
