import calculus.Chapter04.Section03TaylorElementary

/-!
# Bài tập 4.3.27: tổng Maclaurin nhỏ hơn hàm mũ

Nguồn: `source/Ch4_hamsokhavi.tex`, Bài 27.
-/
namespace calculus.Chapter04.Section03ExponentialSumExercise
open Set Finset
open scoped BigOperators

/-- Bài 27: tổng Maclaurin hữu hạn nhỏ hơn `exp x` khi `x > 0`. -/
theorem exponential_partial_sum_lt {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ range (m + 1), x ^ k / (k.factorial : ℝ)) < Real.exp x := by
  obtain ⟨θ, _, he⟩ := Section03TaylorElementary.exponential_maclaurin m hm x
  have hr : 0 < Real.exp (θ * x) * x ^ (m + 1) /
      ((m + 1).factorial : ℝ) := by positivity
  linarith

end calculus.Chapter04.Section03ExponentialSumExercise
