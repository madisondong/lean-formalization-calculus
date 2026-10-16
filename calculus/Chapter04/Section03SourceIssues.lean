import calculus.Chapter04.Section01Higher
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

/-!
# Phản ví dụ cho các công thức trong §4.3

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1110–1112, 1174–1175. Đoạn một điểm không thỏa điều kiện `a < b` của Định nghĩa 2.1.6.
-/
namespace calculus.Chapter04.Section03SourceIssues
open Set
open Finset hiding Ioo Icc
open scoped BigOperators


theorem quadratic_exercise_hypotheses :
    ContinuousOn (fun x : ℝ ↦ x ^ 2) (Icc 0 1) ∧
      DifferentiableOn ℝ (fun x : ℝ ↦ x ^ 2) (Ioo 0 1) ∧
        (0 : ℝ) ^ 2 = 0 ∧ (1 : ℝ) ^ 2 = 1 := by
  exact ⟨(continuous_pow 2).continuousOn, (differentiable_id.pow 2).differentiableOn,
    by norm_num, by norm_num⟩


theorem positive_index_sum :
    (∑ k ∈ range 2013, ((k + 1 : ℕ) : ℝ)) = (2013 * 2014 / 2 : ℝ) := by
  have hsum (n : ℕ) : (∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  calc
    _ = (2013 : ℝ) * ((2013 : ℝ) + 1) / 2 := hsum 2013
    _ = _ := by norm_num


theorem derivative_square (x : ℝ) : deriv (fun t : ℝ ↦ t ^ 2) x = 2 * x := by
  simp


theorem quadratic_weighted_sum (x : ℕ → ℝ)
    (hx : ∀ k ∈ range 2013, x (k + 1) ∈ Ioo 0 1) :
    (∑ k ∈ range 2013,
      ((k + 1 : ℕ) : ℝ) * x (k + 1) / deriv (fun t : ℝ ↦ t ^ 2) (x (k + 1))) =
        (2013 * 2014 / 4 : ℝ) := by
  have he : (∑ k ∈ range 2013,
      ((k + 1 : ℕ) : ℝ) * x (k + 1) / deriv (fun t : ℝ ↦ t ^ 2) (x (k + 1))) =
        ∑ k ∈ range 2013, ((k + 1 : ℕ) : ℝ) / 2 := by
    apply sum_congr rfl
    intro k hk
    have hne : x (k + 1) ≠ 0 := (hx k hk).1.ne'
    rw [derivative_square]
    field_simp [hne]
  rw [he, ← sum_div, positive_index_sum]
  norm_num

/-- Không có bộ 2013 điểm trong miền `(0, 1)` thỏa kết luận Bài 20, kể cả khi yêu cầu các điểm phân biệt. -/
theorem printed_weighted_sum_false (x : ℕ → ℝ)
    (hx : ∀ k ∈ range 2013, x (k + 1) ∈ Ioo 0 1) :
    (∑ k ∈ range 2013,
      ((k + 1 : ℕ) : ℝ) * x (k + 1) / deriv (fun t : ℝ ↦ t ^ 2) (x (k + 1))) ≠
        (2013 * 2007 / 2 : ℝ) := by
  rw [quadratic_weighted_sum x hx]
  norm_num

/-- Bài 4: trên đoạn một điểm `a = b = 0`, hàm `f = 1` không có điểm nội khoảng. Trường hợp này không thỏa `a < b` trong Định nghĩa 2.1.6. -/
theorem degenerate_logarithmic_exercise_false :
    ContinuousOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc 0 0) ∧
      DifferentiableOn ℝ (fun _ : ℝ ↦ (1 : ℝ)) (Ioo 0 0) ∧
        (∀ x ∈ Ioo (0 : ℝ) 0, (1 : ℝ) ≠ 0) ∧
          ¬∃ c ∈ Ioo (0 : ℝ) 0,
            deriv (fun _ : ℝ ↦ (1 : ℝ)) c / (1 : ℝ) = 1 / (0 - c) + 1 / (0 - c) := by
  refine ⟨continuous_const.continuousOn, (differentiable_const (1 : ℝ)).differentiableOn,
    fun _ _ ↦ one_ne_zero, ?_⟩
  rintro ⟨c, hc, _⟩
  linarith [hc.1, hc.2]

/-- Bài 6: với `a = 0`, đoạn `[0, a]` không có điểm nội khoảng. Trường hợp này không thỏa điều kiện đoạn không suy biến của Định nghĩa 2.1.6. -/
theorem degenerate_exponential_exercise_false :
    DifferentiableOn ℝ (fun _ : ℝ ↦ (0 : ℝ)) (Icc 0 0) ∧
      (0 : ℝ) = 0 ∧
        ¬∃ c ∈ Ioo (0 : ℝ) 0,
          deriv (fun _ : ℝ ↦ (0 : ℝ)) c = (0 : ℝ) * (2024 - 1 / c) := by
  refine ⟨(differentiable_const (0 : ℝ)).differentiableOn, rfl, ?_⟩
  rintro ⟨c, hc, _⟩
  linarith [hc.1, hc.2]

/-- Bài 5 sai trên `[0, 1]`: hàm `f(x)=1−2x` có tỉ số hai giá trị đầu mút âm, còn hàm mũ luôn dương. -/
theorem sign_changing_exponential_ratio_false :
    ContinuousOn (fun x : ℝ ↦ 1 - 2 * x) (Icc 0 1) ∧
      DifferentiableOn ℝ (fun x : ℝ ↦ 1 - 2 * x) (Ioo 0 1) ∧
        ¬∃ c ∈ Ioo (0 : ℝ) 1, (1 - 2 * c) ≠ 0 ∧
          (1 - 2 * (1 : ℝ)) / (1 - 2 * (0 : ℝ)) =
            Real.exp ((1 - 0) * deriv (fun x : ℝ ↦ 1 - 2 * x) c / (1 - 2 * c)) := by
  refine ⟨(continuous_const.sub (continuous_const.mul continuous_id)).continuousOn,
    ((differentiable_const (1 : ℝ)).sub ((differentiable_const (2 : ℝ)).mul differentiable_id)).differentiableOn,
    ?_⟩
  rintro ⟨c, _, _, he⟩
  norm_num at he
  have hp := Real.exp_pos ((1 - 0) * deriv (fun x : ℝ ↦ 1 - 2 * x) c / (1 - 2 * c))
  norm_num at hp
  linarith

/-- Nhận xét 4.3.13: cận thiếu số mũ 2; phản ví dụ `f(x) = x²`, `x₀ = 0`, `x = 1/2`. -/
theorem printed_taylor_approximation_false :
    ContDiff ℝ 3 (fun x : ℝ ↦ x ^ 2) ∧
      ∀ c ∈ uIoo (0 : ℝ) (1 / 2),
        ¬ |(1 / 2 : ℝ) ^ 2 -
          ((0 : ℝ) ^ 2 + deriv (fun x : ℝ ↦ x ^ 2) 0 * (1 / 2) +
            iteratedDeriv 2 (fun x : ℝ ↦ x ^ 2) 0 / 2 * (1 / 2))| ≤
          |iteratedDeriv 3 (fun x : ℝ ↦ x ^ 2) c * (1 / 2) ^ 3| / ((3 : ℕ).factorial : ℝ) := by
  refine ⟨contDiff_id.pow 2, ?_⟩
  intro c _
  rw [derivative_square]
  norm_num [iteratedDeriv_pow,
    Nat.descFactorial]

end calculus.Chapter04.Section03SourceIssues
