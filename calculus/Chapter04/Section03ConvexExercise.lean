import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

/-!
# Bài tập 4.3.11: bước theo đạo hàm của hàm lồi

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1143–1144. Chỉ cần khả vi hai lần, không cần `f″` liên tục.
-/
namespace calculus.Chapter04.Section03ConvexExercise
open Set

/-- Bài 11: hàm có đạo hàm cấp hai dương thỏa `f(x) ≤ f(x + f′(x))`. -/
theorem value_le_at_derivative_step {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hpos : ∀ x, 0 < deriv (deriv f) x) (x : ℝ) : f x ≤ f (x + deriv f x) := by
  have hcv : ConvexOn ℝ univ f :=
    convexOn_univ_of_deriv2_nonneg hf hdf (fun x ↦ (hpos x).le)
  rcases lt_trichotomy (deriv f x) 0 with hn | hz | hp
  · have hxy : x + deriv f x < x := by linarith
    have hs := hcv.slope_le_deriv (mem_univ _) (mem_univ _) hxy (hf x)
    rw [slope_def_field] at hs
    have hmul := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
    nlinarith [sq_nonneg (deriv f x)]
  · simp [hz]
  · have hxy : x < x + deriv f x := by linarith
    have hs := hcv.deriv_le_slope (mem_univ _) (mem_univ _) hxy (hf x)
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    nlinarith [sq_nonneg (deriv f x)]

end calculus.Chapter04.Section03ConvexExercise
