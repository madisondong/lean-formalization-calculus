import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bài tập 4.3.8: nghiệm thực từ điều kiện tổng hệ số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1124–1129.
-/
namespace calculus.Chapter04.Section03PolynomialExercises
open Set
open Finset hiding Ioo Icc
open scoped BigOperators


noncomputable def coefficientPolynomial (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), a k * x ^ k


noncomputable def coefficientPrimitive (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (a k / ((k + 1 : ℕ) : ℝ)) * x ^ (k + 1)


theorem coefficientPrimitive_hasDerivAt (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (coefficientPrimitive a n) (coefficientPolynomial a n x) x := by
  unfold coefficientPrimitive coefficientPolynomial
  apply HasDerivAt.fun_sum
  intro k _
  have hp : HasDerivAt (fun y : ℝ ↦ y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa using (hasDerivAt_id x).fun_pow (k + 1)
  have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcoeff : (a k / ((k + 1 : ℕ) : ℝ)) *
      (((k + 1 : ℕ) : ℝ) * x ^ k) = a k * x ^ k := by
    field_simp [hne]
  exact (hp.const_mul (a k / ((k + 1 : ℕ) : ℝ))).congr_deriv hcoeff

/-- Bài 8: điều kiện tổng hệ số cho một nghiệm trong `(0, 1)`. -/
theorem polynomial_has_real_root (a : ℕ → ℝ) (n : ℕ) (_hn : 1 ≤ n)
    (h : (∑ k ∈ range (n + 1), a k / ((k + 1 : ℕ) : ℝ)) = 0) :
    ∃ c ∈ Ioo (0 : ℝ) 1, coefficientPolynomial a n c = 0 := by
  refine exists_hasDerivAt_eq_zero (by norm_num : (0 : ℝ) < 1)
    (fun x _ ↦ (coefficientPrimitive_hasDerivAt a n x).continuousAt.continuousWithinAt)
    ?_ (fun x _ ↦ coefficientPrimitive_hasDerivAt a n x)
  simp only [coefficientPrimitive, zero_pow (Nat.succ_ne_zero _), mul_zero,
    sum_const_zero, one_pow, mul_one, h]

end calculus.Chapter04.Section03PolynomialExercises
