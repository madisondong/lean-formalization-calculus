import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# §4.4 Bài 7: đa thức nhân hàm mũ giảm

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1740.
-/

set_option autoImplicit false
open Filter Topology
open scoped Polynomial
namespace calculus.Chapter04.Section04PolynomialExponentialDecayExercise

theorem source_polynomial_times_exp_neg_tendsto_zero (P : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ P.eval x * Real.exp (-x)) atTop (𝓝 0) := by
  simpa only [Real.exp_neg, div_eq_mul_inv] using! P.tendsto_div_exp_atTop

end calculus.Chapter04.Section04PolynomialExponentialDecayExercise
