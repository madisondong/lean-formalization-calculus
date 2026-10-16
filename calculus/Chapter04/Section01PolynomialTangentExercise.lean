import calculus.Chapter04.Section01Geometry
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-!
# §4.1 Bài 7(a): tiếp tuyến của đa thức

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 485–487.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section01PolynomialTangentExercise
open calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section01Geometry


def quinticPolynomial (x : ℝ) : ℝ := x ^ 5 - 2 * x + 1


theorem quinticPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt quinticPolynomial (5 * x ^ 4 - 2) x := by
  change HasDerivAt (fun y : ℝ ↦ y ^ 5 - 2 * y + 1) (5 * x ^ 4 - 2) x
  simpa only [Pi.sub_def, Nat.cast_ofNat, Nat.reduceSub] using
    ((hasDerivAt_pow 5 x).sub (hasDerivAt_const_mul (x := x) (2 : ℝ))).add_const 1


theorem quinticPolynomial_at_zero : quinticPolynomial 0 = 1 := by
  norm_num [quinticPolynomial]


theorem quinticPolynomial_hasDerivAt_zero : HasDerivAt quinticPolynomial (-2) 0 := by
  simpa only [zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_sub] using
    quinticPolynomial_hasDerivAt 0

theorem quinticPolynomial_deriv_at_zero : deriv quinticPolynomial 0 = -2 :=
  quinticPolynomial_hasDerivAt_zero.deriv


theorem quinticPolynomial_hasDerivativeWithinAt_zero :
    HasDerivativeWithinAt quinticPolynomial univ 0 (-2) :=
  (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen quinticPolynomial univ isOpen_univ 0 (-2) (mem_univ 0)).mpr
    quinticPolynomial_hasDerivAt_zero

/-- Bài 7(a): tiếp tuyến tại `(0, 1)` là `y = 1 − 2x`. -/
theorem quinticPolynomial_tangent_at_zero :
    quinticPolynomial 0 = 1 ∧ HasDerivAt quinticPolynomial (-2) 0 ∧
      ∀ x : ℝ, tangentLine quinticPolynomial 0 (deriv quinticPolynomial 0) x = 1 - 2 * x := by
  refine ⟨quinticPolynomial_at_zero, quinticPolynomial_hasDerivAt_zero, ?_⟩
  intro x
  rw [quinticPolynomial_deriv_at_zero]
  simp only [tangentLine, quinticPolynomial_at_zero, sub_zero]
  ring


theorem quinticPolynomial_secants_converge_tangent (x : ℝ) :
    Tendsto (fun z : ℝ ↦ secantLine quinticPolynomial 0 z x)
      (𝓝[univ \ {(0 : ℝ)}] (0 : ℝ)) (𝓝 (1 - 2 * x)) := by
  have h := secantLine_tendsto_tangent quinticPolynomial_hasDerivativeWithinAt_zero x
  have he : tangentLine quinticPolynomial 0 (-2) x = 1 - 2 * x := by
    simpa only [quinticPolynomial_deriv_at_zero] using quinticPolynomial_tangent_at_zero.2.2 x
  rw [he] at h
  exact h

end calculus.Chapter04.Section01PolynomialTangentExercise
