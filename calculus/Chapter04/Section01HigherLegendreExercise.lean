import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Bài 23: Rodrigues và phương trình Legendre

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 656–661.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherLegendreExercise
open Polynomial
open scoped Polynomial


def legendreRodriguesBase (m : ℕ) : ℝ[X] := (X ^ 2 - 1) ^ m

/-- Đa thức Legendre, xác định bằng công thức Rodrigues. -/
def legendrePolynomial (m : ℕ) : ℝ[X] :=
  C (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) * derivative^[m] (legendreRodriguesBase m)


def legendrePolynomialValue (m : ℕ) (x : ℝ) : ℝ := (legendrePolynomial m).eval x


theorem polynomial_iteratedDeriv_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ p.eval x) = fun x ↦ (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Polynomial.deriv]
    simp only [Function.iterate_succ_apply']


theorem legendre_rodrigues_normalization_ne_zero (m : ℕ) :
    (2 : ℝ) ^ m * (m.factorial : ℝ) ≠ 0 := by positivity


theorem legendrePolynomialValue_eq_source (m : ℕ) (x : ℝ) :
    legendrePolynomialValue m x = 1 / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
      iteratedDeriv m (fun y : ℝ ↦ (y ^ 2 - 1) ^ m) x := by
  have heq : (fun y : ℝ ↦ (legendreRodriguesBase m).eval y) =
      (fun y : ℝ ↦ (y ^ 2 - 1) ^ m) := by
    funext y
    simp [legendreRodriguesBase]
  rw [← heq, polynomial_iteratedDeriv_eval]
  simp [legendrePolynomialValue, legendrePolynomial]


theorem legendreRodriguesBase_first_identity (m : ℕ) :
    (X ^ 2 - 1) * (legendreRodriguesBase m).derivative =
      C (2 * (m : ℝ)) * X * legendreRodriguesBase m := by
  cases m with
  | zero => simp [legendreRodriguesBase]
  | succ m =>
    change (X ^ 2 - 1 : ℝ[X]) * derivative ((X ^ 2 - 1) ^ (m + 1)) =
      C (2 * ((m + 1 : ℕ) : ℝ)) * X * (X ^ 2 - 1) ^ (m + 1)
    rw [Polynomial.derivative_pow_succ, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_one]
    simp only [Nat.reduceSub, sub_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_ofNat, Polynomial.C_1, pow_succ]
    ring


theorem legendreRodriguesBase_second_identity (m : ℕ) :
    (derivative^[2] (legendreRodriguesBase m)) * X ^ 2 - derivative^[2] (legendreRodriguesBase m) +
      C (2 - 2 * (m : ℝ)) * ((legendreRodriguesBase m).derivative * X) -
      C (2 * (m : ℝ)) * legendreRodriguesBase m = 0 := by
  have h := congrArg derivative (legendreRodriguesBase_first_identity m)
  rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X_sq,
    Polynomial.derivative_one, sub_zero, Polynomial.derivative_mul,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, mul_one] at h
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at ⊢
  simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_ofNat] at h ⊢
  linear_combination h


theorem polynomial_iterate_derivative_add (m : ℕ) (p q : ℝ[X]) :
    derivative^[m] (p + q) = derivative^[m] p + derivative^[m] q :=
  iterate_map_add derivative m p q


theorem legendreRodriguesBase_iterated_identity (m : ℕ) (hm : 1 ≤ m) :
    (X ^ 2 - 1) * derivative^[m + 2] (legendreRodriguesBase m) +
      2 * X * derivative^[m + 1] (legendreRodriguesBase m) -
      C ((m : ℝ) * ((m : ℝ) + 1)) * derivative^[m] (legendreRodriguesBase m) = 0 := by
  have h := congrArg (derivative^[m]) (legendreRodriguesBase_second_identity m)
  rw [iterate_derivative_zero] at h
  rw [iterate_derivative_sub, polynomial_iterate_derivative_add, iterate_derivative_sub,
    iterate_derivative_C_mul, iterate_derivative_C_mul,
    iterate_derivative_derivative_mul_X_sq, iterate_derivative_derivative_mul_X,
    ← Function.iterate_add_apply] at h
  simp only [nsmul_eq_mul, ← C_eq_natCast, Nat.cast_mul, Nat.cast_sub hm,
    Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_add, Polynomial.C_ofNat,
    Polynomial.C_1] at h ⊢
  simp only [Nat.cast_ofNat, Nat.cast_one, Polynomial.C_ofNat, Polynomial.C_1] at h
  linear_combination h


theorem legendrePolynomial_equation (m : ℕ) (hm : 1 ≤ m) :
    (1 - X ^ 2) * (legendrePolynomial m).derivative.derivative -
      2 * X * (legendrePolynomial m).derivative +
      C ((m : ℝ) * ((m : ℝ) + 1)) * legendrePolynomial m = 0 := by
  have h := legendreRodriguesBase_iterated_identity m hm
  simp only [legendrePolynomial, derivative_C_mul,
    ← Function.iterate_succ_apply']
  linear_combination -C (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) * h


theorem legendrePolynomialValue_deriv (m : ℕ) :
    deriv (legendrePolynomialValue m) = fun x ↦ (legendrePolynomial m).derivative.eval x := by
  funext x
  exact (legendrePolynomial m).deriv

/-- Bài 23: phương trình vi phân của hàm thực định nghĩa bằng Rodrigues. -/
theorem legendrePolynomialValue_equation (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (1 - x ^ 2) * deriv (deriv (legendrePolynomialValue m)) x -
      2 * x * deriv (legendrePolynomialValue m) x +
      (m : ℝ) * ((m : ℝ) + 1) * legendrePolynomialValue m x = 0 := by
  have h := congrArg (Polynomial.eval x) (legendrePolynomial_equation m hm)
  rw [legendrePolynomialValue_deriv, Polynomial.deriv]
  simpa [legendrePolynomialValue] using h

/-- Bài 23: công thức Rodrigues và phương trình vi phân. -/
theorem legendre_rodrigues_solution (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : ℝ, legendrePolynomialValue m x = 1 / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
      iteratedDeriv m (fun y : ℝ ↦ (y ^ 2 - 1) ^ m) x) ∧
      ∀ x : ℝ, (1 - x ^ 2) * deriv (deriv (legendrePolynomialValue m)) x -
        2 * x * deriv (legendrePolynomialValue m) x +
        (m : ℝ) * ((m : ℝ) + 1) * legendrePolynomialValue m x = 0 :=
  ⟨legendrePolynomialValue_eq_source m, legendrePolynomialValue_equation m hm⟩

end calculus.Chapter04.Section01HigherLegendreExercise
