import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bài 21: các đạo hàm của arctan tại 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 648–650.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherArctangentExercise
open scoped ContDiff


def reciprocalQuadratic (x : ℝ) : ℝ := 1 / (1 + x ^ 2)


theorem reciprocalQuadratic_contDiff (n : ℕ) : ContDiff ℝ n reciprocalQuadratic := by
  have h : ContDiff ℝ n (fun x : ℝ ↦ 1 + x ^ 2) := contDiff_const.add (contDiff_id.pow 2)
  change ContDiff ℝ n (fun x : ℝ ↦ 1 / (1 + x ^ 2))
  simpa only [one_div] using
    (show ContDiff ℝ n (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) from
      h.inv (fun x ↦ by positivity : ∀ x : ℝ, 1 + x ^ 2 ≠ 0))


theorem quadratic_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ 1 + x ^ 2) 0 =
      if n = 0 then 1 else if n = 2 then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [iteratedDeriv_const_add (by omega : 0 < n) 1, iteratedDeriv_fun_pow_zero]
    simp [hn]


theorem reciprocalQuadratic_zero : reciprocalQuadratic 0 = 1 := by simp [reciprocalQuadratic]


theorem reciprocalQuadratic_hasDerivAt_zero : HasDerivAt reciprocalQuadratic 0 0 := by
  have hD := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_pow 2 (0 : ℝ))
  have hInv := hD.inv (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)
  apply (hInv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    simp [reciprocalQuadratic, one_div])).congr_deriv
  norm_num


theorem reciprocalQuadratic_derivative_recurrence (m : ℕ) :
    iteratedDeriv (m + 2) reciprocalQuadratic 0 =
      -((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * iteratedDeriv m reciprocalQuadratic 0 := by
  have hQ : ContDiff ℝ (m + 2) (fun x : ℝ ↦ 1 + x ^ 2) :=
    contDiff_const.add (contDiff_id.pow 2)
  have hprod : (fun x : ℝ ↦ (1 + x ^ 2) * reciprocalQuadratic x) = fun _ ↦ (1 : ℝ) := by
    funext x
    have hd : 1 + x ^ 2 ≠ 0 := by positivity
    simp [reciprocalQuadratic, hd]
  have h := iteratedDeriv_fun_mul hQ.contDiffAt (reciprocalQuadratic_contDiff (m + 2)).contDiffAt
    (x := (0 : ℝ))
  rw [hprod, iteratedDeriv_const] at h
  simp only [if_neg (by omega : m + 2 ≠ 0)] at h
  let t := fun i : ℕ ↦ ((m + 2).choose i : ℝ) *
    iteratedDeriv i (fun x : ℝ ↦ 1 + x ^ 2) 0 *
    iteratedDeriv (m + 2 - i) reciprocalQuadratic 0
  change 0 = ∑ i ∈ Finset.range (m + 3), t i at h
  rw [Finset.sum_range_succ' t (m + 2),
    Finset.sum_range_succ' (fun i ↦ t (i + 1)) (m + 1),
    Finset.sum_range_succ' (fun i ↦ t (i + 1 + 1)) m] at h
  have hz : ∑ i ∈ Finset.range m, t (i + 1 + 1 + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [t, quadratic_iteratedDeriv_zero, show i + 1 + 1 + 1 ≠ 2 by omega]
  rw [hz] at h
  simp only [t, quadratic_iteratedDeriv_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.sub_zero, show (1 : ℕ) ≠ 0 by decide,
    show (1 : ℕ) ≠ 2 by decide, show (2 : ℕ) ≠ 0 by decide, if_false, if_true,
    mul_zero, zero_mul, zero_add, Nat.add_sub_cancel] at h
  rw [Nat.cast_choose_two] at h
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  nlinarith


theorem reciprocalQuadratic_even_derivative (n : ℕ) :
    iteratedDeriv (2 * n) reciprocalQuadratic 0 = (-1 : ℝ) ^ n * ((2 * n).factorial : ℝ) := by
  induction n with
  | zero => simp [reciprocalQuadratic]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, reciprocalQuadratic_derivative_recurrence,
      ih, pow_succ]
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring


theorem reciprocalQuadratic_odd_derivative (n : ℕ) :
    iteratedDeriv (2 * n + 1) reciprocalQuadratic 0 = 0 := by
  induction n with
  | zero => simpa only [mul_zero, zero_add, iteratedDeriv_one] using reciprocalQuadratic_hasDerivAt_zero.deriv
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      reciprocalQuadratic_derivative_recurrence, ih, mul_zero]

/-- Bài 21: các đạo hàm cấp chẵn của arctan tại 0. -/
theorem arctangent_even_derivative (n : ℕ) : iteratedDeriv (2 * n) Real.arctan 0 = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, iteratedDeriv_succ', Real.deriv_arctan]
    exact reciprocalQuadratic_odd_derivative n

/-- Bài 21: đạo hàm cấp lẻ của arctan tại 0 có hệ số `(2n)!`. -/
theorem arctangent_odd_derivative (n : ℕ) :
    iteratedDeriv (2 * n + 1) Real.arctan 0 = (-1 : ℝ) ^ n * ((2 * n).factorial : ℝ) := by
  rw [iteratedDeriv_succ', Real.deriv_arctan]
  exact reciprocalQuadratic_even_derivative n

/-- Bài 21: các đạo hàm cấp chẵn và lẻ của arctan tại 0. -/
theorem arctangent_derivatives_at_zero (n : ℕ) (_hn : 1 ≤ n) :
    iteratedDeriv (2 * n) Real.arctan 0 = 0 ∧
      iteratedDeriv (2 * n + 1) Real.arctan 0 = (-1 : ℝ) ^ n * ((2 * n).factorial : ℝ) :=
  ⟨arctangent_even_derivative n, arctangent_odd_derivative n⟩

end calculus.Chapter04.Section01HigherArctangentExercise
