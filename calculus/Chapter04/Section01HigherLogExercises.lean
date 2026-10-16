import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 24(c,g): đạo hàm cấp cao có logarit

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 668,672.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherLogExercises
open Filter Set calculus.Chapter04.Section01Higher
open scoped ContDiff Topology

/-- Số điều hòa `Hₙ = 1 + 1/2 + … + 1/n`. -/
def harmonicNumber (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℝ)


theorem harmonicNumber_succ (n : ℕ) :
    harmonicNumber (n + 1) = harmonicNumber n + 1 / ((n + 1 : ℕ) : ℝ) := by
  simp only [harmonicNumber, Finset.sum_range_succ]

/-- Bài 24(c): đạo hàm cấp `n` của `log x/x` trên `x > 0`. -/
theorem logarithm_div_coordinate_iteratedDeriv (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ ↦ Real.log y / y) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
        ((Real.log x - harmonicNumber n) / x ^ (n + 1)) := by
  induction n generalizing x with
  | zero => simp [harmonicNumber]
  | succ n ih =>
    have hnear : iteratedDeriv n (fun y : ℝ ↦ Real.log y / y) =ᶠ[𝓝 x]
        fun y : ℝ ↦ (-1 : ℝ) ^ n * (n.factorial : ℝ) *
          ((Real.log y - harmonicNumber n) / y ^ (n + 1)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih y hy
    have hq := (((Real.hasDerivAt_log hx.ne').sub_const (harmonicNumber n)).fun_div
      (hasDerivAt_pow (n + 1) x) (pow_ne_zero _ hx.ne')).const_mul
        ((-1 : ℝ) ^ n * (n.factorial : ℝ))
    rw [iteratedDeriv_succ, hnear.deriv_eq, hq.deriv, harmonicNumber_succ]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx.ne', hn]
    ring

/-- Bài 24(c): đạo hàm cấp `n` của `log x/x`, biểu diễn qua số điều hòa. -/
theorem logarithm_div_coordinate_positive_order (n : ℕ) (_hn : 1 ≤ n)
    (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ ↦ Real.log y / y) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
        ((Real.log x - harmonicNumber n) / x ^ (n + 1)) :=
  logarithm_div_coordinate_iteratedDeriv n x hx

/-- Công thức đạo hàm cấp `m` của logarit. -/
def logarithmNthDerivative (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then Real.log x else (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / x ^ m


theorem logarithm_iteratedDeriv (m : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv m Real.log x = logarithmNthDerivative m x := by
  cases m with
  | zero => simp [logarithmNthDerivative]
  | succ m =>
    rw [iteratedDeriv_succ', Real.deriv_log']
    have heq : (Inv.inv : ℝ → ℝ) = fun y : ℝ ↦ 1 / y := by funext y; simp
    rw [heq, reciprocal_iteratedDeriv m x hx.ne']
    simp [logarithmNthDerivative]

/-- Bài 24(g): đạo hàm cấp `n` của `xⁿ log x` trên `x > 0`. -/
theorem power_logarithm_iteratedDeriv (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ ↦ y ^ n * Real.log y) x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((n.descFactorial i : ℝ) * x ^ (n - i)) * logarithmNthDerivative (n - i) x := by
  have hp : ContDiffAt ℝ n (fun y : ℝ ↦ y ^ n) x := contDiff_id.contDiffAt.pow n
  have hl : ContDiffAt ℝ n Real.log x := Real.contDiffAt_log.mpr hx.ne'
  rw [iteratedDeriv_fun_mul hp hl]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_pow, logarithm_iteratedDeriv (n - i) x hx]

end calculus.Chapter04.Section01HigherLogExercises
