import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bài 22: đa thức tử trong đạo hàm của 1/(xᵏ−1)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 652–654.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherRationalExercises
open Polynomial Filter Set
open scoped Polynomial Topology


def powerDenominator (k : ℕ) : ℝ[X] := X ^ k - 1

/-- Truy hồi đa thức tử từ quy tắc đạo hàm của thương. -/
def reciprocalPowerNumerator (k : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (reciprocalPowerNumerator k n).derivative * powerDenominator k -
      C ((n + 1 : ℕ) : ℝ) * reciprocalPowerNumerator k n * (powerDenominator k).derivative


theorem powerDenominator_eval (k : ℕ) (x : ℝ) :
    (powerDenominator k).eval x = x ^ k - 1 := by simp [powerDenominator]


theorem powerDenominator_derivative_eval_one (k : ℕ) :
    (powerDenominator k).derivative.eval 1 = (k : ℝ) := by
  simp [powerDenominator, derivative_X_pow]


theorem numerator_step_algebra (n : ℕ) (u p dp du : ℝ) (hu : u ≠ 0) :
    (dp * u ^ (n + 1) - p * (((n + 1 : ℕ) : ℝ) * u ^ n * du)) /
        (u ^ (n + 1)) ^ 2 =
      (dp * u - ((n + 1 : ℕ) : ℝ) * p * du) / u ^ (n + 2) := by
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  field_simp [hu]
  ring


theorem reciprocal_power_iteratedDeriv (k n : ℕ) (_hk : 1 ≤ k) (x : ℝ)
    (hx : x ^ k - 1 ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (y ^ k - 1)) x =
      (reciprocalPowerNumerator k n).eval x / (x ^ k - 1) ^ (n + 1) := by
  let D := powerDenominator k
  have hopen : IsOpen {y : ℝ | y ^ k - 1 ≠ 0} :=
    isClosed_singleton.isOpen_compl.preimage ((continuous_id.pow k).sub continuous_const)
  have hformula : ∀ n : ℕ, EqOn (iteratedDeriv n (fun y : ℝ ↦ 1 / (y ^ k - 1)))
      (fun y ↦ (reciprocalPowerNumerator k n).eval y / (D.eval y) ^ (n + 1))
      {y : ℝ | y ^ k - 1 ≠ 0} := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simp [reciprocalPowerNumerator, D, powerDenominator]
    | succ n ih =>
      intro y hy
      have hd : D.eval y ≠ 0 := by simpa [D, powerDenominator] using hy
      have hnear : iteratedDeriv n (fun z : ℝ ↦ 1 / (z ^ k - 1)) =ᶠ[𝓝 y]
          (fun z ↦ (reciprocalPowerNumerator k n).eval z / (D.eval z) ^ (n + 1)) := by
        filter_upwards [hopen.mem_nhds hy] with z hz
        exact ih hz
      have hq := ((reciprocalPowerNumerator k n).hasDerivAt y).fun_div
        ((D.hasDerivAt y).fun_pow (n + 1)) (pow_ne_zero _ hd)
      simp only [Nat.add_sub_cancel] at hq
      rw [iteratedDeriv_succ, hnear.deriv_eq, hq.deriv]
      rw [numerator_step_algebra n _ _ _ _ hd]
      simp only [reciprocalPowerNumerator, eval_sub, eval_mul, eval_C]
      rfl
  simpa only [D, powerDenominator_eval] using hformula n hx

/-- Bài 22: `Pₙ(1) = (−1)ⁿn!kⁿ`. -/
theorem reciprocalPowerNumerator_eval_one (k n : ℕ) :
    (reciprocalPowerNumerator k n).eval 1 = (-1 : ℝ) ^ n * (n.factorial : ℝ) * (k : ℝ) ^ n := by
  induction n with
  | zero => simp [reciprocalPowerNumerator]
  | succ n ih =>
    simp only [reciprocalPowerNumerator, eval_sub, eval_mul, eval_C,
      powerDenominator_eval, one_pow, sub_self, mul_zero, zero_sub,
      powerDenominator_derivative_eval_one, ih]
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, pow_succ]
    ring

/-- Bài 22: biểu diễn đa thức tử và giá trị tại 1. -/
theorem reciprocal_power_numerator_solution (k n : ℕ) (hk : 1 ≤ k) (_hn : 1 ≤ n) :
    (∀ x : ℝ, x ^ k - 1 ≠ 0 →
      iteratedDeriv n (fun y : ℝ ↦ 1 / (y ^ k - 1)) x =
        (reciprocalPowerNumerator k n).eval x / (x ^ k - 1) ^ (n + 1)) ∧
      (reciprocalPowerNumerator k n).eval 1 =
        (-1 : ℝ) ^ n * (n.factorial : ℝ) * (k : ℝ) ^ n :=
  ⟨fun x hx ↦ reciprocal_power_iteratedDeriv k n hk x hx,
    reciprocalPowerNumerator_eval_one k n⟩

end calculus.Chapter04.Section01HigherRationalExercises
