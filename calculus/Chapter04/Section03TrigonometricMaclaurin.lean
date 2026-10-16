import calculus.Chapter04.Section03TaylorElementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# §4.3: công thức Maclaurin của sin và cos ở mọi bậc

Nguồn: `C04-S03-display-L1287`, `source/Ch4_hamsokhavi.tex` dòng 1288–1289; điều kiện θ∈(0,1) ở dòng 1294.
-/
set_option autoImplicit false
open Set Finset
open scoped BigOperators
namespace calculus.Chapter04.Section03TrigonometricMaclaurin
open calculus.Chapter04.Section03TaylorElementary


theorem sine_taylor_polynomial_odd (n : ℕ) (x : ℝ) :
    (∑ k ∈ range (2 * n), iteratedDeriv k Real.sin 0 / (k.factorial : ℝ) * x ^ k) =
      ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hEven (k : ℕ) : iteratedDeriv (2 * k) Real.sin 0 = 0 := by
    rw [Real.iteratedDeriv_even_sin]
    simp
  have hOdd (k : ℕ) : iteratedDeriv (2 * k + 1) Real.sin 0 = (-1 : ℝ) ^ k := by
    rw [Real.iteratedDeriv_odd_sin]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    rw [hEven n, hOdd n]
    simp only [zero_div, zero_mul, add_zero]
    ring


theorem cosine_taylor_polynomial_even (n : ℕ) (x : ℝ) :
    (∑ k ∈ range (2 * n + 1), iteratedDeriv k Real.cos 0 / (k.factorial : ℝ) * x ^ k) =
      ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hEven (k : ℕ) : iteratedDeriv (2 * k) Real.cos 0 = (-1 : ℝ) ^ k := by
    rw [Real.iteratedDeriv_even_cos]
    simp
  have hOdd (k : ℕ) : iteratedDeriv (2 * k + 1) Real.cos 0 = 0 := by
    rw [Real.iteratedDeriv_odd_cos]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    rw [hOdd n]
    have hIndex : (2 * n + 1) + 1 = 2 * (n + 1) := by omega
    rw [hIndex, hEven (n + 1)]
    simp only [zero_div, zero_mul, add_zero]
    ring


theorem sine_even_derivative_phase (n : ℕ) (z : ℝ) :
    iteratedDeriv (2 * n) Real.sin z = Real.sin (z + (n : ℝ) * Real.pi) := by
  rw [Real.sin_add_nat_mul_pi]
  simp


theorem cosine_odd_derivative_phase (n : ℕ) (z : ℝ) :
    iteratedDeriv (2 * n + 1) Real.cos z =
      Real.cos (z + ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) := by
  have hd : iteratedDeriv (2 * n + 1) Real.cos z =
      (-1 : ℝ) ^ (n + 1) * Real.sin z := by
    simpa using congrFun (Real.iteratedDeriv_odd_cos n) z
  have hPhase : z + ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 =
      (z + Real.pi / 2) + (n : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hd, hPhase, Real.cos_add_nat_mul_pi, Real.cos_add_pi_div_two, pow_succ]
  ring

/-- Công thức, dòng 1288: khai triển sin; chọn `θ ∈ (0, 1)` sau `n, x`. -/
theorem sine_maclaurin (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.sin x =
        (∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ)) +
        Real.sin (θ * x + (n : ℝ) * Real.pi) * x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  by_cases hx : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [show 2 * n ≠ 0 by omega]
  · have hOrder : 2 * n - 1 + 1 = 2 * n := by omega
    obtain ⟨c, hc, he⟩ := global_taylor_lagrange (2 * n - 1)
      (x₀ := 0) (x := x) Real.contDiff_sin (Ne.symm hx)
    obtain ⟨θ, hθ, hcθ⟩ := between_zero_eq_fraction hx hc
    refine ⟨θ, hθ, ?_⟩
    simpa only [sub_zero, hOrder, sine_taylor_polynomial_odd,
      sine_even_derivative_phase, hcθ] using he

/-- Công thức, dòng 1289: khai triển cos; chọn `θ ∈ (0, 1)` sau `n, x`. -/
theorem cosine_maclaurin (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.cos x =
        (∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * x ^ (2 * k) /
          ((2 * k).factorial : ℝ)) +
        Real.cos (θ * x + ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) *
          x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  by_cases hx : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [sum_range_succ']
    simp [Nat.mul_add]
  · obtain ⟨c, hc, he⟩ := global_taylor_lagrange (2 * n)
      (x₀ := 0) (x := x) Real.contDiff_cos (Ne.symm hx)
    obtain ⟨θ, hθ, hcθ⟩ := between_zero_eq_fraction hx hc
    refine ⟨θ, hθ, ?_⟩
    simpa only [sub_zero, cosine_taylor_polynomial_even,
      cosine_odd_derivative_phase, hcθ] using he

end calculus.Chapter04.Section03TrigonometricMaclaurin
