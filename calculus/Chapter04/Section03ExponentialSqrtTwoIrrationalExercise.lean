import calculus.Chapter04.Section03TaylorElementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational

/-!
# §4.3, Bài 30(b): exp(sqrt 2) là số vô tỉ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1370.
-/
set_option autoImplicit false
open Set Finset
open scoped BigOperators
namespace calculus.Chapter04.Section03ExponentialSqrtTwoIrrationalExercise
open calculus.Chapter04.Section03TaylorElementary

/-- Dãy số nguyên `Aₙ = (2n)!/2ⁿ`. -/
def coshSqrtTwoDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * (2 * n + 1) * coshSqrtTwoDenominator n


theorem coshSqrtTwoDenominator_pos (n : ℕ) : 0 < coshSqrtTwoDenominator n := by
  induction n with
  | zero => norm_num [coshSqrtTwoDenominator]
  | succ n ih =>
    rw [coshSqrtTwoDenominator]
    positivity


theorem coshSqrtTwoDenominator_dvd_succ (n : ℕ) :
    coshSqrtTwoDenominator n ∣ coshSqrtTwoDenominator (n + 1) := by
  refine ⟨(n + 1) * (2 * n + 1), ?_⟩
  rw [coshSqrtTwoDenominator]
  ring


theorem coshSqrtTwoDenominator_dvd {k n : ℕ} (hkn : k ≤ n) :
    coshSqrtTwoDenominator k ∣ coshSqrtTwoDenominator n := by
  induction hkn with
  | refl => exact dvd_rfl
  | step _ ih => exact Nat.dvd_trans ih (coshSqrtTwoDenominator_dvd_succ _)


theorem factorial_dvd_coshSqrtTwoDenominator (n : ℕ) :
    Nat.factorial n ∣ coshSqrtTwoDenominator n := by
  induction n with
  | zero => simp [coshSqrtTwoDenominator]
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(2 * n + 1) * d, ?_⟩
    rw [coshSqrtTwoDenominator, Nat.factorial_succ, hd]
    ring


theorem factorial_two_mul_eq (n : ℕ) :
    Nat.factorial (2 * n) = 2 ^ n * coshSqrtTwoDenominator n := by
  induction n with
  | zero => simp [coshSqrtTwoDenominator]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, ih, coshSqrtTwoDenominator, pow_succ]
    ring


theorem power_two_div_factorial_eq (k : ℕ) :
    (2 : ℝ) ^ k / (Nat.factorial (2 * k) : ℝ) = 1 / (coshSqrtTwoDenominator k : ℝ) := by
  have hA : (coshSqrtTwoDenominator k : ℝ) ≠ 0 := by
    exact_mod_cast (coshSqrtTwoDenominator_pos k).ne'
  have hPow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  rw [factorial_two_mul_eq]
  push_cast
  field_simp [hA, hPow]


noncomputable def coshSqrtTwoPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), 1 / (coshSqrtTwoDenominator k : ℝ)


def denominatorScaledCoshSqrtTwoPartialSum (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), coshSqrtTwoDenominator n / coshSqrtTwoDenominator k


theorem denominatorScaledCoshSqrtTwoPartialSum_cast (n : ℕ) :
    (denominatorScaledCoshSqrtTwoPartialSum n : ℝ) =
      (coshSqrtTwoDenominator n : ℝ) * coshSqrtTwoPartialSum n := by
  rw [denominatorScaledCoshSqrtTwoPartialSum, Nat.cast_sum, coshSqrtTwoPartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have hk' := mem_range.mp hk
    omega
  have hA : (coshSqrtTwoDenominator k : ℝ) ≠ 0 := by
    exact_mod_cast (coshSqrtTwoDenominator_pos k).ne'
  rw [Nat.cast_div (coshSqrtTwoDenominator_dvd hkn) hA]
  ring


theorem cosh_taylor_polynomial_even (n : ℕ) (x : ℝ) :
    (∑ k ∈ range (2 * n + 1), iteratedDeriv k Real.cosh 0 / (k.factorial : ℝ) * x ^ k) =
      ∑ k ∈ range (n + 1), x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hEven (k : ℕ) : iteratedDeriv (2 * k) Real.cosh 0 = 1 := by
    rw [Real.iteratedDeriv_even_cosh]
    simp
  have hOdd (k : ℕ) : iteratedDeriv (2 * k + 1) Real.cosh 0 = 0 := by
    rw [Real.iteratedDeriv_odd_cosh]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    rw [hOdd n, show (2 * n + 1) + 1 = 2 * (n + 1) by omega, hEven (n + 1)]
    simp only [zero_div, zero_mul, add_zero]
    ring


theorem cosh_sqrt_two_taylor_polynomial (n : ℕ) :
    (∑ k ∈ range (2 * n + 1 + 1), iteratedDeriv k Real.cosh 0 / (k.factorial : ℝ) *
      Real.sqrt 2 ^ k) = coshSqrtTwoPartialSum n := by
  have hOdd : iteratedDeriv (2 * n + 1) Real.cosh 0 = 0 := by
    rw [Real.iteratedDeriv_odd_cosh]
    simp
  rw [sum_range_succ, cosh_taylor_polynomial_even, hOdd]
  simp only [zero_div, zero_mul, add_zero, coshSqrtTwoPartialSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), power_two_div_factorial_eq]


theorem denominator_mul_cosh_remainder_eq (n : ℕ) :
    ∃ c ∈ Ioo (0 : ℝ) (Real.sqrt 2),
      (coshSqrtTwoDenominator n : ℝ) * (Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n) =
        2 * Real.cosh c / (((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨c, hc, he⟩ := global_taylor_lagrange (2 * n + 1)
    (x₀ := 0) (x := Real.sqrt 2) Real.contDiff_cosh hs.ne
  have hc' : c ∈ Ioo (0 : ℝ) (Real.sqrt 2) := by
    simpa only [uIoo_of_lt hs] using hc
  rw [sub_zero, cosh_sqrt_two_taylor_polynomial] at he
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, Real.iteratedDeriv_even_cosh,
    pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at he
  have hdiff : Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n =
      Real.cosh c * (2 : ℝ) ^ (n + 1) / (Nat.factorial (2 * (n + 1)) : ℝ) := by
    linarith only [he]
  have hA : (coshSqrtTwoDenominator n : ℝ) ≠ 0 := by
    exact_mod_cast (coshSqrtTwoDenominator_pos n).ne'
  have hPow : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hN : (n : ℝ) + 1 ≠ 0 := by positivity
  have hOdd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hEven : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  refine ⟨c, hc', ?_⟩
  rw [hdiff, factorial_two_mul_eq, coshSqrtTwoDenominator]
  push_cast
  field_simp [hA, hPow, hN, hOdd, hEven]


theorem exponential_two_lt_nine : Real.exp 2 < 9 := by
  have he : Real.exp 2 = Real.exp 1 ^ 2 := by
    simp
  rw [he]
  calc
    Real.exp 1 ^ 2 < (3 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (Real.exp_pos 1).le (by norm_num : (0 : ℝ) ≤ 3)).mpr
        Real.exp_one_lt_three
    _ = 9 := by norm_num


theorem denominator_mul_cosh_remainder (n : ℕ) (hn : 2 ≤ n) :
    0 < (coshSqrtTwoDenominator n : ℝ) * (Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n) ∧
      (coshSqrtTwoDenominator n : ℝ) * (Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n) < 1 := by
  obtain ⟨c, hc, hr⟩ := denominator_mul_cosh_remainder_eq n
  have hs2 : Real.sqrt 2 < (2 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc2 : c < 2 := hc.2.trans hs2
  have hneg : Real.exp (-c) < Real.exp c := Real.exp_strictMono (by linarith [hc.1])
  have hcosh : Real.cosh c < Real.exp c := by
    rw [Real.cosh_eq]
    linarith only [hneg]
  have hbound : Real.cosh c < 9 :=
    (hcosh.trans (Real.exp_strictMono hc2)).trans exponential_two_lt_nine
  have hD : 0 < ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hD18 : (18 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
  constructor
  · rw [hr]
    exact div_pos (mul_pos (by norm_num) (Real.cosh_pos c)) hD
  · rw [hr]
    apply (div_lt_one hD).mpr
    nlinarith only [hbound, hD18]


theorem irrational_cosh_sqrt_two : Irrational (Real.cosh (Real.sqrt 2)) := by
  rintro ⟨q, hq⟩
  let n : ℕ := q.den + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hdenn : q.den ≤ n := by dsimp [n]; omega
  have hdiv : q.den ∣ coshSqrtTwoDenominator n :=
    (Nat.dvd_factorial q.den_pos hdenn).trans (factorial_dvd_coshSqrtTwoDenominator n)
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hscaled : (coshSqrtTwoDenominator n : ℝ) * Real.cosh (Real.sqrt 2) =
      ((q.num * (coshSqrtTwoDenominator n / q.den : ℕ) : ℤ) : ℝ) := by
    rw [← hq, Rat.cast_def, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdiv hden0]
    ring
  let z : ℤ := q.num * (coshSqrtTwoDenominator n / q.den : ℕ) -
    (denominatorScaledCoshSqrtTwoPartialSum n : ℕ)
  have hz : (z : ℝ) = (coshSqrtTwoDenominator n : ℝ) *
      (Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n) := by
    calc
      (z : ℝ) = ((q.num * (coshSqrtTwoDenominator n / q.den : ℕ) : ℤ) : ℝ) -
          (denominatorScaledCoshSqrtTwoPartialSum n : ℝ) := by
        simp only [z, Int.cast_sub, Int.cast_natCast]
      _ = (coshSqrtTwoDenominator n : ℝ) * Real.cosh (Real.sqrt 2) -
          (coshSqrtTwoDenominator n : ℝ) * coshSqrtTwoPartialSum n := by
        rw [← hscaled, denominatorScaledCoshSqrtTwoPartialSum_cast]
      _ = (coshSqrtTwoDenominator n : ℝ) * (Real.cosh (Real.sqrt 2) - coshSqrtTwoPartialSum n) := by ring
  obtain ⟨hlo, hhi⟩ := denominator_mul_cosh_remainder n hn
  have hzposR : (0 : ℝ) < (z : ℝ) := by rw [hz]; exact hlo
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hzone : (1 : ℤ) ≤ z := by omega
  have hzoneR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzone
  rw [hz] at hzoneR
  exact not_lt_of_ge hzoneR hhi

/-- Bài 4.3.30(b): `exp(√2)` là số vô tỉ. -/
theorem irrational_exp_sqrt_two : Irrational (Real.exp (Real.sqrt 2)) := by
  rintro ⟨q, hq⟩
  apply irrational_cosh_sqrt_two
  refine ⟨(q + q⁻¹) / 2, ?_⟩
  push_cast
  rw [Real.cosh_eq, Real.exp_neg, ← hq]

end calculus.Chapter04.Section03ExponentialSqrtTwoIrrationalExercise
