import calculus.Chapter04.Section03TrigonometricMaclaurin
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Real.Irrational

/-!
# §4.3, Bài 30(a): sin 1 là số vô tỉ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1365–1372, phần (a) tại dòng 1368.
-/
set_option autoImplicit false
open Set Finset
open scoped BigOperators
namespace calculus.Chapter04.Section03SineIrrationalExercise
open calculus.Chapter04.Section03TrigonometricMaclaurin


noncomputable def sinePartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k / ((2 * k + 1).factorial : ℝ)


def factorialScaledSinePartialSum (n : ℕ) : ℤ :=
  ∑ k ∈ range n, (-1 : ℤ) ^ k * (Nat.factorial (2 * n) / Nat.factorial (2 * k + 1) : ℕ)


theorem factorialScaledSinePartialSum_cast (n : ℕ) :
    (factorialScaledSinePartialSum n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) * sinePartialSum n := by
  rw [factorialScaledSinePartialSum, Int.cast_sum, sinePartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : 2 * k + 1 ≤ 2 * n := by
    have hk' := Finset.mem_range.mp hk
    omega
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkn)
    (by positivity : (Nat.factorial (2 * k + 1) : ℝ) ≠ 0)]
  ring


theorem factorial_mul_sine_remainder (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (2 * n) : ℝ) * (Real.sin 1 - sinePartialSum n) ≠ 0 ∧
      |(Nat.factorial (2 * n) : ℝ) * (Real.sin 1 - sinePartialSum n)| < 1 := by
  obtain ⟨θ, hθ, he⟩ := sine_maclaurin n hn 1
  simp only [one_pow, mul_one] at he
  change Real.sin 1 = sinePartialSum n +
    Real.sin (θ + (n : ℝ) * Real.pi) / (Nat.factorial (2 * n) : ℝ) at he
  have hdiff : Real.sin 1 - sinePartialSum n =
      Real.sin (θ + (n : ℝ) * Real.pi) / (Nat.factorial (2 * n) : ℝ) := by
    linarith
  have hFact : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
  have hr : (Nat.factorial (2 * n) : ℝ) * (Real.sin 1 - sinePartialSum n) =
      Real.sin (θ + (n : ℝ) * Real.pi) := by
    rw [hdiff]
    field_simp [hFact]
  have hθπ : θ < Real.pi := by linarith [hθ.2, Real.pi_gt_three]
  have hpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθπ
  have hPiTwo : 1 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsinLt : Real.sin θ < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [hθ.1, Real.pi_pos] : -(Real.pi / 2) ≤ θ)
      (le_rfl : Real.pi / 2 ≤ Real.pi / 2) (hθ.2.trans hPiTwo)
  constructor
  · rw [hr, Real.sin_add_nat_mul_pi]
    exact mul_ne_zero (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hpos.ne'
  · rw [hr, Real.sin_add_nat_mul_pi, abs_mul, abs_pow]
    norm_num only [abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos hpos]
    exact hsinLt

/-- Bài 4.3.30(a): `sin 1` là số vô tỉ. -/
theorem irrational_sin_one : Irrational (Real.sin 1) := by
  rintro ⟨q, hq⟩
  let n : ℕ := q.den + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdenn : q.den ≤ 2 * n := by dsimp [n]; omega
  have hdiv : q.den ∣ Nat.factorial (2 * n) := Nat.dvd_factorial q.den_pos hdenn
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hscaled : (Nat.factorial (2 * n) : ℝ) * Real.sin 1 =
      ((q.num * (Nat.factorial (2 * n) / q.den : ℕ) : ℤ) : ℝ) := by
    rw [← hq, Rat.cast_def, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdiv hden0]
    ring
  let z : ℤ := q.num * (Nat.factorial (2 * n) / q.den : ℕ) -
    factorialScaledSinePartialSum n
  have hz : (z : ℝ) = (Nat.factorial (2 * n) : ℝ) * (Real.sin 1 - sinePartialSum n) := by
    calc
      (z : ℝ) = ((q.num * (Nat.factorial (2 * n) / q.den : ℕ) : ℤ) : ℝ) -
          (factorialScaledSinePartialSum n : ℝ) := by
        simp only [z, Int.cast_sub]
      _ = (Nat.factorial (2 * n) : ℝ) * Real.sin 1 -
          (Nat.factorial (2 * n) : ℝ) * sinePartialSum n := by
        rw [← hscaled, factorialScaledSinePartialSum_cast]
      _ = (Nat.factorial (2 * n) : ℝ) * (Real.sin 1 - sinePartialSum n) := by ring
  obtain ⟨hne, hlt⟩ := factorial_mul_sine_remainder n hn
  have hzltR : |(z : ℝ)| < 1 := by rw [hz]; exact hlt
  have hzlt : |z| < (1 : ℤ) := by exact_mod_cast hzltR
  have hzero : z = 0 := by
    have hzbound := abs_lt.mp hzlt
    omega
  exact hne (by rw [← hz, hzero]; norm_num)

end calculus.Chapter04.Section03SineIrrationalExercise
