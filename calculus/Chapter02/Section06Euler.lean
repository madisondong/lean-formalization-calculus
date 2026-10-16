import calculus.Chapter02.Section06
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.Real.Irrational

/-!
# Ví dụ 2.6.9: tính tăng và tính vô tỉ của e

Nguồn: `source/Ch2_dayso.tex`, dòng 1938–1951.
-/

set_option autoImplicit false

namespace calculus.Chapter02.Section06Euler

open Set Filter
open scoped Topology

/-- Dãy định nghĩa e tại n≥1. -/
noncomputable def eulerApprox (n : ℕ) : ℝ := (1 + 1 / (n : ℝ)) ^ n

/-- Dòng 1941: aₙ≤aₙ₊₁ tại mọi n≥1. -/
theorem eulerApprox_le_succ (n : ℕ) (hn : 1 ≤ n) : eulerApprox n ≤ eulerApprox (n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbase : 0 ≤ 1 + 1 / (n : ℝ) := by positivity
  have hweights : 1 / ((n : ℝ) + 1) + (n : ℝ) / ((n : ℝ) + 1) = 1 := by
    field_simp
    ring
  have hagm := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 / ((n : ℝ) + 1)) (w₂ := (n : ℝ) / ((n : ℝ) + 1))
    (p₁ := 1) (p₂ := 1 + 1 / (n : ℝ))
    (by positivity) (by positivity) zero_le_one hbase hweights
  have harith : 1 / ((n : ℝ) + 1) * 1 +
      ((n : ℝ) / ((n : ℝ) + 1)) * (1 + 1 / (n : ℝ)) =
      1 + 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  simp only [Real.one_rpow, one_mul] at hagm
  rw [harith] at hagm
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hbase _) hagm (n + 1)
  have hleft : ((1 + 1 / (n : ℝ)) ^ ((n : ℝ) / ((n : ℝ) + 1))) ^ (n + 1) =
      (1 + 1 / (n : ℝ)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    have he : (n : ℝ) / ((n : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) = n := by
      push_cast
      field_simp
    rw [he, Real.rpow_natCast]
  rw [hleft] at hpow
  simpa [eulerApprox] using hpow

/-- Dãy định nghĩa e tăng. -/
theorem eulerApprox_increasing : Section06.SequenceIncreasing eulerApprox := eulerApprox_le_succ

/-- Tổng riêng Taylor của exp(1) gồm các chỉ số 0,…,n. -/
noncomputable def eulerPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℝ)


theorem eulerPartialSum_lt_exp_one (n : ℕ) : eulerPartialSum n < Real.exp 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one (n + 2)
  have hp : 0 < 1 / (Nat.factorial (n + 1) : ℝ) := by positivity
  simp only [one_pow] at hsum
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ] at hsum
  change eulerPartialSum n + 1 / (Nat.factorial (n + 1) : ℝ) ≤ Real.exp 1 at hsum
  linarith


theorem factorial_mul_euler_remainder (n : ℕ) (hn : 1 ≤ n) :
    0 < (Nat.factorial n : ℝ) * (Real.exp 1 - eulerPartialSum n) ∧
      (Nat.factorial n : ℝ) * (Real.exp 1 - eulerPartialSum n) < 1 := by
  have hf : (0 : ℝ) < Nat.factorial n := by positivity
  constructor
  · exact mul_pos hf (sub_pos.mpr (eulerPartialSum_lt_exp_one n))
  · have hbound := Real.exp_bound (x := (1 : ℝ)) (n := n + 1) (by norm_num) (by omega)
    simp only [abs_one, one_pow, one_mul] at hbound
    change |Real.exp 1 - eulerPartialSum n| ≤
      ((n + 1 + 1 : ℕ) : ℝ) / ((Nat.factorial (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ)) at hbound
    have hu := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbound) hf.le
    have hid : (Nat.factorial n : ℝ) *
        (((n + 1 + 1 : ℕ) : ℝ) / ((Nat.factorial (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ))) =
        ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [hid] at hu
    apply hu.trans_lt
    apply (div_lt_one (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mpr
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- Tổng riêng Taylor nhân n! là số nguyên. -/
def factorialScaledPartialSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.factorial n / Nat.factorial k


theorem factorialScaledPartialSum_cast (n : ℕ) :
    (factorialScaledPartialSum n : ℝ) = (Nat.factorial n : ℝ) * eulerPartialSum n := by
  rw [factorialScaledPartialSum, Nat.cast_sum, eulerPartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkn) (by positivity : (Nat.factorial k : ℝ) ≠ 0)]
  ring

/-- e=exp(1) là số vô tỉ. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  let n : ℕ := q.den + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdenn : q.den ≤ n := by dsimp [n]; omega
  have hdiv : q.den ∣ Nat.factorial n := Nat.dvd_factorial q.den_pos hdenn
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hscaled : (Nat.factorial n : ℝ) * Real.exp 1 =
      ((q.num * (Nat.factorial n / q.den : ℕ) : ℤ) : ℝ) := by
    rw [← hq, Rat.cast_def, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdiv hden0]
    ring
  let z : ℤ := q.num * (Nat.factorial n / q.den : ℕ) - (factorialScaledPartialSum n : ℕ)
  have hz : (z : ℝ) = (Nat.factorial n : ℝ) * (Real.exp 1 - eulerPartialSum n) := by
    calc
      (z : ℝ) = ((q.num * (Nat.factorial n / q.den : ℕ) : ℤ) : ℝ) -
          (factorialScaledPartialSum n : ℝ) := by
        simp only [z, Int.cast_sub, Int.cast_natCast]
      _ = (Nat.factorial n : ℝ) * Real.exp 1 -
          (Nat.factorial n : ℝ) * eulerPartialSum n := by
        rw [← hscaled, factorialScaledPartialSum_cast]
      _ = (Nat.factorial n : ℝ) * (Real.exp 1 - eulerPartialSum n) := by ring
  obtain ⟨hlo, hhi⟩ := factorial_mul_euler_remainder n hn
  have hzposR : (0 : ℝ) < (z : ℝ) := by rw [hz]; exact hlo
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hzone : (1 : ℤ) ≤ z := by omega
  have hzoneR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzone
  rw [hz] at hzoneR
  exact not_lt_of_ge hzoneR hhi

/-- Ví dụ 2.6.9: dãy tăng, hội tụ về e<3; e vô tỉ và có 12 chữ số sau dấu phẩy như trong bảng. -/
theorem euler_example_complete :
    Section06.SequenceIncreasing eulerApprox ∧
      Section03.ConvergesTo eulerApprox (Real.exp 1) ∧
      (∀ n : ℕ, 1 ≤ n → eulerApprox n < 3) ∧
      ((2718281828459 : ℝ) / 10 ^ 12 < Real.exp 1 ∧
        Real.exp 1 < (2718281828460 : ℝ) / 10 ^ 12) ∧
      Irrational (Real.exp 1) := by
  exact ⟨eulerApprox_increasing, Section06.euler_sequence_converges,
    Section06.euler_sequence_lt_three, Section06.euler_printed_decimal_interval, irrational_exp_one⟩

end calculus.Chapter02.Section06Euler
