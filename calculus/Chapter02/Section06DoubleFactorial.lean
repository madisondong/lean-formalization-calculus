import calculus.Chapter02.Section06
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Mục 2.6: giai thừa kép

Nguồn: `source/Ch2_dayso.tex`, dòng 2038–2043; Bài 2.6.7(a,b).
-/
namespace calculus.Chapter02.Section06DoubleFactorial
open Filter
open scoped Topology BigOperators
open calculus.Chapter02.Section03 calculus.Chapter02.Section06

/-- Giai thừa kép lẻ: 1·3·5·…·(2n+1). -/
theorem odd_double_factorial_eq_product (n : ℕ) :
    ((2 * n + 1).doubleFactorial : ℝ) =
      1 * ∏ k ∈ Finset.range n, (2 * ((k : ℝ) + 1) + 1) := by
  simp [Nat.doubleFactorial_eq_prod_odd, Nat.cast_prod]

/-- Giai thừa kép chẵn: 2·4·6·…·(2n). -/
theorem even_double_factorial_eq_product (n : ℕ) :
    ((2 * n).doubleFactorial : ℝ) =
      ∏ k ∈ Finset.range n, 2 * ((k : ℝ) + 1) := by
  simp [Nat.doubleFactorial_eq_prod_even, Nat.cast_prod]

/-- Bài 2.6.7(a): dãy n!/(2n+1)!!. -/
noncomputable def factorialOddDoubleFactorialRatio (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((2 * n + 1).doubleFactorial : ℝ)

/-- Bài 2.6.7(b): dãy (2n)!!/(2n+1)!!. -/
noncomputable def evenOddDoubleFactorialRatio (n : ℕ) : ℝ :=
  ((2 * n).doubleFactorial : ℝ) / ((2 * n + 1).doubleFactorial : ℝ)

/-- Mọi mẫu lẻ và tử n! đều dương. -/
theorem factorial_odd_double_factorial_ratio_pos (n : ℕ) : 0 < factorialOddDoubleFactorialRatio n := by
  apply div_pos
  · exact_mod_cast Nat.factorial_pos n
  · exact_mod_cast Nat.doubleFactorial_pos (2 * n + 1)

/-- Mọi tử chẵn và mẫu lẻ đều dương. -/
theorem even_odd_double_factorial_ratio_pos (n : ℕ) : 0 < evenOddDoubleFactorialRatio n := by
  apply div_pos
  · exact_mod_cast Nat.doubleFactorial_pos (2 * n)
  · exact_mod_cast Nat.doubleFactorial_pos (2 * n + 1)

/-- Truy hồi của tỉ số n!/(2n+1)!!. -/
theorem factorial_odd_double_factorial_ratio_successor (n : ℕ) :
    factorialOddDoubleFactorialRatio (n + 1) =
      factorialOddDoubleFactorialRatio n * (((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) := by
  unfold factorialOddDoubleFactorialRatio
  rw [Nat.factorial_succ, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
    Nat.doubleFactorial_add_two]
  push_cast
  field_simp; ring

/-- Truy hồi của tỉ số (2n)!!/(2n+1)!!. -/
theorem even_odd_double_factorial_ratio_successor (n : ℕ) :
    evenOddDoubleFactorialRatio (n + 1) =
      evenOddDoubleFactorialRatio n * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) := by
  unfold evenOddDoubleFactorialRatio
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
    show 2 * (n + 1) = 2 * n + 2 by omega,
    Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two]
  push_cast
  field_simp; ring

/-- Bài 2.6.7(a): dãy giảm ngặt tại n≥1. -/
theorem factorial_odd_double_factorial_ratio_strict_decrease :
    ∀ n : ℕ, 1 ≤ n → factorialOddDoubleFactorialRatio (n + 1) < factorialOddDoubleFactorialRatio n := by
  intro n _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfac : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  rw [factorial_odd_double_factorial_ratio_successor]
  simpa using mul_lt_mul_of_pos_left hfac (factorial_odd_double_factorial_ratio_pos n)

/-- Bài 2.6.7(a): dãy giảm. -/
theorem factorial_odd_double_factorial_ratio_sequenceDecreasing : SequenceDecreasing factorialOddDoubleFactorialRatio :=
  fun n hn => (factorial_odd_double_factorial_ratio_strict_decrease n hn).le

/-- Cận hình học của n!/(2n+1)!!. -/
theorem factorial_odd_double_factorial_ratio_geometric_bound (n : ℕ) :
    factorialOddDoubleFactorialRatio n ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [factorialOddDoubleFactorialRatio, Nat.doubleFactorial]
  | succ n ih =>
    have hfac : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ 1 / 2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    rw [factorial_odd_double_factorial_ratio_successor, pow_succ]
    calc
      factorialOddDoubleFactorialRatio n * (((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) ≤
          (1 / 2 : ℝ) ^ n * (((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ n * (1 / 2) := mul_le_mul_of_nonneg_left hfac (by positivity)

/-- Bài 2.6.7(a): n!/(2n+1)!! hội tụ về 0. -/
theorem factorial_odd_double_factorial_ratio_converges : ConvergesTo factorialOddDoubleFactorialRatio 0 := by
  have hgeom : ConvergesTo (fun n : ℕ => (1 / 2 : ℝ) ^ n) 0 :=
    convergesTo_iff_tendsto.mpr (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num))
  apply convergesTo_of_error_le (fun n _ => by positivity) hgeom (show (0 : ℝ) < 1 by norm_num)
  intro n _
  simpa only [sub_zero, abs_of_pos (factorial_odd_double_factorial_ratio_pos n), one_mul] using
    factorial_odd_double_factorial_ratio_geometric_bound n

/-- Bài 2.6.7(b): dãy giảm ngặt. -/
theorem even_odd_double_factorial_ratio_strict_decrease :
    ∀ n : ℕ, 1 ≤ n → evenOddDoubleFactorialRatio (n + 1) < evenOddDoubleFactorialRatio n := by
  intro n _
  have hfac : (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  rw [even_odd_double_factorial_ratio_successor]
  simpa using mul_lt_mul_of_pos_left hfac (even_odd_double_factorial_ratio_pos n)

/-- Bài 2.6.7(b): dãy giảm. -/
theorem even_odd_double_factorial_ratio_sequenceDecreasing : SequenceDecreasing evenOddDoubleFactorialRatio :=
  fun n hn => (even_odd_double_factorial_ratio_strict_decrease n hn).le

/-- Cận trên cho bình phương của (2n)!!/(2n+1)!!. -/
theorem even_odd_double_factorial_ratio_square_bound (n : ℕ) :
    evenOddDoubleFactorialRatio n ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [evenOddDoubleFactorialRatio, Nat.doubleFactorial]
  | succ n ih =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hfac : ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) ^ 2 ≤
        ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [div_pow]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    rw [even_odd_double_factorial_ratio_successor, mul_pow]
    calc
      evenOddDoubleFactorialRatio n ^ 2 * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) ^ 2 ≤
          (1 / ((n : ℝ) + 1)) * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) ^ 2 :=
        mul_le_mul_of_nonneg_right ih (sq_nonneg _)
      _ ≤ (1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        field_simp; ring

/-- Bài 2.6.7(b): (2n)!!/(2n+1)!! hội tụ về 0. -/
theorem even_odd_double_factorial_ratio_converges : ConvergesTo evenOddDoubleFactorialRatio 0 := by
  have hrec : ConvergesTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using successor_converges reciprocal_converges
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := hrec (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, hN, fun n hn => ?_⟩
  have hsmall' : 1 / ((n : ℝ) + 1) < ε ^ 2 := by
    simpa only [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))] using hsmall n hn
  have hb := even_odd_double_factorial_ratio_square_bound n
  have hp := even_odd_double_factorial_ratio_pos n
  rw [sub_zero, abs_of_pos hp]
  nlinarith

end calculus.Chapter02.Section06DoubleFactorial
