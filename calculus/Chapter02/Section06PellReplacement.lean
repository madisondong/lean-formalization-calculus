import calculus.Chapter02.Section03

/-!
# Bài tập Pell thay thế

Nguồn: bài thay thế cho C02-S07-exercise-002.
Điều kiện đầu x₀=y₀=1; truy hồi xₙ₊₁=xₙ+2yₙ và yₙ₊₁=xₙ+yₙ.
-/

namespace calculus.Chapter02.Section06PellReplacement

open Filter Topology

variable (x y : ℕ → ℝ)
    (hxzero : x 0 = 1) (hyzero : y 0 = 1)
    (hynext : ∀ n, y (n + 1) = x n + y n)
    (hxnext : ∀ n, x (n + 1) = x n + 2 * y n)

include hxzero hyzero hynext hxnext

/-- Mẫu yₙ của bài thay thế có cận dưới tăng tuyến tính. -/
theorem replacement_lower_bounds (n : ℕ) :
    1 ≤ x n ∧ (n : ℝ) + 1 ≤ y n := by
  induction n with
  | zero => simp [hxzero, hyzero]
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · rw [hxnext n]
      linarith [ih.1, ih.2]
    · rw [hynext n]
      push_cast
      linarith [ih.1, ih.2]

/-- Cả hai dãy đều dương tại mọi chỉ số, kể cả n=0. -/
theorem replacement_positive (n : ℕ) : 0 < x n ∧ 0 < y n := by
  have hb := replacement_lower_bounds x y hxzero hyzero hynext hxnext n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor <;> linarith [hb.1, hb.2]

/-- Mẫu yₙ khác 0 tại mọi chỉ số của bài tập thay thế. -/
theorem replacement_y_ne_zero (n : ℕ) : y n ≠ 0 :=
  ne_of_gt (replacement_positive x y hxzero hyzero hynext hxnext n).2

/-- Đồng nhất thức Pell có dấu luân phiên, bắt đầu từ `1² - 2·1² = -1`. -/
theorem replacement_pell_invariant (n : ℕ) :
    x n ^ 2 - 2 * y n ^ 2 = (-1 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [hxzero, hyzero]
  | succ n ih =>
    rw [hxnext n, hynext n]
    have hsign : (-1 : ℝ) ^ (n + 1 + 1) = -((-1 : ℝ) ^ (n + 1)) := by
      rw [pow_succ]
      ring
    rw [hsign]
    nlinarith [ih]

/-- Cận trên cho sai số của tỉ số xₙ/yₙ. -/
theorem replacement_ratio_error_bound (n : ℕ) :
    |x n / y n - Real.sqrt 2| ≤ 1 / y n := by
  have hb := replacement_lower_bounds x y hxzero hyzero hynext hxnext n
  have hpos := replacement_positive x y hxzero hyzero hynext hxnext n
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsquare : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsum : 1 ≤ x n + Real.sqrt 2 * y n := by
    nlinarith [mul_nonneg hroot hpos.2.le]
  have hprod : (x n - Real.sqrt 2 * y n) * (x n + Real.sqrt 2 * y n) =
      (-1 : ℝ) ^ (n + 1) := by
    calc
      (x n - Real.sqrt 2 * y n) * (x n + Real.sqrt 2 * y n) =
          x n ^ 2 - Real.sqrt 2 ^ 2 * y n ^ 2 := by ring
      _ = x n ^ 2 - 2 * y n ^ 2 := by rw [hsquare]
      _ = (-1 : ℝ) ^ (n + 1) :=
        replacement_pell_invariant x y hxzero hyzero hynext hxnext n
  have habs : |x n - Real.sqrt 2 * y n| * (x n + Real.sqrt 2 * y n) = 1 := by
    calc
      |x n - Real.sqrt 2 * y n| * (x n + Real.sqrt 2 * y n) =
          |(x n - Real.sqrt 2 * y n) * (x n + Real.sqrt 2 * y n)| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ x n + Real.sqrt 2 * y n)]
      _ = |(-1 : ℝ) ^ (n + 1)| := congrArg abs hprod
      _ = 1 := by rw [abs_pow]; norm_num
  have hsmall : |x n - Real.sqrt 2 * y n| ≤ 1 := by
    nlinarith [abs_nonneg (x n - Real.sqrt 2 * y n)]
  have hratio : x n / y n - Real.sqrt 2 = (x n - Real.sqrt 2 * y n) / y n := by
    field_simp [ne_of_gt hpos.2]
  rw [hratio, abs_div, abs_of_pos hpos.2]
  exact div_le_div_of_nonneg_right hsmall hpos.2.le

/-- Tỉ số của bài tập thay thế hội tụ về `√2`; mọi mẫu đều khác 0. -/
theorem replacement_ratio_tendsto :
    Tendsto (fun n => x n / y n) atTop (𝓝 (Real.sqrt 2)) := by
  apply calculus.Chapter02.Section03.convergesTo_iff_tendsto.mp
  apply calculus.Chapter02.Section03.convergesTo_of_error_le_const_div
    (C := 1) (by norm_num)
  intro n hn
  have hb := replacement_lower_bounds x y hxzero hyzero hynext hxnext n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    |x n / y n - Real.sqrt 2| ≤ 1 / y n :=
      replacement_ratio_error_bound x y hxzero hyzero hynext hxnext n
    _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos (by linarith [hb.2])

end calculus.Chapter02.Section06PellReplacement
