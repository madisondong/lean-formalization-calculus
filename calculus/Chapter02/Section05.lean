import calculus.Chapter02.Section04
import calculus.Chapter02.Section01Exercises
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

/-!
# 2.5. Các phép toán trên dãy hội tụ

Nguồn: `source/Ch2_dayso.tex`, dòng 1644–1873.
-/

namespace calculus.Chapter02.Section05

open Filter Set
open scoped Topology BigOperators
open calculus.Chapter02.Section03


theorem positive_cast (n : ℕ) (hn : 1 ≤ n) : 0 < (n : ℝ) := by
  exact_mod_cast (by omega : 0 < n)


theorem ratio_normalize (A B x y c : ℝ) (hc : c ≠ 0)
    (hx : x = A * c) (hy : y = B * c) : x / y = A / B := by
  rw [hx, hy, mul_div_mul_right _ _ hc]

/-- Định lí 2.5.1(i): giới hạn của tổng. -/
theorem add_converges {u v : ℕ → ℝ} {a b : ℝ}
    (hu : ConvergesTo u a) (hv : ConvergesTo v b) :
    ConvergesTo (fun n ↦ u n + v n) (a + b) :=
  convergesTo_iff_tendsto.mpr ((convergesTo_iff_tendsto.mp hu).add
    (convergesTo_iff_tendsto.mp hv))

/-- Định lí 2.5.1(ii): nhân với hằng số thực bất kỳ. -/
theorem const_mul_converges {u : ℕ → ℝ} {a : ℝ} (hu : ConvergesTo u a) (c : ℝ) :
    ConvergesTo (fun n ↦ c * u n) (c * a) :=
  convergesTo_iff_tendsto.mpr ((convergesTo_iff_tendsto.mp hu).const_mul c)

/-- Định lí 2.5.1(iii): giới hạn của tích. -/
theorem mul_converges {u v : ℕ → ℝ} {a b : ℝ}
    (hu : ConvergesTo u a) (hv : ConvergesTo v b) :
    ConvergesTo (fun n ↦ u n * v n) (a * b) :=
  convergesTo_iff_tendsto.mpr ((convergesTo_iff_tendsto.mp hu).mul
    (convergesTo_iff_tendsto.mp hv))

/-- Định lí 2.5.1(iv): giới hạn của thương, với mẫu khác 0 tại mọi n≥1. -/
theorem div_converges {u v : ℕ → ℝ} {a b : ℝ}
    (hu : ConvergesTo u a) (hv : ConvergesTo v b) (hb : b ≠ 0)
    (_hv : ∀ n : ℕ, 1 ≤ n → v n ≠ 0) :
    ConvergesTo (fun n ↦ u n / v n) (a / b) := by
  apply convergesTo_iff_tendsto.mpr
  simpa using! (convergesTo_iff_tendsto.mp hu).div (convergesTo_iff_tendsto.mp hv) hb

/-- Định lí 2.5.1(iv): sai số bằng 0 là phản ví dụ cho dấu < trong lời giải. -/
theorem reciprocal_strict_bound_counterexample :
    ¬ |1 / (1 : ℝ) - 1 / 1| < 2 * |1 - 1| / 1 ^ 2 := by norm_num

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S05-theorem-001.proof-strict-reciprocal-bound: cận sai số nghịch đảo dùng dấu `≤`. -/
theorem reciprocal_error_nonstrict (b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbound : |b| / 2 ≤ |c|) :
    |1 / c - 1 / b| ≤ 2 * |c - b| / b ^ 2 := by
  have heq : 1 / c - 1 / b = (b - c) / (c * b) := by field_simp
  rw [heq, abs_div, abs_mul, abs_sub_comm]
  apply (div_le_div_iff₀ (mul_pos (abs_pos.mpr hc) (abs_pos.mpr hb))
    (sq_pos_of_ne_zero hb)).mpr
  have hscaled := mul_le_mul_of_nonneg_right hbound
    (show 0 ≤ 2 * |c - b| * |b| by positivity)
  have hsq := congrArg (fun t : ℝ ↦ |c - b| * t) (sq_abs b)
  nlinarith [hscaled, hsq]

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S05-theorem-001.proof-strict-reciprocal-bound, dòng 1679–1684: cận ngặt cho sai số nghịch đảo trong lời giải gốc. -/
theorem source_reciprocal_strict_error_bound (b c : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hclose : |c - b| < |b| / 2) :
    |1 / c - 1 / b| < 2 * |c - b| / b ^ 2 := by
  sorry

/-- Mẫu của các phân thức đa thức khác 0 tại n≥1. -/
theorem polynomial_denominators_valid (n : ℕ) (hn : 1 ≤ n) :
    1-3 * (n : ℝ) ^ 3 ≠ 0 ∧ 0 < 3-2 * (n : ℝ) + (n : ℝ) ^ 2 ∧
      0 < 3-2 * (n : ℝ) + (n : ℝ) ^ 3 := by
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ)-1)]
  have h3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr h1)]
  constructor
  · nlinarith
  · constructor <;> nlinarith [sq_nonneg ((n : ℝ)-1)]

/-- Ví dụ 2.5.2: giới hạn bằng −1/3. -/
theorem cubic_rational_converges :
    ConvergesTo (fun n ↦ ((n : ℝ) ^ 3 + n ^ 2 + 1) / (1 - 3 * n ^ 3)) (-1 / 3) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ (1 + 1 / (n : ℝ) + (1 / (n : ℝ)) ^ 3) /
      ((1 / (n : ℝ)) ^ 3 - 3)) atTop (𝓝 (-1 / 3)) := by
    convert! ((tendsto_const_nhds.add h).add (h.pow 3)).div
      ((h.pow 3).sub_const 3) (by norm_num : (0 : ℝ) ^ 3-3 ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  symm
  apply ratio_normalize _ _ _ _ ((n : ℝ) ^ 3) (pow_ne_zero 3 hn0)
  · field_simp
  · field_simp

/-- Ví dụ 2.5.3: giới hạn bằng −1/2. -/
theorem geometric_rational_converges :
    ConvergesTo (fun n ↦ (5 + (2 : ℝ) ^ n - 7 ^ n) / (3 + 6 ^ n + 2 * 7 ^ n)) (-1 / 2) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 7 : ℝ)| < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2 / 7 : ℝ)| < 1)
  have h6 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(6 / 7 : ℝ)| < 1)
  have H : Tendsto (fun n : ℕ ↦ (5 * (1 / 7 : ℝ) ^ n + (2 / 7) ^ n-1) /
      (3 * (1 / 7 : ℝ) ^ n + (6 / 7) ^ n + 2)) atTop (𝓝 (-1 / 2)) := by
    convert! ((h1.const_mul 5).add h2 |>.sub_const 1).div
      (((h1.const_mul 3).add h6).add_const 2) (by norm_num : (3 * 0 + 0 + 2 : ℝ) ≠ 0)
      using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n _
  symm
  apply ratio_normalize _ _ _ _ ((7 : ℝ) ^ n) (pow_ne_zero n (by norm_num))
  · simp only [div_pow]; field_simp; simp
  · simp only [div_pow]; field_simp; simp

/-- Giới hạn của dãy không âm là số không âm. -/
theorem limit_nonneg {u : ℕ → ℝ} {a : ℝ} (hu : ConvergesTo u a)
    (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n) : 0 ≤ a :=
  calculus.Chapter02.Section04.limit_le_of_positive_terms (fun _ ↦ 0) u 0 a
    tendsto_const_nhds (convergesTo_iff_tendsto.mp hu) h

/-- Định lí 2.5.4: tính liên tục của căn trên miền không âm. -/
theorem sqrt_converges {u : ℕ → ℝ} {a : ℝ} (hu : ConvergesTo u a)
    (_h : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n) :
    ConvergesTo (fun n ↦ Real.sqrt (u n)) (Real.sqrt a) :=
  convergesTo_iff_tendsto.mpr (convergesTo_iff_tendsto.mp hu).sqrt

/-- Bài tập 1(a): giới hạn phân thức bậc hai. -/
theorem quadratic_rational_converges :
    ConvergesTo (fun n ↦ (1 + (n : ℝ)-3 * n ^ 2) / (3-2 * n + n ^ 2)) (-3) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ ((1 / (n : ℝ)) ^ 2 + 1 / (n : ℝ)-3) /
      (3 * (1 / (n : ℝ)) ^ 2-2 * (1 / (n : ℝ)) + 1)) atTop (𝓝 (-3)) := by
    convert! (((h.pow 2).add h).sub_const 3).div
      ((((h.pow 2).const_mul 3).sub (h.const_mul 2)).add_const 1)
      (by norm_num : (3 * 0 ^ 2-2 * 0 + 1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  symm
  apply ratio_normalize _ _ _ _ ((n : ℝ) ^ 2) (pow_ne_zero 2 hn0)
  · field_simp
  · field_simp

/-- Bài tập 1(b): tử bậc hai, mẫu bậc ba. -/
theorem quadratic_over_cubic_converges :
    ConvergesTo (fun n ↦ (1 + (n : ℝ)-3 * n ^ 2) / (3-2 * n + n ^ 3)) 0 := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ ((1 / (n : ℝ)) ^ 3 + (1 / (n : ℝ)) ^ 2-3 * (1 / (n : ℝ))) /
      (3 * (1 / (n : ℝ)) ^ 3-2 * (1 / (n : ℝ)) ^ 2 + 1)) atTop (𝓝 0) := by
    convert! (((h.pow 3).add (h.pow 2)).sub (h.const_mul 3)).div
      ((((h.pow 3).const_mul 3).sub ((h.pow 2).const_mul 2)).add_const 1)
      (by norm_num : (3 * 0 ^ 3-2 * 0 ^ 2 + 1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  symm
  apply ratio_normalize _ _ _ _ ((n : ℝ) ^ 3) (pow_ne_zero 3 hn0)
  · field_simp
  · field_simp


theorem reciprocal_sqrt_tendsto :
    Tendsto (fun n : ℕ ↦ 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, Real.sqrt_zero]
    using (convergesTo_iff_tendsto.mp reciprocal_converges).sqrt

/-- Bài tập 1(c): giới hạn thương hai căn. -/
theorem sqrt_linear_ratio_converges :
    ConvergesTo (fun n ↦ (Real.sqrt (3 * (n : ℝ)) + 1) /
      (Real.sqrt 3 + Real.sqrt (n : ℝ))) (Real.sqrt 3) := by
  have h := reciprocal_sqrt_tendsto
  have H : Tendsto (fun n : ℕ ↦ (Real.sqrt 3 + 1 / Real.sqrt (n : ℝ)) /
      (Real.sqrt 3 * (1 / Real.sqrt (n : ℝ)) + 1)) atTop (𝓝 (Real.sqrt 3)) := by
    convert! (h.const_add (Real.sqrt 3)).div
      ((h.const_mul (Real.sqrt 3)).add_const 1) (by norm_num : (Real.sqrt 3 * 0 + 1 : ℝ) ≠ 0)
      using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hs := Real.sqrt_pos.2 (positive_cast n hn)
  symm
  apply ratio_normalize _ _ _ _ (Real.sqrt (n : ℝ)) (ne_of_gt hs)
  · rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  · field_simp

/-- Miền căn và mẫu của Bài tập 1(d,e), chỉ xét n≥1. -/
theorem first_exercise_radical_domains (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ 2 * (n : ℝ) ^ 2-1 ∧ 0 < (n : ℝ) + 1 ∧ 0 < (2 * (n : ℝ) + 1) / (n : ℝ) := by
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := positive_cast n hn
  refine ⟨by nlinarith [sq_nonneg ((n : ℝ)-1)], by positivity, by positivity⟩

/-- Bài tập 1(d): √(2n²−1)/(n+1)→√2. -/
theorem sqrt_quadratic_ratio_converges :
    ConvergesTo (fun n ↦ Real.sqrt (2 * (n : ℝ) ^ 2-1) / (n + 1)) (Real.sqrt 2) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ Real.sqrt (2-(1 / (n : ℝ)) ^ 2) / (1 + 1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
    convert! ((tendsto_const_nhds.sub (h.pow 2)).sqrt).div (h.const_add 1)
      (by norm_num : (1 + 0 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hp := positive_cast n hn
  have hn0 := ne_of_gt hp
  symm
  apply ratio_normalize _ _ _ _ (n : ℝ) hn0
  · have heq : 2 * (n : ℝ) ^ 2-1 = (n : ℝ) ^ 2 * (2-(1 / (n : ℝ)) ^ 2) := by field_simp
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hp), mul_comm]
  · field_simp

/-- Bài tập 1(e): cơ số→2, số mũ 1/n→0 nên căn bậc n→1. -/
theorem nth_root_linear_ratio_converges :
    ConvergesTo (fun n ↦ Real.rpow ((2 * (n : ℝ) + 1) / n) (1 / (n : ℝ))) 1 := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have hb : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ) + 1) / n) atTop (𝓝 2) := by
    have H : Tendsto (fun n : ℕ ↦ 2 + 1 / (n : ℝ)) atTop (𝓝 2) := by
      simpa using h.const_add 2
    apply H.congr' (eventually_atTop.2 ⟨1, ?_⟩)
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  apply convergesTo_iff_tendsto.mpr
  simpa using hb.rpow h (Or.inl (by norm_num : (2 : ℝ) ≠ 0))

/-- Bài tập 2(a): √n(√(n+1)−√n)→1/2. -/
theorem scaled_sqrt_successor_increment_converges :
    ConvergesTo (fun n ↦ Real.sqrt (n : ℝ) * (Real.sqrt ((n : ℝ) + 1)-Real.sqrt (n : ℝ))) (1 / 2) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ 1 / (Real.sqrt (1 + 1 / (n : ℝ)) + 1)) atTop (𝓝 (1 / 2)) := by
    convert! tendsto_const_nhds.div ((h.const_add 1).sqrt.add_const 1)
      (by norm_num : (Real.sqrt (1 + 0) + 1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  have hp := positive_cast n hn
  have hs := Real.sqrt_pos.2 hp
  have hn0 := ne_of_gt hp
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hp)
  have hrad : 0 ≤ 1 + 1 / (n : ℝ) := by positivity
  have hsq' := Real.sq_sqrt hrad
  have heq : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / n) := by field_simp
  rw [heq, Real.sqrt_mul (le_of_lt hp)]
  symm
  apply (eq_div_iff (by positivity : Real.sqrt (1 + 1 / (n : ℝ)) + 1 ≠ 0)).mpr
  calc
    _ = Real.sqrt (n : ℝ) ^ 2 * (Real.sqrt (1 + 1 / (n : ℝ)) ^ 2-1) := by ring
    _ = 1 := by rw [hsq, hsq']; field_simp; ring

/-- Bài tập 2(b): chênh lệch căn hai số liên tiếp→0. -/
theorem sqrt_successor_increment_converges :
    ConvergesTo (fun n ↦ Real.sqrt ((n : ℝ) + 1)-Real.sqrt (n : ℝ)) 0 := by
  have H := (convergesTo_iff_tendsto.mp scaled_sqrt_successor_increment_converges).mul
    reciprocal_sqrt_tendsto
  apply convergesTo_iff_tendsto.mpr
  have H' : Tendsto (fun n : ℕ ↦
      (Real.sqrt (n : ℝ) * (Real.sqrt ((n : ℝ) + 1)-Real.sqrt (n : ℝ))) * (1 / Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by simpa using H
  apply H'.congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hs := Real.sqrt_pos.2 (positive_cast n hn)
  field_simp


theorem sqrt_increment_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) ^ 2 + a * n + b)-(n : ℝ) =
      (a + b / n) / (Real.sqrt (1 + a / n + b / (n : ℝ) ^ 2) + 1) := by
  have hp := positive_cast n hn
  have hn0 := ne_of_gt hp
  have hrad : 0 ≤ 1 + a / (n : ℝ) + b / (n : ℝ) ^ 2 := by positivity
  have hs : Real.sqrt (1 + a / (n : ℝ) + b / (n : ℝ) ^ 2) ^ 2 =
      1 + a / (n : ℝ) + b / (n : ℝ) ^ 2 := Real.sq_sqrt hrad
  have heq : (n : ℝ) ^ 2 + a * n + b = (n : ℝ) ^ 2 * (1 + a / n + b / (n : ℝ) ^ 2) := by
    field_simp
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hp)]
  have hden : Real.sqrt (1 + a / (n : ℝ) + b / (n : ℝ) ^ 2) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hden).mpr
  have hid : ((n : ℝ) * Real.sqrt (1 + a / n + b / (n : ℝ) ^ 2)-n) *
      (Real.sqrt (1 + a / n + b / (n : ℝ) ^ 2) + 1) =
      (n : ℝ) * (Real.sqrt (1 + a / n + b / (n : ℝ) ^ 2) ^ 2-1) := by ring
  rw [hid, hs]
  field_simp
  ring

/-- Giới hạn chung của chênh lệch căn trong Bài tập 2 và 5. -/
theorem sqrt_increment_converges (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ConvergesTo (fun n ↦ Real.sqrt ((n : ℝ) ^ 2 + a * n + b)-(n : ℝ)) (a / 2) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ (a + b * (1 / (n : ℝ))) /
      (Real.sqrt (1 + a * (1 / (n : ℝ)) + b * (1 / (n : ℝ)) ^ 2) + 1)) atTop (𝓝 (a / 2)) := by
    convert! ((h.const_mul b).const_add a).div
      ((((h.const_mul a).const_add 1).add ((h.pow 2).const_mul b)).sqrt.add_const 1)
      (by norm_num : (Real.sqrt (1 + a * 0 + b * 0 ^ 2) + 1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  rw [sqrt_increment_eq a b ha hb n hn]
  simp only [div_eq_mul_inv, one_mul, inv_pow]

/-- Bài tập 2(c): √(n²+n)−n→1/2. -/
theorem sqrt_quadratic_increment_converges :
    ConvergesTo (fun n ↦ Real.sqrt ((n : ℝ) ^ 2 + n)-(n : ℝ)) (1 / 2) := by
  simpa using sqrt_increment_converges 1 0 (by norm_num) (by norm_num)

/-- Bài tập 2(d): thương các chênh lệch căn, với mẫu khác 0 khi n đủ lớn. -/
theorem ratio_sqrt_increments_converges (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hcd : c ≠ d) :
    ConvergesTo (fun n ↦
      (Real.sqrt ((n : ℝ) ^ 2 + a * n + 1)-Real.sqrt ((n : ℝ) ^ 2 + b * n + 2)) /
      (Real.sqrt ((n : ℝ) ^ 2 + c * n + 3)-Real.sqrt ((n : ℝ) ^ 2 + d * n + 4))) ((a-b) / (c-d)) := by
  have A := convergesTo_iff_tendsto.mp (sqrt_increment_converges a 1 (le_of_lt ha) (by norm_num))
  have B := convergesTo_iff_tendsto.mp (sqrt_increment_converges b 2 (le_of_lt hb) (by norm_num))
  have C := convergesTo_iff_tendsto.mp (sqrt_increment_converges c 3 (le_of_lt hc) (by norm_num))
  have D := convergesTo_iff_tendsto.mp (sqrt_increment_converges d 4 (le_of_lt hd) (by norm_num))
  have hden : c / 2-d / 2 ≠ 0 := by intro h; apply hcd; linarith
  apply convergesTo_iff_tendsto.mpr
  convert! (A.sub B).div (C.sub D) hden using 1
  · funext n
    congr 1 <;> ring
  · field_simp

/-- Bài tập 2(d): mẫu khác 0 từ một ngưỡng. -/
theorem ratio_sqrt_increments_eventually_defined (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hcd : c ≠ d) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n : ℝ) ^ 2 + c * n + 3)-Real.sqrt ((n : ℝ) ^ 2 + d * n + 4) ≠ 0 := by
  have C := convergesTo_iff_tendsto.mp (sqrt_increment_converges c 3 (le_of_lt hc) (by norm_num))
  have D := convergesTo_iff_tendsto.mp (sqrt_increment_converges d 4 (le_of_lt hd) (by norm_num))
  have hden : c / 2-d / 2 ≠ 0 := by intro h; apply hcd; linarith
  have H := (C.sub D).eventually_ne hden
  filter_upwards [H] with n hn
  convert hn using 1
  ring

/-- Mẫu bằng 0 ở chỉ số đầu; giới hạn chỉ dùng phần đuôi đã xác định. -/
theorem ratio_sqrt_first_denominator_zero :
    Real.sqrt ((1 : ℝ) ^ 2 + 2 * 1 + 3)-Real.sqrt ((1 : ℝ) ^ 2 + 1 * 1 + 4) = 0 := by norm_num


theorem affine_rpow_hasDerivAt (a p : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.rpow (1 + a * t) p) (a * p) 0 := by
  convert! (((hasDerivAt_id (0 : ℝ)).const_mul a).const_add 1).rpow_const
    (Or.inl (by norm_num : (1 + a * 0 : ℝ) ≠ 0)) using 1
  all_goals simp


theorem rpow_scaled_difference_tendsto (a b p : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k *
      (Real.rpow (1 + a / (n : ℝ) ^ k) p-Real.rpow (1 + b / (n : ℝ) ^ k) p))
      atTop (𝓝 ((a-b) * p)) := by
  have h : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by omega : k ≠ 0)]
      using (convergesTo_iff_tendsto.mp reciprocal_converges).pow k
  have hw : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ k) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h, eventually_atTop.2 ⟨1, fun n hn ↦ by
      exact one_div_pos.mpr (pow_pos (positive_cast n hn) k)⟩⟩
  have hd := (affine_rpow_hasDerivAt a p).sub (affine_rpow_hasDerivAt b p)
  have H := hd.tendsto_slope_zero_right.comp hw
  convert! H using 1
  · funext n
    simp [Pi.sub_apply, Real.rpow_eq_pow, div_eq_mul_inv]
  · ring


theorem root_degree_increment_converges (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    ConvergesTo (fun n ↦ Real.rpow ((n : ℝ) ^ k + a * (n : ℝ) ^ (k-1)) (1 / (k : ℝ))-(n : ℝ))
      (a / (k : ℝ)) := by
  have H := rpow_scaled_difference_tendsto a 0 (1 / (k : ℝ)) 1 le_rfl
  have H' : Tendsto (fun n : ℕ ↦ (n : ℝ)*
      (Real.rpow (1 + a / (n : ℝ)) (1 / (k : ℝ))-1)) atTop (𝓝 (a / (k : ℝ))) := by
    simpa [div_eq_mul_inv, Real.rpow_eq_pow] using H
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H')
  intro n hn
  have hp := positive_cast n hn
  have hn0 := ne_of_gt hp
  have heq : (n : ℝ) ^ k + a * (n : ℝ) ^ (k-1) = (n : ℝ) ^ k * (1 + a / n) := by
    have he : (n : ℝ) ^ (k-1) * (n : ℝ) = (n : ℝ) ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    field_simp
    rw [← he]
    ring
  simp only [Real.rpow_eq_pow]
  rw [heq, Real.mul_rpow (pow_nonneg (le_of_lt hp) k) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (le_of_lt hp) (by omega : k ≠ 0)]
  ring

/-- Bài tập 2(e): căn bậc ba của n³+3n² trừ n tiến về 1. -/
theorem cube_root_increment_converges :
    ConvergesTo (fun n ↦ Real.rpow ((n : ℝ) ^ 3 + 3 * n ^ 2) (1 / 3)-(n : ℝ)) 1 := by
  simpa using root_degree_increment_converges 3 (by norm_num) 3 (by norm_num)

/-- Bài tập 2(f): chênh lệch căn bậc ba và căn bậc hai tiến về 1/2. -/
theorem cube_root_sub_sqrt_converges :
    ConvergesTo (fun n ↦ Real.rpow ((n : ℝ) ^ 3 + 3 * n ^ 2) (1 / 3)-Real.sqrt ((n : ℝ) ^ 2 + n)) (1 / 2) := by
  have H := (convergesTo_iff_tendsto.mp cube_root_increment_converges).sub
    (convergesTo_iff_tendsto.mp sqrt_quadratic_increment_converges)
  apply convergesTo_iff_tendsto.mpr
  convert! H using 1
  · funext n; ring
  · norm_num

/-- Bài tập 2(g): chênh lệch hai căn bậc bốn có giới hạn 1/4. -/
theorem fourth_root_difference_converges :
    ConvergesTo (fun n ↦ Real.rpow ((n : ℝ) ^ 4 + 2 * n ^ 3) (1 / 4)-
      Real.rpow ((n : ℝ) ^ 4 + n ^ 3) (1 / 4)) (1 / 4) := by
  have A := convergesTo_iff_tendsto.mp (root_degree_increment_converges 4 (by norm_num) 2 (by norm_num))
  have B := convergesTo_iff_tendsto.mp (root_degree_increment_converges 4 (by norm_num) 1 (by norm_num))
  apply convergesTo_iff_tendsto.mpr
  convert! A.sub B using 1
  · funext n; simp only [Nat.reduceSub, one_mul, Nat.cast_ofNat]; ring
  · norm_num

/-- Chênh lệch căn bậc k của hai đa thức chỉ khác hằng số. -/
noncomputable def rootDifference (k : ℕ) (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow ((n : ℝ) ^ k + a) (1 / (k : ℝ))-Real.rpow ((n : ℝ) ^ k + b) (1 / (k : ℝ))

/-- Chênh lệch căn nhân với n^(k−1). -/
noncomputable def scaledRootDifference (k : ℕ) (a b : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (k-1) * rootDifference k a b n


theorem root_constant_rescale (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ k + a) ^ (1 / (k : ℝ)) =
      (n : ℝ) * (1 + a / (n : ℝ) ^ k) ^ (1 / (k : ℝ)) := by
  have hp := positive_cast n hn
  have heq : (n : ℝ) ^ k + a = (n : ℝ) ^ k * (1 + a / (n : ℝ) ^ k) := by
    field_simp
  rw [heq, Real.mul_rpow (pow_nonneg (le_of_lt hp) k) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (le_of_lt hp) (by omega : k ≠ 0)]


theorem scaled_root_difference_converges (k : ℕ) (hk : 1 ≤ k) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ConvergesTo (scaledRootDifference k a b) ((a-b) / (k : ℝ)) := by
  have H := rpow_scaled_difference_tendsto a b (1 / (k : ℝ)) k hk
  have H' : ConvergesTo (fun n : ℕ ↦ (n : ℝ) ^ k *
      (Real.rpow (1 + a / (n : ℝ) ^ k) (1 / (k : ℝ))-
       Real.rpow (1 + b / (n : ℝ) ^ k) (1 / (k : ℝ)))) ((a-b) / (k : ℝ)) := by
    apply convergesTo_iff_tendsto.mpr
    simpa only [div_eq_mul_inv, one_mul] using H
  refine (convergesTo_congr ?_).mp H'
  intro n hn
  dsimp [scaledRootDifference, rootDifference]
  rw [root_constant_rescale k hk a ha n hn, root_constant_rescale k hk b hb n hn]
  have hp : (n : ℝ) ^ (k-1) * (n : ℝ) = (n : ℝ) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  simp only [mul_sub, ← mul_assoc, hp]

/-- Bài tập 3: mẫu dương tại n≥1. -/
theorem root_difference_pos (k : ℕ) (hk : 1 ≤ k) (a b : ℝ)
    (hb : 0 ≤ b) (hab : b < a) (n : ℕ) : 0 < rootDifference k a b n := by
  dsimp [rootDifference]
  apply sub_pos.mpr
  exact Real.rpow_lt_rpow (by positivity) (by linarith) (by
    have hp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity)


theorem root_ratio_rescale_of_le (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k ≤ m)
    (n : ℕ) (hn : 1 ≤ n) :
    rootDifference k 3 1 n / rootDifference m 9 2 n =
      (scaledRootDifference k 3 1 n / scaledRootDifference m 9 2 n) * (n : ℝ) ^ (m-k) := by
  have hn0 := ne_of_gt (positive_cast n hn)
  have he : k-1 + (m-k) = m-1 := by omega
  dsimp [scaledRootDifference]
  symm
  rw [mul_div_mul_comm]
  calc
    _ = ((n : ℝ) ^ (k-1) * (n : ℝ) ^ (m-k) / (n : ℝ) ^ (m-1))*
        (rootDifference k 3 1 n / rootDifference m 9 2 n) := by ring
    _ = rootDifference k 3 1 n / rootDifference m 9 2 n := by
      rw [← pow_add, he, div_self (pow_ne_zero _ hn0), one_mul]


theorem root_ratio_rescale_of_ge (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : m ≤ k)
    (n : ℕ) (hn : 1 ≤ n) :
    rootDifference k 3 1 n / rootDifference m 9 2 n =
      (scaledRootDifference k 3 1 n / scaledRootDifference m 9 2 n) * (1 / (n : ℝ) ^ (k-m)) := by
  have hn0 := ne_of_gt (positive_cast n hn)
  have he : m-1 + (k-m) = k-1 := by omega
  dsimp [scaledRootDifference]
  symm
  rw [mul_div_mul_comm]
  calc
    _ = ((n : ℝ) ^ (k-1) / ((n : ℝ) ^ (m-1) * (n : ℝ) ^ (k-m)))*
        (rootDifference k 3 1 n / rootDifference m 9 2 n) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = rootDifference k 3 1 n / rootDifference m 9 2 n := by
      rw [← pow_add, he, div_self (pow_ne_zero _ hn0), one_mul]


theorem scaled_root_ratio_converges (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ConvergesTo (fun n ↦ scaledRootDifference k 3 1 n / scaledRootDifference m 9 2 n)
      ((2 / (k : ℝ)) / (7 / (m : ℝ))) := by
  have A := convergesTo_iff_tendsto.mp (scaled_root_difference_converges k hk 3 1 (by norm_num) (by norm_num))
  have B := convergesTo_iff_tendsto.mp (scaled_root_difference_converges m hm 9 2 (by norm_num) (by norm_num))
  apply convergesTo_iff_tendsto.mpr
  have hden : (9-2) / (m : ℝ) ≠ 0 := by
    have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  convert! A.div B hden using 1
  all_goals norm_num

/-- Bài tập 3, k=m: giới hạn 2/7. -/
theorem root_ratio_equal_degree_converges (k : ℕ) (hk : 1 < k) :
    ConvergesTo (fun n ↦ rootDifference k 3 1 n / rootDifference k 9 2 n) (2 / 7) := by
  have hk1 : 1 ≤ k := by omega
  have H := scaled_root_ratio_converges k k hk1 hk1
  have H' : ConvergesTo (fun n ↦ scaledRootDifference k 3 1 n / scaledRootDifference k 9 2 n)
      (2 / 7) := by
    convert H using 1
    have hp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    field_simp
  refine (convergesTo_congr ?_).mp H'
  intro n hn
  simpa using (root_ratio_rescale_of_le k k hk1 hk1 le_rfl n hn).symm

/-- Bài tập 3, k>m: tỉ số tiến về 0. -/
theorem root_ratio_larger_degree_converges (k m : ℕ) (hk : 1 < k) (hm : 1 < m)
    (hkm : m < k) : ConvergesTo (fun n ↦ rootDifference k 3 1 n / rootDifference m 9 2 n) 0 := by
  have A := convergesTo_iff_tendsto.mp (scaled_root_ratio_converges k m (by omega) (by omega))
  have B : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ (k-m)) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by omega : k-m ≠ 0)]
      using (convergesTo_iff_tendsto.mp reciprocal_converges).pow (k-m)
  have H' : ConvergesTo (fun n ↦
      (scaledRootDifference k 3 1 n / scaledRootDifference m 9 2 n) * (1 / (n : ℝ) ^ (k-m))) 0 := by
    apply convergesTo_iff_tendsto.mpr
    simpa using A.mul B
  refine (convergesTo_congr ?_).mp H'
  intro n hn
  exact (root_ratio_rescale_of_ge k m (by omega) (by omega) hkm.le n hn).symm

/-- Bài tập 3, k<m: tỉ số tiến về +∞. -/
theorem root_ratio_smaller_degree_tendsto_atTop (k m : ℕ) (hk : 1 < k) (hm : 1 < m)
    (hkm : k < m) : Tendsto (fun n ↦ rootDifference k 3 1 n / rootDifference m 9 2 n) atTop atTop := by
  have A := convergesTo_iff_tendsto.mp (scaled_root_ratio_converges k m (by omega) (by omega))
  have B : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (m-k)) atTop atTop :=
    (Filter.tendsto_pow_atTop (by omega : m-k ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hp : 0 < (2 / (k : ℝ)) / (7 / (m : ℝ)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  apply (A.pos_mul_atTop hp B).congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  exact (root_ratio_rescale_of_le k m (by omega) (by omega) hkm.le n hn).symm

/-- Bài tập 4(a): tổng hình học từ 0 đến n. -/
theorem geometric_partial_sum_converges (a : ℝ) (ha : |a| < 1) :
    ConvergesTo (fun n ↦ ∑ k ∈ Finset.range (n + 1), a ^ k) (1 / (1-a)) := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [one_div] using (Filter.tendsto_add_atTop_iff_nat 1).mpr
    (hasSum_geometric_of_abs_lt_one ha).tendsto_sum_nat

/-- Tổng hình học 1+b+⋯+bⁿ khác 0 khi |b|<1. -/
theorem geometric_partial_sum_ne_zero (b : ℝ) (hb : |b| < 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), b ^ k) ≠ 0 := by
  have hb1 : b ≠ 1 := by intro h; subst b; norm_num at hb
  rw [geom_sum_eq hb1]
  apply div_ne_zero
  · have hp := pow_lt_one₀ (abs_nonneg b) hb (by omega : n + 1 ≠ 0)
    have H : b ^ (n + 1) < 1 := lt_of_le_of_lt (le_abs_self _) (by simpa only [abs_pow] using hp)
    linarith
  · exact sub_ne_zero.mpr hb1

/-- Bài tập 4(a): thương các tổng hình học. -/
theorem ratio_geometric_partial_sums_converges (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    ConvergesTo (fun n ↦ (∑ k ∈ Finset.range (n + 1), a ^ k) /
      (∑ k ∈ Finset.range (n + 1), b ^ k)) ((1-b) / (1-a)) := by
  have ha0 : 1-a ≠ 0 := by have := le_abs_self a; linarith
  have hb0 : 1-b ≠ 0 := by have := le_abs_self b; linarith
  apply convergesTo_iff_tendsto.mpr
  have H := (convergesTo_iff_tendsto.mp (geometric_partial_sum_converges a ha)).div
    (convergesTo_iff_tendsto.mp (geometric_partial_sum_converges b hb)) (by positivity : 1 / (1-b) ≠ 0)
  convert! H using 1
  field_simp

/-- Công thức rút gọn tổng 1/[k(k+1)], k=1,…,n. -/
theorem reciprocal_product_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * (k + 2))) = 1-1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- Bài tập 4(b): tổng rút gọn tiến về 1. -/
theorem reciprocal_product_sum_converges :
    ConvergesTo (fun n ↦ ∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * (k + 2))) 1 := by
  have H : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Filter.tendsto_add_atTop_iff_nat 1).mpr
      (convergesTo_iff_tendsto.mp reciprocal_converges)
  apply convergesTo_iff_tendsto.mpr
  simpa only [reciprocal_product_sum_eq, sub_zero] using H.const_sub 1

/-- Tổng k·k!, với k=1,…,n. -/
theorem mul_factorial_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * ((k + 1).factorial : ℝ)) =
      ((n + 1).factorial : ℝ)-1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hf : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
      convert! congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.factorial_succ (n + 1)) using 1
      push_cast
      ring
    simp only [Nat.add_assoc]
    rw [hf]
    ring

/-- Bài tập 4(c): giới hạn tổng giai thừa chia cho (n+1)!. -/
theorem mul_factorial_sum_converges :
    ConvergesTo (fun n ↦ (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * ((k + 1).factorial : ℝ)) /
      ((n + 1).factorial : ℝ)) 1 := by
  have H : Tendsto (fun n : ℕ ↦ 1 / ((n + 1).factorial : ℝ)) atTop (𝓝 0) := by
    simpa only [one_pow] using (Filter.tendsto_add_atTop_iff_nat 1).mpr
      (FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ))
  apply convergesTo_iff_tendsto.mpr
  have H' : Tendsto (fun n : ℕ ↦ 1-1 / ((n + 1).factorial : ℝ)) atTop (𝓝 1) := by
    simpa using H.const_sub 1
  apply H'.congr'
  apply Filter.Eventually.of_forall
  intro n
  change 1-1 / ((n + 1).factorial : ℝ) =
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * ((k + 1).factorial : ℝ)) / ((n + 1).factorial : ℝ)
  rw [mul_factorial_sum_eq]
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  field_simp

/-- Tổng hữu hạn có trọng số lẻ và mẫu 2ᵏ. -/
theorem odd_geometric_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 * ((k : ℝ) + 1)-1) / (2 : ℝ) ^ (k + 1)) =
      3-(2 * (n : ℝ) + 3) / (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

/-- Bài tập 4(d): giới hạn tổng bằng 3. -/
theorem odd_geometric_sum_converges :
    ConvergesTo (fun n ↦ ∑ k ∈ Finset.range n, (2 * ((k : ℝ) + 1)-1) / (2 : ℝ) ^ (k + 1)) 3 := by
  have hn := tendsto_self_mul_const_pow_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
  have H := ((hn.const_mul 2).add (hp.const_mul 3)).const_sub 3
  apply convergesTo_iff_tendsto.mpr
  convert! H using 1
  · funext n
    rw [odd_geometric_sum_eq]
    simp only [div_pow, one_pow]
    ring
  · norm_num

/-- Bài tập 4(e): tổng bình phương chia n³ tiến về 1/3. -/
theorem sum_squares_div_cube_converges :
    ConvergesTo (fun n ↦ (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2) / (n : ℝ) ^ 3) (1 / 3) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ (1 + 1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) / 6) atTop (𝓝 (1 / 3)) := by
    convert! ((h.const_add 1).mul (h.const_add 2)).div_const 6 using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  rw [calculus.Chapter02.Section01Exercises.sum_squares]
  have hn0 := ne_of_gt (positive_cast n hn)
  field_simp

/-- Tổng các giá trị ak+b với k=0,…,n. -/
theorem affine_sum_eq (a b : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (a * (k : ℝ) + b)) = ((n : ℝ) + 1) * (a * n / 2 + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 4(f): tử 3k+1 và mẫu 2k+3, tổng từ 0 đến n. -/
theorem ratio_affine_sums_converges :
    ConvergesTo (fun n ↦ (∑ k ∈ Finset.range (n + 1), (3 * (k : ℝ) + 1)) /
      (∑ k ∈ Finset.range (n + 1), (2 * (k : ℝ) + 3))) (3 / 2) := by
  have h := convergesTo_iff_tendsto.mp reciprocal_converges
  have H : Tendsto (fun n : ℕ ↦ (3 / 2 + 1 / (n : ℝ)) / (1 + 3 * (1 / (n : ℝ)))) atTop (𝓝 (3 / 2)) := by
    convert! (h.const_add (3 / 2)).div ((h.const_mul 3).const_add 1)
      (by norm_num : (1 + 3 * 0 : ℝ) ≠ 0) using 1
    all_goals norm_num
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H)
  intro n hn
  rw [affine_sum_eq, affine_sum_eq]
  have hn0 := ne_of_gt (positive_cast n hn)
  have hc : ((n : ℝ) + 1) * (n : ℝ) ≠ 0 := by positivity
  symm
  apply ratio_normalize _ _ _ _ (((n : ℝ) + 1) * (n : ℝ)) hc
  · field_simp
  · field_simp

/-- Bài tập 5: độ lệch căn từ n tiến về 0, sin đổi dấu theo tính chẵn lẻ. -/
theorem sine_sqrt_quadratic_converges :
    ConvergesTo (fun n ↦ Real.sin (Real.pi * Real.sqrt (1 + (n : ℝ) ^ 2))) 0 := by
  have D := convergesTo_iff_tendsto.mp (sqrt_increment_converges 0 1 (by norm_num) (by norm_num))
  have D' : Tendsto (fun n : ℕ ↦ Real.pi * (Real.sqrt (1 + (n : ℝ) ^ 2)-(n : ℝ)))
      atTop (𝓝 0) := by simpa [add_comm] using D.const_mul Real.pi
  have H := Real.continuous_sin.continuousAt.tendsto.comp D'
  have H' : Tendsto (fun n : ℕ ↦ Real.sin (Real.pi * (Real.sqrt (1 + (n : ℝ) ^ 2)-(n : ℝ))))
      atTop (𝓝 0) := by simpa [Function.comp_def] using H
  have hb : calculus.Chapter02.Section04.SequenceBounded (fun n ↦ (-1 : ℝ) ^ n) := by
    apply (calculus.Chapter02.Section04.sequenceBounded_iff_abs _).mpr
    exact ⟨2, by norm_num, fun n _ ↦ by simp [abs_pow]⟩
  have Hm := calculus.Chapter02.Section04.zero_mul_sequenceBounded _ _ H' hb
  apply convergesTo_iff_tendsto.mpr
  convert! Hm using 1
  funext n
  have heq : Real.pi * Real.sqrt (1 + (n : ℝ) ^ 2) =
      Real.pi * (Real.sqrt (1 + (n : ℝ) ^ 2)-(n : ℝ)) + (n : ℝ) * Real.pi := by ring
  rw [heq, Real.sin_add_nat_mul_pi]
  ring

/-- Bài tập 6: giới hạn tỉ số của hai số hạng liên tiếp. -/
theorem ratio_test_zero_corrected {u : ℕ → ℝ} {l : ℝ}
    (hu : ∀ n : ℕ, 1 ≤ n → u n ≠ 0) (hl : l < 1)
    (hr : ConvergesTo (fun n ↦ |u (n + 1) / u n|) l) : ConvergesTo u 0 := by
  apply convergesTo_iff_tendsto.mpr
  apply Summable.tendsto_atTop_zero
  apply summable_of_ratio_test_tendsto_lt_one hl (eventually_atTop.2 ⟨1, hu⟩)
  simpa only [Real.norm_eq_abs, abs_div] using convergesTo_iff_tendsto.mp hr

/-- Bài tập 7: giới hạn với mọi a∈ℝ. -/
theorem pow_div_factorial_converges (a : ℝ) :
    ConvergesTo (fun n ↦ a ^ n / (n.factorial : ℝ)) 0 :=
  convergesTo_iff_tendsto.mpr (FloorSemiring.tendsto_pow_div_factorial_atTop a)

/-- Bài tập 8: căn bậc n của 2023ⁿ+2024ⁿ+2025ⁿ tiến về 2025. -/
theorem nth_root_sum_powers_converges :
    ConvergesTo (fun n ↦ Real.rpow ((2023 : ℝ) ^ n + 2024 ^ n + 2025 ^ n) (1 / (n : ℝ))) 2025 := by
  have A := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2023 / 2025 : ℝ)| < 1)
  have B := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2024 / 2025 : ℝ)| < 1)
  have H := ((A.add B).add_const 1).rpow (convergesTo_iff_tendsto.mp reciprocal_converges)
    (Or.inl (by norm_num : (0 + 0 + 1 : ℝ) ≠ 0))
  have H' : Tendsto (fun n : ℕ ↦ 2025 * Real.rpow ((2023 / 2025 : ℝ) ^ n + (2024 / 2025) ^ n + 1)
      (1 / (n : ℝ))) atTop (𝓝 2025) := by simpa using H.const_mul 2025
  refine (convergesTo_congr ?_).mp (convergesTo_iff_tendsto.mpr H')
  intro n hn
  have heq : (2023 : ℝ) ^ n + 2024 ^ n + 2025 ^ n =
      (2025 : ℝ) ^ n * ((2023 / 2025 : ℝ) ^ n + (2024 / 2025) ^ n + 1) := by
    simp only [div_pow]
    field_simp
  simp only [Real.rpow_eq_pow]
  rw [heq, Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2025) (by omega : n ≠ 0)]

/-- Hai liên hợp của 2+√3 có tổng 4, tích 1. -/
theorem sqrt_three_conjugates :
    (2 + Real.sqrt 3) + (2-Real.sqrt 3) = 4 ∧
      (2 + Real.sqrt 3) * (2-Real.sqrt 3) = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  constructor
  · ring
  · nlinarith

/-- Tổng hai lũy thừa liên hợp là số nguyên. -/
theorem conjugate_power_sum_integer (n : ℕ) :
    ∃ z : ℤ, (2 + Real.sqrt 3) ^ n + (2-Real.sqrt 3) ^ n = (z : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨2, by norm_num⟩
  | one => exact ⟨4, by simp; ring⟩
  | more n ih ih' =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := ih'
    refine ⟨4 * w-z, ?_⟩
    calc
      _ = ((2 + Real.sqrt 3) + (2-Real.sqrt 3))*
          ((2 + Real.sqrt 3) ^ (n + 1) + (2-Real.sqrt 3) ^ (n + 1)) -
          ((2 + Real.sqrt 3) * (2-Real.sqrt 3))*
          ((2 + Real.sqrt 3) ^ n + (2-Real.sqrt 3) ^ n) := by
        simp only [pow_succ]; ring
      _ = ((4 * w-z : ℤ):ℝ) := by
        rw [sqrt_three_conjugates.1, sqrt_three_conjugates.2, hz, hw]
        push_cast
        ring

/-- Liên hợp 2−√3 thuộc (0,1); lũy thừa tại chỉ số dương khác 0. -/
theorem conjugate_mem_unit_interval : 0 < 2-Real.sqrt 3 ∧ 2-Real.sqrt 3 < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg 3
  constructor <;> nlinarith

/-- Công thức chính xác cho phần thập phân, n≥1. -/
theorem conjugate_power_fract_eq (n : ℕ) (hn : 1 ≤ n) :
    Int.fract ((2 + Real.sqrt 3) ^ n) = 1-(2-Real.sqrt 3) ^ n := by
  obtain ⟨z, hz⟩ := conjugate_power_sum_integer n
  have hp := pow_pos conjugate_mem_unit_interval.1 n
  have hl := pow_lt_one₀ (le_of_lt conjugate_mem_unit_interval.1)
    conjugate_mem_unit_interval.2 (by omega : n ≠ 0)
  have hf : Int.floor ((2 + Real.sqrt 3) ^ n) = z-1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  rw [Int.fract, hf]
  push_cast
  linarith

/-- Bài tập 9: phần thập phân tiến về 1, dù từng số hạng nhỏ hơn 1. -/
theorem conjugate_power_fract_converges :
    ConvergesTo (fun n ↦ (2 + Real.sqrt 3) ^ n-(Int.floor ((2 + Real.sqrt 3) ^ n):ℝ)) 1 := by
  have H := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by rw [abs_of_pos conjugate_mem_unit_interval.1]; exact conjugate_mem_unit_interval.2)
  have H' : ConvergesTo (fun n : ℕ ↦ 1-(2-Real.sqrt 3) ^ n) 1 := by
    apply convergesTo_iff_tendsto.mpr
    simpa using H.const_sub 1
  refine (convergesTo_congr ?_).mp H'
  intro n hn
  exact (conjugate_power_fract_eq n hn).symm

/-- Bài tập 10(a): hai dãy phân kì có tổng bằng 0. -/
theorem divergent_pair_sum_converges :
    ∃ u v : ℕ → ℝ, IsDivergent u ∧ IsDivergent v ∧
      ConvergesTo (fun n ↦ u n + v n) 0 := by
  refine ⟨fun n ↦ (-1 : ℝ) ^ n, fun n ↦ -((-1 : ℝ) ^ n), alternating_isDivergent, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    apply alternating_isDivergent
    refine ⟨-a, convergesTo_iff_tendsto.mpr ?_⟩
    simpa using (convergesTo_iff_tendsto.mp ha).neg
  · simpa using constant_converges 0

/-- Bài tập 10(b): cùng dãy luân phiên dấu hai lần, tích bằng 1. -/
theorem divergent_pair_product_converges :
    ∃ u v : ℕ → ℝ, IsDivergent u ∧ IsDivergent v ∧
      ConvergesTo (fun n ↦ u n * v n) 1 := by
  refine ⟨fun n ↦ (-1 : ℝ) ^ n, fun n ↦ (-1 : ℝ) ^ n,
    alternating_isDivergent, alternating_isDivergent, ?_⟩
  convert constant_converges 1 using 1
  funext n
  rw [← mul_pow]
  norm_num

end calculus.Chapter02.Section05
