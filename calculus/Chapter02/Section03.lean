import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# 2.3. Giới hạn của dãy số

Nguồn: `source/Ch2_dayso.tex`, dòng 851–1164.
-/

open Filter Topology

namespace calculus.Chapter02.Section03

/-- Định nghĩa 2.3.7: hội tụ theo ε–N, với N≥1. -/
def ConvergesTo (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → |u n - a| < ε

/-- Định nghĩa 2.3.1: giới hạn 0. -/
def ConvergesToZero (u : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → |u n| < ε

/-- Định nghĩa 2.3.7: tồn tại một giới hạn thực hữu hạn. -/
def IsConvergent (u : ℕ → ℝ) : Prop := ∃ a : ℝ, ConvergesTo u a

/-- Định nghĩa 2.3.7: không có giới hạn thực hữu hạn. -/
def IsDivergent (u : ℕ → ℝ) : Prop := ¬ IsConvergent u

/-- Hội tụ ε–N tương đương `Tendsto`. -/
theorem convergesTo_iff_tendsto {u : ℕ → ℝ} {a : ℝ} :
    ConvergesTo u a ↔ Tendsto u atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, _, hN⟩ := h ε hε
    exact ⟨N, fun n hn ↦ by simpa only [Real.dist_eq] using hN n hn⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max 1 N, le_max_left _ _, fun n hn ↦ ?_⟩
    simpa only [Real.dist_eq] using hN n (le_trans (le_max_right _ _) hn)

/-- Dòng 858: định nghĩa giới hạn 0 tương đương định nghĩa ε–N tổng quát. -/
theorem convergesToZero_iff {u : ℕ → ℝ} : ConvergesToZero u ↔ ConvergesTo u 0 := by
  simp only [ConvergesToZero, ConvergesTo, sub_zero]

/-- Bài tập 2.3.1: dãy hằng có giới hạn bằng chính hằng số. -/
theorem constant_converges (C : ℝ) : ConvergesTo (fun _ ↦ C) C := by
  intro ε hε
  exact ⟨1, le_rfl, fun _ _ ↦ by simpa using hε⟩


theorem convergesTo_congr {u v : ℕ → ℝ} {a : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → u n = v n) : ConvergesTo u a ↔ ConvergesTo v a := by
  constructor
  · intro hu ε hε
    obtain ⟨N, hN, hn⟩ := hu ε hε
    exact ⟨N, hN, fun n hnn ↦ by rw [← h n (hN.trans hnn)]; exact hn n hnn⟩
  · intro hv ε hε
    obtain ⟨N, hN, hn⟩ := hv ε hε
    exact ⟨N, hN, fun n hnn ↦ by rw [h n (hN.trans hnn)]; exact hn n hnn⟩


theorem convergesTo_eventually_congr {u v : ℕ → ℝ} {a : ℝ} (k : ℕ)
    (h : ∀ n : ℕ, k ≤ n → u n = v n) : ConvergesTo u a ↔ ConvergesTo v a := by
  constructor
  · intro hu ε hε
    obtain ⟨N, hN, hn⟩ := hu ε hε
    refine ⟨max k N, hN.trans (le_max_right _ _), fun n hnn ↦ ?_⟩
    rw [← h n ((le_max_left _ _).trans hnn)]
    exact hn n ((le_max_right _ _).trans hnn)
  · intro hv ε hε
    obtain ⟨N, hN, hn⟩ := hv ε hε
    refine ⟨max k N, hN.trans (le_max_right _ _), fun n hnn ↦ ?_⟩
    rw [h n ((le_max_left _ _).trans hnn)]
    exact hn n ((le_max_right _ _).trans hnn)

/-- Ví dụ 2.3.2: 1/n tiến về 0. -/
theorem reciprocal_converges : ConvergesTo (fun n ↦ 1 / (n : ℝ)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨max 1 N, le_max_left _ _, fun n hn ↦ ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N) hn))
  have hlarge : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN
    (by exact_mod_cast le_trans (le_max_right 1 N) hn)
  rw [sub_zero, abs_of_pos (one_div_pos.mpr hnpos)]
  apply (div_lt_iff₀ hnpos).mpr
  simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge

/-- Bài tập 2.3.10: nếu |uₙ−a|≤Cbₙ, C>0 và bₙ≥0, bₙ→0, thì uₙ→a. -/
theorem convergesTo_of_error_le {u b : ℕ → ℝ} {a C : ℝ}
    (hbnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ b n) (hb : ConvergesTo b 0) (hC : 0 < C)
    (herr : ∀ n : ℕ, 1 ≤ n → |u n - a| ≤ C * b n) : ConvergesTo u a := by
  intro ε hε
  obtain ⟨N, hN, hn⟩ := hb (ε / C) (div_pos hε hC)
  refine ⟨N, hN, fun n hnn ↦ ?_⟩
  have hsmall := hn n hnn
  rw [sub_zero, abs_of_nonneg (hbnonneg n (hN.trans hnn))] at hsmall
  apply lt_of_le_of_lt (herr n (hN.trans hnn))
  simpa only [mul_comm] using (lt_div_iff₀ hC).mp hsmall


theorem convergesTo_of_error_le_const_div {u : ℕ → ℝ} {a C : ℝ} (hC : 0 < C)
    (herr : ∀ n : ℕ, 1 ≤ n → |u n - a| ≤ C / (n : ℝ)) : ConvergesTo u a := by
  apply convergesTo_of_error_le (b := fun n ↦ 1 / (n : ℝ))
  · intro n hn
    positivity
  · exact reciprocal_converges
  · exact hC
  · intro n hn
    simpa only [mul_one_div] using herr n hn

/-- Định lí 2.3.5: uₙ→0 khi và chỉ khi |uₙ|→0. -/
theorem convergesTo_zero_iff_abs {u : ℕ → ℝ} :
    ConvergesTo u 0 ↔ ConvergesTo (fun n ↦ |u n|) 0 := by
  simp only [ConvergesTo, sub_zero, abs_abs]

/-- Nhận xét 2.3.9(i): trừ giới hạn để đưa về giới hạn 0. -/
theorem convergesTo_iff_sub_zero {u : ℕ → ℝ} {a : ℝ} :
    ConvergesTo u a ↔ ConvergesTo (fun n ↦ u n - a) 0 := by
  simp only [ConvergesTo, sub_zero]

/-- Nhận xét 2.3.9(ii): lân cận ε là khoảng mở quanh a. -/
theorem error_lt_iff_mem_interval (x a ε : ℝ) :
    |x - a| < ε ↔ x ∈ Set.Ioo (a - ε) (a + ε) := by
  rw [abs_lt, Set.mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Nhận xét 2.3.9(ii): tiêu chuẩn hội tụ bằng khoảng mở. -/
theorem convergesTo_iff_eventually_interval {u : ℕ → ℝ} {a : ℝ} :
    ConvergesTo u a ↔ ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → u n ∈ Set.Ioo (a - ε) (a + ε) := by
  simp only [ConvergesTo, error_lt_iff_mem_interval]

/-- Nhận xét 2.3.9(iv): phủ định đầy đủ; ε phụ thuộc a, n phụ thuộc a,ε,N. -/
theorem isDivergent_iff {u : ℕ → ℝ} : IsDivergent u ↔
    ∀ a : ℝ, ∃ ε > 0, ∀ N : ℕ, 1 ≤ N → ∃ n : ℕ, N ≤ n ∧ ε ≤ |u n - a| := by
  classical
  simp only [IsDivergent, IsConvergent, ConvergesTo, not_exists, not_forall, not_lt,
    not_and, exists_prop]

/-- Định lí 2.3.8: tính duy nhất của giới hạn hữu hạn. -/
theorem limit_unique {u : ℕ → ℝ} {a b : ℝ}
    (ha : ConvergesTo u a) (hb : ConvergesTo u b) : a = b :=
  tendsto_nhds_unique (convergesTo_iff_tendsto.mp ha) (convergesTo_iff_tendsto.mp hb)

/-- Định lí 2.3.12: trị tuyệt đối bảo toàn giới hạn. -/
theorem abs_converges {u : ℕ → ℝ} {a : ℝ} (h : ConvergesTo u a) :
    ConvergesTo (fun n ↦ |u n|) |a| := by
  intro ε hε
  obtain ⟨N, hN, hn⟩ := h ε hε
  exact ⟨N, hN, fun n hnn ↦ lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) (hn n hnn)⟩

/-- Ví dụ 2.3.3: 1/n^α tiến về 0 với α>0. -/
theorem reciprocal_rpow_converges (α : ℝ) (hα : 0 < α) :
    ConvergesTo (fun n ↦ 1 / Real.rpow (n : ℝ) α) 0 := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [one_div, Function.comp_def, Real.rpow_eq_pow] using!
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop


theorem reciprocal_geometric_converges (b : ℝ) (hb : 1 < b) :
    ConvergesTo (fun n ↦ 1 / b ^ n) 0 := by
  apply convergesTo_iff_tendsto.mpr
  exact (tendsto_pow_atTop_atTop_of_one_lt hb).inv_tendsto_atTop |>.congr
    (fun n ↦ (one_div (b ^ n)).symm)

/-- Ví dụ 2.3.4: 1/2ⁿ tiến về 0. -/
theorem reciprocal_two_pow_converges : ConvergesTo (fun n ↦ 1 / (2 : ℝ) ^ n) 0 :=
  reciprocal_geometric_converges 2 (by norm_num)

/-- Ví dụ 2.3.6 và Bài tập 2.3.2(b): (−1)ⁿ/n→0. -/
theorem alternating_reciprocal_converges :
    ConvergesTo (fun n ↦ (-1 : ℝ) ^ n / (n : ℝ)) 0 := by
  apply convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  simp only [sub_zero, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact le_rfl

/-- Ví dụ 2.3.11: dãy luân phiên ±1 không hội tụ. -/
theorem alternating_isDivergent : IsDivergent (fun n ↦ (-1 : ℝ) ^ n) := by
  rw [isDivergent_iff]
  intro a
  refine ⟨1, by norm_num, fun N hN ↦ ?_⟩
  by_cases ha : a < 0
  · refine ⟨2 * N, by omega, ?_⟩
    simp only [pow_mul, neg_one_sq, one_pow]
    rw [abs_of_pos (by linarith : 0 < 1 - a)]
    linarith
  · refine ⟨2 * N + 1, by omega, ?_⟩
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
    rw [abs_of_nonpos (by linarith : -1 - a ≤ 0)]
    linarith

/-- Phản ví dụ cho bước dòng 1032: tại a=0, sai số bằng 1, không lớn hơn 1. -/
theorem alternating_strict_error_counterexample :
    |(-1 : ℝ) - 0| = 1 ∧ ¬ (1 : ℝ) + 0 > 1 := by norm_num

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S03-example-006.proof-strict-error: tại chỉ số lẻ, sai số bằng `1 + a ≥ 1` với `a ≥ 0`. -/
theorem alternating_corrected_odd_error (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    |(-1 : ℝ) ^ (2 * N + 1) - a| = 1 + a ∧
      1 ≤ |(-1 : ℝ) ^ (2 * N + 1) - a| := by
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  rw [abs_of_nonpos (by linarith : -1 - a ≤ 0)]
  constructor <;> linarith

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S03-example-006.proof-strict-error, dòng 1032: bất đẳng thức ngặt cho sai số tại chỉ số lẻ trong lời giải gốc. -/
theorem source_alternating_odd_strict_error (a : ℝ) (ha : 0 ≤ a)
    (N : ℕ) (hN : 1 ≤ N) :
    |(-1 : ℝ) ^ (2 * N + 1) - a| = 1 + a ∧
      1 < |(-1 : ℝ) ^ (2 * N + 1) - a| := by
  sorry

/-- Nhận xét 2.3.13: |uₙ| có thể hội tụ dù uₙ phân kì. -/
theorem abs_convergence_converse_counterexample :
    ConvergesTo (fun n ↦ |(-1 : ℝ) ^ n|) 1 ∧ IsDivergent (fun n ↦ (-1 : ℝ) ^ n) := by
  constructor
  · simpa only [abs_pow, abs_neg, abs_one, one_pow] using constant_converges 1
  · exact alternating_isDivergent

/-- Ví dụ 2.3.10, dòng 1016: cận cho sai số. -/
theorem quadratic_ratio_error_bound (n : ℕ) (hn : 1 ≤ n) :
    |((n : ℝ) ^ 2 + n + 2) / ((n : ℝ) ^ 2 + 1) - 1| ≤ 2 / (n : ℝ) := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hden : 0 < (n : ℝ) ^ 2 + 1 := by positivity
  have heq : ((n : ℝ) ^ 2 + n + 2) / ((n : ℝ) ^ 2 + 1) - 1 =
      ((n : ℝ) + 1) / ((n : ℝ) ^ 2 + 1) := by field_simp; ring
  rw [heq, abs_of_pos (div_pos (by positivity) hden)]
  apply (div_le_div_iff₀ hden hnpos).mpr
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- Ví dụ 2.3.10: giới hạn theo định nghĩa ε–N. -/
theorem quadratic_ratio_converges :
    ConvergesTo (fun n ↦ ((n : ℝ) ^ 2 + n + 2) / ((n : ℝ) ^ 2 + 1)) 1 :=
  convergesTo_of_error_le_const_div (by norm_num) quadratic_ratio_error_bound

/-- Dòng 1016: n=1 là phản ví dụ cho đẳng thức sai số. -/
theorem quadratic_ratio_printed_equality_counterexample :
    |((1 : ℝ) ^ 2 + 1 + 2) / ((1 : ℝ) ^ 2 + 1) - 1| ≠ 2 / (1 : ℝ) := by norm_num

/-- Bài tập 2.3.2(a): 5n/(n+1)→5. -/
theorem linear_ratio_converges : ConvergesTo (fun n ↦ 5 * (n : ℝ) / (n + 1)) 5 := by
  apply convergesTo_of_error_le_const_div (C := 5) (by norm_num)
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have heq : 5 * (n : ℝ) / (n + 1) - 5 = -(5 / (n + 1)) := by field_simp; ring
  rw [heq, abs_neg, abs_of_pos (div_pos (by norm_num) (by positivity))]
  exact div_le_div_of_nonneg_left (by norm_num) hnpos (by linarith)

/-- Bài tập 2.3.2(c): (2n²+1)/(n²+n+1)→2. -/
theorem second_quadratic_ratio_converges :
    ConvergesTo (fun n ↦ (2 * (n : ℝ) ^ 2 + 1) / ((n : ℝ) ^ 2 + n + 1)) 2 := by
  apply convergesTo_of_error_le_const_div (C := 3) (by norm_num)
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < (n : ℝ) ^ 2 + n + 1 := by positivity
  have heq : (2 * (n : ℝ) ^ 2 + 1) / ((n : ℝ) ^ 2 + n + 1) - 2 =
      -((2 * (n : ℝ) + 1) / ((n : ℝ) ^ 2 + n + 1)) := by field_simp; ring
  rw [heq, abs_neg, abs_of_pos (div_pos (by positivity) hden)]
  apply (div_le_div_iff₀ hden hnpos).mpr
  nlinarith [sq_nonneg (n : ℝ)]

/-- Bài tập 2.3.2(d): (2n³+1)/(4n³−n)→1/2. -/
theorem cubic_ratio_converges :
    ConvergesTo (fun n ↦ (2 * (n : ℝ) ^ 3 + 1) / (4 * (n : ℝ) ^ 3 - n)) (1 / 2) := by
  apply convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hcube : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn1)]
  have hden : 0 < 4 * (n : ℝ) ^ 3 - n := by linarith
  have heq : (2 * (n : ℝ) ^ 3 + 1) / (4 * (n : ℝ) ^ 3 - n) - 1 / 2 =
      ((n : ℝ) + 2) / (2 * (4 * (n : ℝ) ^ 3 - n)) := by
    rw [div_sub_div _ _ (ne_of_gt hden) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1 <;> ring
  rw [heq, abs_of_pos (div_pos (by positivity) (by positivity))]
  apply (div_le_div_iff₀ (by positivity) hnpos).mpr
  nlinarith

/-- Bài tập 2.3.2(e): (3ⁿ+1)/3ⁿ→1. -/
theorem geometric_ratio_converges :
    ConvergesTo (fun n ↦ ((3 : ℝ) ^ n + 1) / 3 ^ n) 1 := by
  intro ε hε
  obtain ⟨N, hN, hn⟩ := reciprocal_geometric_converges 3 (by norm_num) ε hε
  refine ⟨N, hN, fun n hnn ↦ ?_⟩
  have heq : ((3 : ℝ) ^ n + 1) / 3 ^ n - 1 = 1 / 3 ^ n := by
    field_simp
    ring
  rw [heq]
  simpa only [sub_zero] using hn n hnn

/-- Bài tập 2.3.2(f): cos n/n→0. -/
theorem cosine_div_converges : ConvergesTo (fun n ↦ Real.cos (n : ℝ) / n) 0 := by
  apply convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [sub_zero, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hnpos.le

/-- Bài tập 2.3.5: dãy có giới hạn dương thì các số hạng dương từ một ngưỡng. -/
theorem eventually_positive {u : ℕ → ℝ} {a : ℝ} (h : ConvergesTo u a) (ha : 0 < a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 0 < u n := by
  obtain ⟨N, hN, hn⟩ := h a ha
  refine ⟨N, hN, fun n hnn ↦ ?_⟩
  have hsmall := (abs_lt.mp (hn n hnn)).1
  linarith


theorem successor_converges {u : ℕ → ℝ} {a : ℝ} (h : ConvergesTo u a) :
    ConvergesTo (fun n ↦ u (n + 1)) a := by
  intro ε hε
  obtain ⟨N, hN, hn⟩ := h ε hε
  exact ⟨N, hN, fun n hnn ↦ hn (n + 1) (by omega)⟩

/-- Bài tập 2.3.6: tử và mẫu của tỉ số dương từ một ngưỡng. -/
theorem successor_ratio_eventually_defined {u : ℕ → ℝ} {a : ℝ}
    (h : ConvergesTo u a) (ha : 0 < a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 0 < u n ∧ 0 < u (n + 1) := by
  obtain ⟨N, hN, hn⟩ := eventually_positive h ha
  exact ⟨N, hN, fun n hnn ↦ ⟨hn n hnn, hn (n + 1) (by omega)⟩⟩

/-- Bài tập 2.3.6: khi a>0, tỉ số uₙ₊₁/uₙ tiến về 1. -/
theorem successor_ratio_converges {u : ℕ → ℝ} {a : ℝ}
    (h : ConvergesTo u a) (ha : 0 < a) : ConvergesTo (fun n ↦ u (n + 1) / u n) 1 := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [div_self (ne_of_gt ha)] using!
    (convergesTo_iff_tendsto.mp (successor_converges h)).div
      (convergesTo_iff_tendsto.mp h) (ne_of_gt ha)

/-- Bài tập 2.3.6, phản ví dụ khi a=0: u_n=1/2^n có thương hằng 1/2. -/
theorem successor_ratio_at_zero_counterexample :
    ConvergesTo (fun n ↦ 1 / (2 : ℝ) ^ n) 0 ∧
    (∀ n : ℕ, (1 / (2 : ℝ) ^ (n + 1)) / (1 / (2 : ℝ) ^ n) = 1 / 2) ∧
    ¬ ConvergesTo (fun n ↦ (1 / (2 : ℝ) ^ (n + 1)) / (1 / (2 : ℝ) ^ n)) 1 := by
  have hratio : ∀ n : ℕ, (1 / (2 : ℝ) ^ (n + 1)) / (1 / (2 : ℝ) ^ n) = 1 / 2 := by
    intro n
    rw [pow_succ]
    field_simp
  refine ⟨reciprocal_two_pow_converges, hratio, ?_⟩
  intro h
  have hc : ConvergesTo (fun n ↦ (1 / (2 : ℝ) ^ (n + 1)) / (1 / (2 : ℝ) ^ n)) (1 / 2) :=
    (convergesTo_congr (fun n _ ↦ hratio n)).mpr (constant_converges (1 / 2))
  have := limit_unique h hc
  norm_num at this

/-- Bài tập 2.3.9(a). -/
theorem one_sub_converges {u : ℕ → ℝ} (h : ConvergesTo u 1) :
    ConvergesTo (fun n ↦ 1 - u n) 0 := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub (convergesTo_iff_tendsto.mp h)

/-- Bài tập 2.3.9(b). -/
theorem three_mul_add_one_converges {u : ℕ → ℝ} (h : ConvergesTo u 1) :
    ConvergesTo (fun n ↦ 3 * u n + 1) 4 := by
  apply convergesTo_iff_tendsto.mpr
  convert ((tendsto_const_nhds (x := (3 : ℝ))).mul
    (convergesTo_iff_tendsto.mp h)).add (tendsto_const_nhds (x := (1 : ℝ))) using 1
  norm_num

/-- Bài tập 2.3.9(c): miền xác định của thương bắt đầu từ một ngưỡng dương. -/
theorem square_add_two_div_eventually_defined {u : ℕ → ℝ} (h : ConvergesTo u 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 0 < u n :=
  eventually_positive h (by norm_num)

/-- Bài tập 2.3.9(c): nếu uₙ→1 thì (2+uₙ²)/uₙ→3. -/
theorem square_add_two_div_converges {u : ℕ → ℝ} (h : ConvergesTo u 1) :
    ConvergesTo (fun n ↦ (2 + u n ^ 2) / u n) 3 := by
  apply convergesTo_iff_tendsto.mpr
  have hu := convergesTo_iff_tendsto.mp h
  convert! ((tendsto_const_nhds (x := (2 : ℝ))).add (hu.pow 2)).div hu
    (by norm_num : (1 : ℝ) ≠ 0) using 1
  norm_num

/-- Bài tập 2.3.7: dãy hữu tỉ ⌊nx⌋/n tại n≥1. -/
noncomputable def rationalApproximation (x : ℝ) (n : ℕ) : ℚ :=
  (Int.floor ((n : ℝ) * x) : ℚ) / (n : ℚ)


theorem rationalApproximation_cast (x : ℝ) (n : ℕ) :
    (rationalApproximation x n : ℝ) = (Int.floor ((n : ℝ) * x) : ℝ) / (n : ℝ) := by
  simp only [rationalApproximation, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

/-- Sai số của ⌊nx⌋/n không vượt 1/n. -/
theorem rationalApproximation_error_bound (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |(rationalApproximation x n : ℝ) - x| ≤ 1 / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hfloor := Int.floor_le ((n : ℝ) * x)
  have hlt := Int.lt_floor_add_one ((n : ℝ) * x)
  rw [rationalApproximation_cast]
  have heq : (Int.floor ((n : ℝ) * x) : ℝ) / n - x =
      -(((n : ℝ) * x - Int.floor ((n : ℝ) * x)) / n) := by field_simp; ring
  rw [heq, abs_neg, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hfloor) hnpos.le)]
  apply div_le_div_of_nonneg_right _ hnpos.le
  linarith

/-- Bài tập 2.3.7: dãy hữu tỉ hội tụ về x. -/
theorem rationalApproximation_converges (x : ℝ) :
    ConvergesTo (fun n ↦ (rationalApproximation x n : ℝ)) x :=
  convergesTo_of_error_le_const_div (by norm_num) (rationalApproximation_error_bound x)

/-- Bài tập 2.3.7: tồn tại dãy hữu tỉ hội tụ về mỗi số thực. -/
theorem exists_rational_sequence_converges (x : ℝ) :
    ∃ r : ℕ → ℚ, ConvergesTo (fun n ↦ (r n : ℝ)) x :=
  ⟨rationalApproximation x, rationalApproximation_converges x⟩

/-- Dãy vô tỉ cụ thể cho Bài tập 2.3.8: cộng √2/n vào dãy hữu tỉ tiến về x. -/
noncomputable def irrationalApproximation (x : ℝ) (n : ℕ) : ℝ :=
  (rationalApproximation x n : ℝ) + Real.sqrt 2 / (n : ℝ)

/-- Các số hạng tại n≥1 đều vô tỉ. -/
theorem irrationalApproximation_irrational (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Irrational (irrationalApproximation x n) := by
  exact (irrational_sqrt_two.div_natCast (by omega : n ≠ 0)).ratCast_add
    (rationalApproximation x n)

/-- Bài tập 2.3.8: dãy vô tỉ hội tụ về x. -/
theorem irrationalApproximation_converges (x : ℝ) : ConvergesTo (irrationalApproximation x) x := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [irrationalApproximation, add_zero] using!
    (convergesTo_iff_tendsto.mp (rationalApproximation_converges x)).add
      (tendsto_const_div_atTop_nhds_zero_nat (Real.sqrt 2))

/-- Bài tập 2.3.8: tồn tại dãy vô tỉ tiến về mỗi x thực. -/
theorem exists_irrational_sequence_converges (x : ℝ) :
    ∃ s : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → Irrational (s n)) ∧ ConvergesTo s x :=
  ⟨irrationalApproximation x, irrationalApproximation_irrational x,
    irrationalApproximation_converges x⟩

/-- Bài tập 2.3.3: dãy phần nguyên tiến về √2; dãy hằng √2 có từng số hạng vô tỉ. -/
theorem sqrt_two_approximating_sequences :
    ConvergesTo (fun n ↦ (rationalApproximation (Real.sqrt 2) n : ℝ)) (Real.sqrt 2) ∧
    (∀ n : ℕ, 1 ≤ n → Irrational ((fun _ : ℕ ↦ Real.sqrt 2) n)) ∧
    ConvergesTo (fun _ ↦ Real.sqrt 2) (Real.sqrt 2) :=
  ⟨rationalApproximation_converges _, fun _ _ ↦ irrational_sqrt_two, constant_converges _⟩

/-- Bài tập 2.3.4: dãy hữu tỉ hằng 2026 và dãy vô tỉ cụ thể cùng tiến về 2026. -/
theorem integer_2026_approximating_sequences :
    ConvergesTo (fun _ : ℕ ↦ ((2026 : ℚ) : ℝ)) 2026 ∧
    (∀ n : ℕ, 1 ≤ n → Irrational (irrationalApproximation 2026 n)) ∧
    ConvergesTo (irrationalApproximation 2026) 2026 := by
  exact ⟨constant_converges _, irrationalApproximation_irrational _,
    irrationalApproximation_converges _⟩

end calculus.Chapter02.Section03
