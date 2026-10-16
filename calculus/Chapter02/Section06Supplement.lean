import calculus.Chapter02.Section06
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Mục 2.6: bài tập bổ sung

Nguồn: `source/Ch2_dayso.tex`, dòng 2153–2211; Bài 2.6.19–25, mã C02-S07.
-/
namespace calculus.Chapter02.Section06Supplement
open Filter Set
open scoped Topology BigOperators
open calculus.Chapter02.Section03 calculus.Chapter02.Section04 calculus.Chapter02.Section06

/-- Bài 2.6.20: hai điều kiện đầu bằng 0 buộc cả hai dãy bằng 0. -/
theorem zero_initial_coupled_recurrence (x y : ℕ → ℝ)
    (hx : x 0 = 0) (hy : y 0 = 0)
    (hynext : ∀ n, y (n + 1) = x n + y n)
    (hxnext : ∀ n, x (n + 1) = x n + 2 * y (n + 1)) :
    ∀ n, x n = 0 ∧ y n = 0 := by
  intro n
  induction n with
  | zero => exact ⟨hx, hy⟩
  | succ n ih =>
    have hys : y (n + 1) = 0 := by rw [hynext n, ih.1, ih.2]; ring
    exact ⟨by rw [hxnext n, ih.1, hys]; ring, hys⟩

/-- Bài 2.6.20: x=y=0 thỏa truy hồi nhưng biểu thức không bằng ±1. -/
theorem zero_initial_pell_counterexample :
    (∀ _n : ℕ, (0 : ℝ) = 0 + 0 ∧ (0 : ℝ) = 0 + 2 * 0) ∧
    ¬ ((0 : ℝ) ^ 2 - 2 * 0 ^ 2 = 1 ∨ (0 : ℝ) ^ 2 - 2 * 0 ^ 2 = -1) := by
  constructor <;> norm_num

/-- Trung bình cộng của x₁,…,xₙ, với n≥1. -/
noncomputable def arithmeticMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, x k) / n

/-- Bài 2.6.22: trung bình cộng hội tụ về cùng giới hạn với dãy gốc. -/
theorem arithmeticMean_converges (x : ℕ → ℝ) (a : ℝ) (hx : ConvergesTo x a) :
    ConvergesTo (arithmeticMean x) a := by
  apply convergesTo_iff_tendsto.mpr
  have hs : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 a) :=
    (convergesTo_iff_tendsto.mp hx).comp (tendsto_add_atTop_nat 1)
  have hc := hs.cesaro
  convert hc using 1
  ext n
  simp only [arithmeticMean]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Bài 2.6.25(a): giới hạn với số mũ thực k≥1. -/
theorem log_base_div_real_rpow_converges (a : ℝ) (_ha : 1 < a) (k : ℝ) (hk : 1 ≤ k) :
    ConvergesTo (fun n : ℕ => Real.logb a n / (n : ℝ) ^ k) 0 := by
  apply convergesTo_iff_tendsto.mpr
  have hlog := (isLittleO_log_rpow_atTop (show 0 < k by linarith)).tendsto_div_nhds_zero
  have hnat := hlog.comp tendsto_natCast_atTop_atTop
  have hscaled := hnat.div_const (Real.log a)
  convert hscaled using 1
  · ext n
    dsimp only [Function.comp_def]
    rw [Real.logb]
    ring
  · simp

/-- Bài 2.6.25(a), log cơ số a, số mũ tự nhiên k≥1. -/
theorem log_base_div_nat_pow_converges (a : ℝ) (_ha : 1 < a) (k : ℕ) (hk : 1 ≤ k) :
    ConvergesTo (fun n : ℕ => Real.logb a n / (n : ℝ) ^ k) 0 := by
  apply convergesTo_iff_tendsto.mpr
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (k : ℝ) by exact_mod_cast (show 0 < k by omega))).tendsto_div_nhds_zero
  have hnat := hlog.comp tendsto_natCast_atTop_atTop
  have hscaled := hnat.div_const (Real.log a)
  convert hscaled using 1
  · ext n
    dsimp only [Function.comp_def]
    rw [Real.logb, Real.rpow_natCast]
    ring
  · simp

/-- Trung bình cộng và trung bình nhân bảo toàn thứ tự dương, đồng thời giảm khoảng cách. -/
theorem arithmetic_geometric_step (x y : ℝ) (hy : 0 < y) (hyx : y < x) :
    0 < Real.sqrt (x * y) ∧ Real.sqrt (x * y) < (x + y) / 2 ∧
      y < Real.sqrt (x * y) ∧ (x + y) / 2 < x ∧
      0 < (x + y) / 2 - Real.sqrt (x * y) ∧
      (x + y) / 2 - Real.sqrt (x * y) < (x - y) / 2 := by
  have hx : 0 < x := lt_trans hy hyx
  have hroot := Real.sqrt_nonneg (x * y)
  have hsq := Real.sq_sqrt (mul_nonneg hx.le hy.le)
  have hrpos : 0 < Real.sqrt (x * y) := Real.sqrt_pos.2 (mul_pos hx hy)
  have hyr : y < Real.sqrt (x * y) := by nlinarith [sq_pos_of_pos (sub_pos.mpr hyx)]
  have hram : Real.sqrt (x * y) < (x + y) / 2 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hyx)]
  exact ⟨hrpos, hram, hyr, by linarith, by linarith, by linarith⟩

/-- Bài 2.6.19(a): 0<yₙ<xₙ tại mọi chỉ số. -/
theorem arithmetic_geometric_recurrence_order (x y : ℕ → ℝ)
    (hy : 0 < y 1) (hyx : y 1 < x 1)
    (hxnext : ∀ n, 1 ≤ n → x (n + 1) = (x n + y n) / 2)
    (hynext : ∀ n, 1 ≤ n → y (n + 1) = Real.sqrt (x n * y n)) :
    ∀ n, 1 ≤ n → 0 < y n ∧ y n < x n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨hy, hyx⟩
  | succ n hn ih =>
    have hstep := arithmetic_geometric_step (x n) (y n) ih.1 ih.2
    rw [hxnext n hn, hynext n hn]
    exact ⟨hstep.1, hstep.2.1⟩

/-- Bài 2.6.19(b): y tăng, x giảm và cả hai bị chặn. -/
theorem arithmetic_geometric_recurrence_monotone_bounded (x y : ℕ → ℝ)
    (hy : 0 < y 1) (hyx : y 1 < x 1)
    (hxnext : ∀ n, 1 ≤ n → x (n + 1) = (x n + y n) / 2)
    (hynext : ∀ n, 1 ≤ n → y (n + 1) = Real.sqrt (x n * y n)) :
    SequenceIncreasing y ∧ SequenceBoundedAbove y ∧ SequenceDecreasing x ∧ SequenceBoundedBelow x := by
  have horder := arithmetic_geometric_recurrence_order x y hy hyx hxnext hynext
  have hyinc : SequenceIncreasing y := by
    intro n hn
    rw [hynext n hn]
    exact (arithmetic_geometric_step (x n) (y n) (horder n hn).1 (horder n hn).2).2.2.1.le
  have hxdec : SequenceDecreasing x := by
    intro n hn
    rw [hxnext n hn]
    exact (arithmetic_geometric_step (x n) (y n) (horder n hn).1 (horder n hn).2).2.2.2.1.le
  have hxfirst : ∀ n, 1 ≤ n → x n ≤ x 1 := by
    intro n hn
    exact (sequenceDecreasing_iff_antitoneOn x).mp hxdec (by simp) hn hn
  exact ⟨hyinc, ⟨x 1, fun n hn => (horder n hn).2.le.trans (hxfirst n hn)⟩,
    hxdec, ⟨0, fun n hn => (horder n hn).1.le.trans (horder n hn).2.le⟩⟩

/-- Bài 2.6.19(c): cận ngặt bắt đầu tại n=1. -/
theorem arithmetic_geometric_recurrence_gap (x y : ℕ → ℝ)
    (hy : 0 < y 1) (hyx : y 1 < x 1)
    (hxnext : ∀ n, 1 ≤ n → x (n + 1) = (x n + y n) / 2)
    (hynext : ∀ n, 1 ≤ n → y (n + 1) = Real.sqrt (x n * y n)) :
    ∀ n, 1 ≤ n → 0 < x (n + 1) - y (n + 1) ∧
      x (n + 1) - y (n + 1) < (x 1 - y 1) / (2 : ℝ) ^ n := by
  have horder := arithmetic_geometric_recurrence_order x y hy hyx hxnext hynext
  have hcontract : ∀ n, 1 ≤ n → 0 < x (n + 1) - y (n + 1) ∧
      x (n + 1) - y (n + 1) < (x n - y n) / 2 := by
    intro n hn
    rw [hxnext n hn, hynext n hn]
    exact (arithmetic_geometric_step (x n) (y n) (horder n hn).1 (horder n hn).2).2.2.2.2
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hcontract 1 (by omega)
  | succ n hn ih =>
    refine ⟨(hcontract (n + 1) (by omega)).1, ?_⟩
    calc
      x (n + 1 + 1) - y (n + 1 + 1) < (x (n + 1) - y (n + 1)) / 2 :=
        (hcontract (n + 1) (by omega)).2
      _ < ((x 1 - y 1) / (2 : ℝ) ^ n) / 2 := div_lt_div_of_pos_right ih.2 (by norm_num)
      _ = (x 1 - y 1) / (2 : ℝ) ^ (n + 1) := by rw [pow_succ, div_div]

/-- Bài 2.6.19(d): cả hai dãy hội tụ đến cùng một giới hạn. -/
theorem arithmetic_geometric_recurrence_common_limit (x y : ℕ → ℝ)
    (hy : 0 < y 1) (hyx : y 1 < x 1)
    (hxnext : ∀ n, 1 ≤ n → x (n + 1) = (x n + y n) / 2)
    (hynext : ∀ n, 1 ≤ n → y (n + 1) = Real.sqrt (x n * y n)) :
    ∃ a : ℝ, ConvergesTo x a ∧ ConvergesTo y a := by
  obtain ⟨hyi, hyb, hxd, hxb⟩ :=
    arithmetic_geometric_recurrence_monotone_bounded x y hy hyx hxnext hynext
  obtain ⟨a, ha⟩ := decreasing_bounded_convergent x hxd hxb
  obtain ⟨b, hb⟩ := increasing_bounded_convergent y hyi hyb
  have hxs := convergesTo_iff_tendsto.mp (successor_converges ha)
  have hab := ((convergesTo_iff_tendsto.mp ha).add (convergesTo_iff_tendsto.mp hb)).div_const 2
  have hxseq : Tendsto (fun n => (x n + y n) / 2) atTop (𝓝 a) := by
    apply hxs.congr'
    exact eventually_atTop.2 ⟨1, fun n hn => hxnext n hn⟩
  have heq : a = (a + b) / 2 := tendsto_nhds_unique hxseq hab
  have hba : b = a := by linarith
  exact ⟨a, ha, by simpa only [hba] using hb⟩

/-- Trung bình điều hòa; cần mẫu tổng khác 0. -/
noncomputable def harmonicMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  n / (∑ k ∈ Finset.Icc 1 n, 1 / x k)

/-- Bài 2.6.22: dãy phản ví dụ có số hạng khác 0 và giới hạn 0. -/
noncomputable def alternatingReciprocal (n : ℕ) : ℝ := (-1 : ℝ) ^ n / n

theorem alternatingReciprocal_converges : ConvergesTo alternatingReciprocal 0 :=
  alternating_reciprocal_converges

theorem alternatingReciprocal_nonzero (n : ℕ) (hn : 1 ≤ n) :
    alternatingReciprocal n ≠ 0 := by
  apply div_ne_zero (pow_ne_zero _ (by norm_num))
  exact_mod_cast (show n ≠ 0 by omega)


theorem alternatingReciprocal_inv (n : ℕ) :
    1 / alternatingReciprocal n = (-1 : ℝ) ^ n * n := by
  rw [alternatingReciprocal, one_div_div, div_eq_mul_inv, ← inv_pow]
  norm_num
  ring

/-- Tổng các nghịch đảo tại chỉ số chẵn. -/
theorem alternatingReciprocal_sum_even (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * m), 1 / alternatingReciprocal k) = m := by
  simp_rw [alternatingReciprocal_inv]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    simp [pow_add, pow_mul]
    ring

/-- Tổng các nghịch đảo ở chỉ số lẻ. -/
theorem alternatingReciprocal_sum_odd (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * m + 1), 1 / alternatingReciprocal k) = -(m + 1 : ℝ) := by
  rw [Finset.sum_Icc_succ_top (by omega), alternatingReciprocal_sum_even,
    alternatingReciprocal_inv]
  simp [pow_add, pow_mul]
  ring

/-- Mẫu của trung bình điều hòa khác 0 tại n≥1. -/
theorem alternatingReciprocal_sum_nonzero (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 n, 1 / alternatingReciprocal k) ≠ 0 := by
  obtain ⟨m, he | ho⟩ := Nat.even_or_odd' n
  · rw [he, alternatingReciprocal_sum_even]
    exact_mod_cast (show m ≠ 0 by omega)
  · rw [ho, alternatingReciprocal_sum_odd]
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

/-- Dãy con chẵn của trung bình điều hòa phản ví dụ luôn bằng 2. -/
theorem alternating_harmonicMean_even (m : ℕ) (hm : 1 ≤ m) :
    harmonicMean alternatingReciprocal (2 * m) = 2 := by
  rw [harmonicMean, alternatingReciprocal_sum_even]
  have hmn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  field_simp

/-- Dãy con lẻ của trung bình điều hòa có công thức âm. -/
theorem alternating_harmonicMean_odd (m : ℕ) :
    harmonicMean alternatingReciprocal (2 * m + 1) = -(2 * (m : ℝ) + 1) / (m + 1) := by
  simp only [harmonicMean, alternatingReciprocal_sum_odd, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_neg, neg_div]

/-- Bài 2.6.22: phản ví dụ với các số hạng và tổng nghịch đảo đều khác 0. -/
theorem harmonic_mean_source_counterexample :
    ConvergesTo alternatingReciprocal 0 ∧
    (∀ n, 1 ≤ n → alternatingReciprocal n ≠ 0) ∧
    (∀ n, 1 ≤ n → (∑ k ∈ Finset.Icc 1 n, 1 / alternatingReciprocal k) ≠ 0) ∧
    ¬ ConvergesTo (harmonicMean alternatingReciprocal) 0 := by
  refine ⟨alternatingReciprocal_converges, alternatingReciprocal_nonzero,
    alternatingReciprocal_sum_nonzero, ?_⟩
  intro hzero
  obtain ⟨N, hN, htail⟩ := hzero 1 (by norm_num)
  have heven := alternating_harmonicMean_even N hN
  have hbad := htail (2 * N) (by omega)
  rw [heven] at hbad
  norm_num at hbad

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S07-exercise-004: trung bình điều hòa của các số hạng dương là số dương. -/
theorem positive_harmonic_mean_domain (x : ℕ → ℝ)
    (hx : ∀ n : ℕ, 1 ≤ n → 0 < x n) (n : ℕ) (hn : 1 ≤ n) :
    0 < (n : ℝ) ∧ 0 < (∑ k ∈ Finset.Icc 1 n, 1 / x k) ∧
      0 < harmonicMean x n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < ∑ k ∈ Finset.Icc 1 n, 1 / x k := by
    apply Finset.sum_pos'
    · intro k hk
      exact (one_div_pos.mpr (hx k (Finset.mem_Icc.mp hk).1)).le
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, one_div_pos.mpr (hx 1 le_rfl)⟩
  exact ⟨hnpos, hs, div_pos hnpos hs⟩

/-- Trung bình điều hòa của dãy dương hội tụ về cùng giới hạn khi giới hạn ấy dương. -/
theorem positive_limit_harmonic_mean_converges (x : ℕ → ℝ) (a : ℝ)
    (_hxpos : ∀ n : ℕ, 1 ≤ n → 0 < x n)
    (hx : ConvergesTo x a) (ha : 0 < a) :
    ConvergesTo (harmonicMean x) a := by
  have hi : ConvergesTo (fun n ↦ 1 / x n) (1 / a) :=
    convergesTo_iff_tendsto.mpr (tendsto_const_nhds.div
      (convergesTo_iff_tendsto.mp hx) ha.ne')
  have hm := arithmeticMean_converges (fun n ↦ 1 / x n) (1 / a) hi
  have hh := (convergesTo_iff_tendsto.mp hm).inv₀ (one_div_ne_zero ha.ne')
  apply convergesTo_iff_tendsto.mpr
  change Tendsto (fun n ↦ harmonicMean x n) atTop (𝓝 a)
  simpa only [arithmeticMean, harmonicMean, inv_div, inv_one, inv_inv,
    one_div, div_eq_mul_inv, mul_inv_rev, mul_one, one_mul, mul_comm] using hh

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- Bài 2.6.22, dòng 2172–2176: khẳng định gốc về giới hạn của trung bình cộng và trung bình điều hòa. -/
theorem source_arithmetic_harmonic_mean_convergence (x : ℕ → ℝ) (a : ℝ)
    (hx : ConvergesTo x a) :
    ConvergesTo (arithmeticMean x) a ∧ ConvergesTo (harmonicMean x) a := by
  sorry

/-- Trung bình điều hòa nằm ngặt giữa hai số dương khác nhau. -/
theorem harmonic_step_between (x y : ℝ) (hy : 0 < y) (hyx : y < x) :
    y < 2 * x * y / (x + y) ∧ 2 * x * y / (x + y) < x := by
  have hx : 0 < x := hy.trans hyx
  have hs : 0 < x + y := add_pos hx hy
  constructor
  · apply (lt_div_iff₀ hs).2
    nlinarith [mul_pos hy (sub_pos.mpr hyx)]
  · apply (div_lt_iff₀ hs).2
    nlinarith [mul_pos hx (sub_pos.mpr hyx)]

/-- Bài 2.6.21: bảo toàn thứ tự dương từ x₀=2√3, y₀=3. -/
theorem harmonic_geometric_recurrence_order (x y : ℕ → ℝ)
    (hxzero : x 0 = 2 * Real.sqrt 3) (hyzero : y 0 = 3)
    (hxnext : ∀ n, x (n + 1) = 2 * x n * y n / (x n + y n))
    (hynext : ∀ n, y (n + 1) = Real.sqrt (x (n + 1) * y n)) :
    ∀ n, 0 < y n ∧ y n < x n := by
  intro n
  induction n with
  | zero =>
    rw [hxzero, hyzero]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    constructor
    · norm_num
    · nlinarith
  | succ n ih =>
    have hbetween := harmonic_step_between (x n) (y n) ih.1 ih.2
    have hnew : y n < x (n + 1) := by rw [hxnext n]; exact hbetween.1
    have hp : 0 < x (n + 1) := ih.1.trans hnew
    have hr := Real.sqrt_nonneg (x (n + 1) * y n)
    have hs := Real.sq_sqrt (mul_nonneg hp.le ih.1.le)
    have hpos : 0 < Real.sqrt (x (n + 1) * y n) := Real.sqrt_pos.2 (mul_pos hp ih.1)
    have hlt : Real.sqrt (x (n + 1) * y n) < x (n + 1) := by
      nlinarith [mul_pos hp (sub_pos.mpr hnew)]
    rw [hynext n]
    exact ⟨hpos, hlt⟩

/-- Bài 2.6.21: y tăng, x giảm và bị chặn. -/
theorem harmonic_geometric_recurrence_monotone_bounded (x y : ℕ → ℝ)
    (hxzero : x 0 = 2 * Real.sqrt 3) (hyzero : y 0 = 3)
    (hxnext : ∀ n, x (n + 1) = 2 * x n * y n / (x n + y n))
    (hynext : ∀ n, y (n + 1) = Real.sqrt (x (n + 1) * y n)) :
    SequenceIncreasing y ∧ SequenceBoundedAbove y ∧ SequenceDecreasing x ∧ SequenceBoundedBelow x ∧
      (∀ n, 3 ≤ y n) := by
  have ho := harmonic_geometric_recurrence_order x y hxzero hyzero hxnext hynext
  have hyall : ∀ n, y n ≤ y (n + 1) := by
    intro n
    have hbetween := harmonic_step_between (x n) (y n) (ho n).1 (ho n).2
    have hnew : y n < x (n + 1) := by rw [hxnext n]; exact hbetween.1
    have hp : 0 < x (n + 1) := (ho n).1.trans hnew
    have hr := Real.sqrt_nonneg (x (n + 1) * y n)
    have hs := Real.sq_sqrt (mul_nonneg hp.le (ho n).1.le)
    rw [hynext n]
    nlinarith [mul_pos (ho n).1 (sub_pos.mpr hnew)]
  have hxall : ∀ n, x (n + 1) ≤ x n := by
    intro n
    rw [hxnext n]
    exact (harmonic_step_between (x n) (y n) (ho n).1 (ho n).2).2.le
  have hym : Monotone y := monotone_nat_of_le_succ hyall
  have hxm : Antitone x := antitone_nat_of_succ_le hxall
  have hybound : ∀ n, 3 ≤ y n := by
    intro n
    simpa only [hyzero] using hym (Nat.zero_le n)
  exact ⟨fun n _ => hyall n, ⟨x 0, fun n _ => (ho n).2.le.trans (hxm (Nat.zero_le n))⟩,
    fun n _ => hxall n, ⟨0, fun n _ => (ho n).1.le.trans (ho n).2.le⟩, hybound⟩

/-- Bài 2.6.21: hai dãy có cùng giới hạn. -/
theorem harmonic_geometric_recurrence_common_limit (x y : ℕ → ℝ)
    (hxzero : x 0 = 2 * Real.sqrt 3) (hyzero : y 0 = 3)
    (hxnext : ∀ n, x (n + 1) = 2 * x n * y n / (x n + y n))
    (hynext : ∀ n, y (n + 1) = Real.sqrt (x (n + 1) * y n)) :
    SequenceDecreasing x ∧ SequenceIncreasing y ∧ ∃ a : ℝ, ConvergesTo x a ∧ ConvergesTo y a := by
  obtain ⟨hyi, hyb, hxd, hxb, hyl⟩ :=
    harmonic_geometric_recurrence_monotone_bounded x y hxzero hyzero hxnext hynext
  obtain ⟨a, ha⟩ := decreasing_bounded_convergent x hxd hxb
  obtain ⟨b, hb⟩ := increasing_bounded_convergent y hyi hyb
  have hypos : 3 ≤ b := limit_le_of_converges (fun _ => 3) y 3 b
    (constant_converges 3) hb (fun n _ => hyl n)
  have hxshift := convergesTo_iff_tendsto.mp (successor_converges ha)
  have hyshift := convergesTo_iff_tendsto.mp (successor_converges hb)
  have ho := harmonic_geometric_recurrence_order x y hxzero hyzero hxnext hynext
  have hsquare : Tendsto (fun n => x (n + 1) * y n) atTop (𝓝 (b ^ 2)) := by
    apply (hyshift.pow 2).congr
    intro n
    rw [hynext n, Real.sq_sqrt]
    exact mul_nonneg ((ho (n + 1)).1.le.trans (ho (n + 1)).2.le) (ho n).1.le
  have heq : b ^ 2 = a * b := tendsto_nhds_unique hsquare (hxshift.mul (convergesTo_iff_tendsto.mp hb))
  have hba : b = a := by
    have hz : (b - a) * b = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · linarith
    · linarith
  exact ⟨hxd, hyi, a, ha, by simpa only [hba] using hb⟩

/-- Căn bậc n của n!, với cơ số dương. -/
noncomputable def factorialRoot (n : ℕ) : ℝ := (n.factorial : ℝ) ^ (1 / (n : ℝ))

/-- Logarit của n chia căn bậc n của n! tiến về 1. -/
theorem factorial_root_log_normalized_converges :
    ConvergesTo (fun n : ℕ => Real.log n - Real.log (n.factorial : ℝ) / n) 1 := by
  apply convergesTo_iff_tendsto.mpr
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    convergesTo_iff_tendsto.mp reciprocal_converges
  have hlogn : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlogtwo : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / n) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => Real.log 2 * (1 / (n : ℝ))) atTop (𝓝 (Real.log 2 * 0))).add hlogn)
    have hzero : Tendsto (fun n : ℕ => Real.log 2 * (1 / (n : ℝ)) + Real.log n / n) atTop (𝓝 0) := by simpa using h
    apply hzero.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [Real.log_mul (by norm_num) hnp.ne', add_div]
    ring
  have hlogstir : Tendsto (fun n => Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) := by
    have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)
    simpa [div_eq_mul_inv] using hs.mul hinv
  have hsum := hlogstir.add (hlogtwo.div_const 2)
  have hmain : Tendsto (fun n : ℕ =>
      1 - (Real.log (Stirling.stirlingSeq n) / n + (Real.log (2 * (n : ℝ)) / n) / 2))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hsum
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [Stirling.log_stirlingSeq_formula, Real.log_div hnp.ne' (Real.exp_ne_zero 1), Real.log_exp]
  field_simp
  ring

/-- Bài 2.6.25(c): n/căn bậc n của n! hội tụ đến e=exp(1). -/
theorem nat_div_factorialRoot_converges :
    ConvergesTo (fun n : ℕ => (n : ℝ) / factorialRoot n) (Real.exp 1) := by
  apply convergesTo_iff_tendsto.mpr
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (convergesTo_iff_tendsto.mp factorial_root_log_normalized_converges)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Function.comp_def]
  rw [Real.exp_sub, Real.exp_log hnp, factorialRoot,
    Real.rpow_def_of_pos (show (0 : ℝ) < (n.factorial : ℝ) by positivity)]
  congr 2
  ring

/-- Bài 2.6.25(b): nghịch đảo căn bậc n của n! hội tụ 0. -/
theorem reciprocal_factorialRoot_converges :
    ConvergesTo (fun n : ℕ => 1 / factorialRoot n) 0 := by
  apply convergesTo_iff_tendsto.mpr
  have h := (convergesTo_iff_tendsto.mp nat_div_factorialRoot_converges).mul
    (convergesTo_iff_tendsto.mp reciprocal_converges)
  have hzero : Tendsto (fun n : ℕ => ((n : ℝ) / factorialRoot n) * (1 / n)) atTop (𝓝 0) := by simpa using h
  apply hzero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hr : factorialRoot n ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  field_simp

end calculus.Chapter02.Section06Supplement
