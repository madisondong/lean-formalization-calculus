import calculus.Chapter02.Section03
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# 2.4. Một số tính chất của dãy hội tụ

Nguồn: `source/Ch2_dayso.tex`, dòng 1165–1643.
-/

namespace calculus.Chapter02.Section04

open Filter Set Function
open scoped Topology

/-- Cận trên của dãy tại các chỉ số n≥1. -/
def SequenceBoundedAbove (u : ℕ → ℝ) : Prop := ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → u n ≤ M

/-- Cận dưới của dãy tại các chỉ số n≥1. -/
def SequenceBoundedBelow (u : ℕ → ℝ) : Prop := ∃ m : ℝ, ∀ n : ℕ, 1 ≤ n → m ≤ u n

/-- Dãy bị chặn khi có cả cận trên và cận dưới. -/
def SequenceBounded (u : ℕ → ℝ) : Prop := SequenceBoundedAbove u ∧ SequenceBoundedBelow u

/-- Tập các số hạng tại n≥1. -/
def sequenceRangeFromOne (u : ℕ → ℝ) : Set ℝ := u '' Ici 1

/-- Nhận xét 2.4.2: cận trên của dãy là cận trên của tập số hạng. -/
theorem sequenceBoundedAbove_iff (u : ℕ → ℝ) : SequenceBoundedAbove u ↔ BddAbove (sequenceRangeFromOne u) := by
  constructor
  · rintro ⟨M, hM⟩; exact ⟨M, by rintro x ⟨n, hn, rfl⟩; exact hM n hn⟩
  · rintro ⟨M, hM⟩; exact ⟨M, fun n hn ↦ hM ⟨n, hn, rfl⟩⟩

/-- Nhận xét 2.4.2: cận dưới của dãy là cận dưới của tập số hạng. -/
theorem sequenceBoundedBelow_iff (u : ℕ → ℝ) : SequenceBoundedBelow u ↔ BddBelow (sequenceRangeFromOne u) := by
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by rintro x ⟨n, hn, rfl⟩; exact hm n hn⟩
  · rintro ⟨m, hm⟩; exact ⟨m, fun n hn ↦ hm ⟨n, hn, rfl⟩⟩

/-- Nhận xét 2.4.2: bị chặn khi và chỉ khi có một cận dương của giá trị tuyệt đối. -/
theorem sequenceBounded_iff_abs (u : ℕ → ℝ) :
    SequenceBounded u ↔ ∃ M > 0, ∀ n : ℕ, 1 ≤ n → |u n| ≤ M := by
  constructor
  · rintro ⟨⟨M, hM⟩, ⟨m, hm⟩⟩
    refine ⟨max |m| |M| + 1, by have := le_max_left |m| |M|; positivity, ?_⟩
    intro n hn
    have hl := hm n hn
    have hu := hM n hn
    have hmaxm := le_max_left |m| |M|
    have hmaxM := le_max_right |m| |M|
    have hmabs := neg_abs_le m
    have hMabs := le_abs_self M
    apply abs_le.mpr
    constructor <;> linarith
  · rintro ⟨M, _, hM⟩
    exact ⟨⟨M, fun n hn ↦ (abs_le.mp (hM n hn)).2⟩,
      ⟨-M, fun n hn ↦ (abs_le.mp (hM n hn)).1⟩⟩

/-- Định lí 2.4.4: dãy hội tụ bị chặn trên toàn bộ các chỉ số n≥1. -/
theorem tendsto_sequenceBounded (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    SequenceBounded u := by
  obtain ⟨M, hM⟩ := hu.bddAbove_range
  obtain ⟨m, hm⟩ := hu.bddBelow_range
  exact ⟨⟨M, fun n _ ↦ hM ⟨n, rfl⟩⟩, ⟨m, fun n _ ↦ hm ⟨n, rfl⟩⟩⟩

/-- Định nghĩa dãy con: chỉ số dương, tăng ngặt, cùng số hạng tương ứng. -/
def IsSequenceSubsequence (u v : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ φ k) ∧ StrictMonoOn φ (Ici 1) ∧
    ∀ k : ℕ, 1 ≤ k → v k = u (φ k)

/-- Bổ đề 2.4.8: chỉ số thứ k của dãy con không nhỏ hơn k. -/
theorem subsequence_index_ge (φ : ℕ → ℕ) (hpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ φ k)
    (hmono : StrictMonoOn φ (Ici 1)) (k : ℕ) (hk : 1 ≤ k) : k ≤ φ k := by
  induction k, hk using Nat.le_induction with
  | base => exact hpos 1 le_rfl
  | succ k hk ih =>
    have hlt := hmono hk (by omega : 1 ≤ k + 1) (by omega : k < k + 1)
    omega

/-- Chỉ số dãy con tiến tới vô cùng. -/
theorem subsequence_index_tendsto (φ : ℕ → ℕ) (hpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ φ k)
    (hmono : StrictMonoOn φ (Ici 1)) : Tendsto φ atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨max N 1, fun k hk ↦
    le_trans (le_trans (le_max_left N 1) hk)
      (subsequence_index_ge φ hpos hmono k (le_trans (le_max_right N 1) hk))⟩

/-- Định lí 2.4.9: mọi dãy con giữ giới hạn của dãy ban đầu. -/
theorem tendsto_sequenceSubsequence (u v : ℕ → ℝ) (a : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : IsSequenceSubsequence u v) :
    Tendsto v atTop (𝓝 a) := by
  obtain ⟨φ, hpos, hmono, hterms⟩ := hv
  exact (hu.comp (subsequence_index_tendsto φ hpos hmono)).congr'
    (eventually_atTop.2 ⟨1, fun k hk ↦ (hterms k hk).symm⟩)

/-- Nhận xét 2.4.10: hai dãy con có hai giới hạn khác nhau buộc dãy gốc phân kì. -/
theorem distinct_subsequence_limits (u v w : ℕ → ℝ) (a b : ℝ)
    (hv : IsSequenceSubsequence u v) (hw : IsSequenceSubsequence u w)
    (hva : Tendsto v atTop (𝓝 a)) (hwb : Tendsto w atTop (𝓝 b)) (hab : a ≠ b) :
    ¬ ∃ c : ℝ, Tendsto u atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  exact hab ((tendsto_nhds_unique hva (tendsto_sequenceSubsequence u v c hc hv)).trans
    (tendsto_nhds_unique hwb (tendsto_sequenceSubsequence u w c hc hw)).symm)

/-- Định lí 2.4.16: bất đẳng thức tại mọi chỉ số n≥1 được bảo toàn khi lấy giới hạn. -/
theorem limit_le_of_positive_terms (u v : ℕ → ℝ) (a b : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n) : a ≤ b :=
  le_of_tendsto_of_tendsto hu hv (eventually_atTop.2 ⟨1, huv⟩)

/-- Trường hợp riêng: giới hạn của dãy trong đoạn đóng vẫn ở trong đoạn. -/
theorem limit_mem_closed_interval (u : ℕ → ℝ) (a b c : ℝ)
    (hu : Tendsto u atTop (𝓝 c)) (hmem : ∀ n : ℕ, 1 ≤ n → u n ∈ Icc a b) :
    c ∈ Icc a b :=
  ⟨limit_le_of_positive_terms (fun _ ↦ a) u a c tendsto_const_nhds hu
      (fun n hn ↦ (hmem n hn).1),
    limit_le_of_positive_terms u (fun _ ↦ b) c b hu tendsto_const_nhds
      (fun n hn ↦ (hmem n hn).2)⟩

/-- Hệ quả 2.4.17 chỉ kết luận ≤, dù từng số hạng có dấu <. -/
theorem limit_le_of_strict_positive_terms (u v : ℕ → ℝ) (a b : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (huv : ∀ n : ℕ, 1 ≤ n → u n < v n) : a ≤ b :=
  limit_le_of_positive_terms u v a b hu hv (fun n hn ↦ (huv n hn).le)

/-- Định lí 2.4.19: định lí kẹp tại các chỉ số dương. -/
theorem squeeze_positive_terms (u v w : ℕ → ℝ) (a : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hw : Tendsto w atTop (𝓝 a))
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n)
    (hvw : ∀ n : ℕ, 1 ≤ n → v n ≤ w n) : Tendsto v atTop (𝓝 a) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hu hw
    (eventually_atTop.2 ⟨1, huv⟩) (eventually_atTop.2 ⟨1, hvw⟩)

/-- Định lí 2.4.21: tích của dãy tiến về 0 và dãy bị chặn tiến về 0. -/
theorem zero_mul_sequenceBounded (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0))
    (hv : SequenceBounded v) : Tendsto (fun n ↦ u n * v n) atTop (𝓝 0) := by
  obtain ⟨M, hMpos, hM⟩ := (sequenceBounded_iff_abs v).mp hv
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall (fun n ↦ norm_nonneg (u n * v n))
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_left (hM n hn) (abs_nonneg (u n))
  · simpa using hu.norm.mul_const M

/-- Ví dụ 2.4.20: sin(n)/n tiến về 0. -/
theorem sin_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.sin n / n) atTop (𝓝 0) := by
  have hb : SequenceBounded (fun n : ℕ ↦ Real.sin n) :=
    (sequenceBounded_iff_abs _).mpr ⟨1, by norm_num, fun n _ ↦ Real.abs_sin_le_one n⟩
  simpa only [div_eq_mul_inv, mul_comm] using
    zero_mul_sequenceBounded (fun n : ℕ ↦ (n : ℝ)⁻¹) (fun n : ℕ ↦ Real.sin n)
      tendsto_inv_atTop_nhds_zero_nat hb

/-- Ví dụ 2.4.22: cos n/2ⁿ→0. -/
theorem cos_div_two_pow_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.cos n / 2 ^ n) atTop (𝓝 0) := by
  have hb : SequenceBounded (fun n : ℕ ↦ Real.cos n) :=
    (sequenceBounded_iff_abs _).mpr ⟨1, by norm_num, fun n _ ↦ Real.abs_cos_le_one n⟩
  have hi : Tendsto (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    zero_mul_sequenceBounded (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) (fun n : ℕ ↦ Real.cos n) hi hb

/-- Mệnh đề 2.4.24(i): mọi cơ số có |α|<1, gồm âm và 0. -/
theorem geometric_tendsto_zero (a : ℝ) (ha : |a| < 1) :
    Tendsto (fun n : ℕ ↦ a ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha

/-- Mệnh đề 2.4.24(ii): căn bậc n của α>0 tiến về 1. -/
theorem constant_nth_root_tendsto_one (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ a ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  simpa only [Real.rpow_zero] using
    (tendsto_const_nhds (x := a)).rpow tendsto_inv_atTop_nhds_zero_nat (Or.inl ha.ne')

/-- Mệnh đề 2.4.24(iii): căn bậc n của n về 1. -/
theorem nat_nth_root_tendsto_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  simpa only [one_div, Function.comp_def] using tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

/-- Bài 2.4.9(c) và 2.4.10(d): n/2^n về 0. -/
theorem nat_div_two_pow_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / 2 ^ n) atTop (𝓝 0) := by
  have hpower : ∀ n : ℕ, 4 ≤ n → (n : ℝ) ^ 2 ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [Nat.cast_add, Nat.cast_one]
      calc
        ((n : ℝ) + 1) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  apply squeeze_zero' ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun n ↦ by positivity
  · refine eventually_atTop.2 ⟨4, ?_⟩
    intro n hn
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)
      (by positivity : (0 : ℝ) < n)).mpr
    simpa only [pow_two, one_mul] using hpower n hn

/-- Bài 2.4.16: căn bậc hai bảo toàn giới hạn của dãy không âm. -/
theorem sqrt_sequence_tendsto (u : ℕ → ℝ) (a : ℝ)
    (_hu_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n ↦ √(u n)) atTop (𝓝 (√a)) :=
  Real.continuous_sqrt.continuousAt.tendsto.comp hu


/-- Ví dụ 2.4.3(a): 1/n dương, ≤1, và dãy bị chặn. -/
theorem reciprocal_sequence_bounds :
    (∀ n : ℕ, 1 ≤ n → 0 < 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1) ∧
    SequenceBounded (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  have hterms : ∀ n : ℕ, 1 ≤ n → 0 < 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · positivity
    · exact (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr (by simpa using hn')
  refine ⟨hterms, ⟨1, fun n hn ↦ (hterms n hn).2⟩, 0, fun n hn ↦ (hterms n hn).1.le⟩

/-- Ví dụ 2.4.3(b): dãy 5−2n² bị chặn trên nhưng không bị chặn dưới. -/
theorem quadratic_sequence_bounds :
    SequenceBoundedAbove (fun n : ℕ ↦ 5 - 2 * (n : ℝ) ^ 2) ∧
    ¬ SequenceBoundedBelow (fun n : ℕ ↦ 5 - 2 * (n : ℝ) ^ 2) := by
  constructor
  · refine ⟨3, ?_⟩
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (|m| + 4)
    have hn1 : 1 ≤ n := by
      have hm0 := abs_nonneg m
      have hn1' : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast hn1'
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hml := neg_abs_le m
    have hbound := hm n hn1
    nlinarith

/-- Ví dụ 2.4.3(c): 3ⁿ có cận dưới 3 và không có cận trên. -/
theorem three_pow_sequence_bounds :
    SequenceBoundedBelow (fun n : ℕ ↦ (3 : ℝ) ^ n) ∧
    ¬ SequenceBoundedAbove (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  constructor
  · refine ⟨3, ?_⟩
    intro n hn
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn
  · rintro ⟨M, hM⟩
    have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually
      (eventually_ge_atTop (M + 1))
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    have hlow := hN (max N 1) (le_max_left N 1)
    have hupp := hM (max N 1) (le_max_right N 1)
    linarith

/-- Ví dụ 2.4.3(d): (−1)ⁿn không bị chặn trên và không bị chặn dưới. -/
theorem alternating_nat_sequence_unbounded :
    ¬ SequenceBoundedAbove (fun n : ℕ ↦ (-1 : ℝ) ^ n * n) ∧
    ¬ SequenceBoundedBelow (fun n : ℕ ↦ (-1 : ℝ) ^ n * n) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (|M| + 1)
    have hkpos : 1 ≤ k := by
      have hk' : (0 : ℝ) < k := lt_trans (by positivity) hk
      exact_mod_cast hk'
    have h := hM (2 * k) (by omega)
    have hMabs := le_abs_self M
    norm_num [pow_mul, Nat.cast_mul] at h
    linarith
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (|m| + 1)
    have h := hm (2 * k + 1) (by omega)
    have hmabs := neg_abs_le m
    norm_num [pow_add, pow_mul, Nat.cast_mul, Nat.cast_add] at h
    linarith

/-- Các hàm chọn chỉ số chẵn, lẻ và bội của 10 tăng ngặt trên miền chỉ số dương. -/
theorem standard_subsequence_indices :
    StrictMonoOn (fun n : ℕ ↦ 2 * n) (Ici 1) ∧
    StrictMonoOn (fun n : ℕ ↦ 2 * n - 1) (Ici 1) ∧
    StrictMonoOn (fun n : ℕ ↦ 10 * n) (Ici 1) := by
  repeat' constructor
  all_goals intro i hi j hj hij; simp only [mem_Ici] at hi hj; dsimp; omega

/-- Trật tự 10,30,20 không thể là chỉ số tăng ngặt của một dãy con. -/
theorem reordered_indices_not_strict (φ : ℕ → ℕ) (h2 : φ 2 = 30) (h3 : φ 3 = 20) :
    ¬ StrictMonoOn φ (Ici 1) := by
  intro h
  have hlt := h (by norm_num : 2 ∈ Ici (1 : ℕ)) (by norm_num : 3 ∈ Ici (1 : ℕ))
    (by norm_num : (2 : ℕ) < 3)
  omega

/-- Các dãy con chẵn và lẻ vẫn giữ giới hạn. -/
theorem tendsto_even_and_odd (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ u (2 * n)) atTop (𝓝 a) ∧
    Tendsto (fun n : ℕ ↦ u (2 * n + 1)) atTop (𝓝 a) := by
  constructor
  · exact hu.comp ((show StrictMono (fun n : ℕ ↦ 2 * n) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)
  · exact hu.comp ((show StrictMono (fun n : ℕ ↦ 2 * n + 1) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)

/-- Mệnh đề 2.4.14: dãy hội tụ khi hai dãy con chẵn/lẻ có cùng giới hạn. -/
theorem tendsto_iff_even_and_odd (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a) ↔
      Tendsto (fun n : ℕ ↦ u (2 * n)) atTop (𝓝 a) ∧
      Tendsto (fun n : ℕ ↦ u (2 * n + 1)) atTop (𝓝 a) := by
  constructor
  · exact tendsto_even_and_odd u a
  · rintro ⟨he, ho⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨Ne, heN⟩ := Metric.tendsto_atTop.mp he ε hε
    obtain ⟨No, hoN⟩ := Metric.tendsto_atTop.mp ho ε hε
    refine ⟨2 * max Ne No + 1, ?_⟩
    intro n hn
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hege : Ne ≤ n / 2 := by omega
    have hoge : No ≤ n / 2 := by omega
    rcases hmod with hm | hm
    · have hidx : 2 * (n / 2) = n := by omega
      simpa only [hidx] using heN (n / 2) hege
    · have hidx : 2 * (n / 2) + 1 = n := by omega
      simpa only [hidx] using hoN (n / 2) hoge

/-- Ví dụ 2.4.11: dãy luân phiên phân kì do hai dãy con hằng ±1. -/
theorem alternating_sequence_divergent :
    ¬ ∃ a : ℝ, Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ n) atTop (𝓝 a) := by
  rintro ⟨a, ha⟩
  obtain ⟨he, ho⟩ := tendsto_even_and_odd _ a ha
  have he1 : Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ (2 * n)) atTop (𝓝 1) := by
    simpa only [pow_mul, neg_one_sq, one_pow] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have ho1 : Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ (2 * n + 1)) atTop (𝓝 (-1)) := by
    simpa only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1)))
  have h1 := tendsto_nhds_unique he1 he
  have h2 := tendsto_nhds_unique ho1 ho
  linarith

/-- Nhận xét 2.4.5: một dãy bị chặn cụ thể vẫn có thể phân kì. -/
theorem bounded_does_not_imply_convergent :
    SequenceBounded (fun n : ℕ ↦ (-1 : ℝ) ^ n) ∧
      ¬ ∃ a : ℝ, Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ n) atTop (𝓝 a) := by
  refine ⟨(sequenceBounded_iff_abs _).mpr ⟨1, by norm_num, ?_⟩, alternating_sequence_divergent⟩
  intro n hn
  simp

/-- Nhận xét 2.4.23: giới hạn khác 0 nhân dãy bị chặn có thể phân kì. -/
theorem nonzero_limit_mul_bounded_counterexample :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) ∧
      SequenceBounded (fun n : ℕ ↦ (-1 : ℝ) ^ n) ∧
      ¬ ∃ a : ℝ, Tendsto (fun n : ℕ ↦ 1 * (-1 : ℝ) ^ n) atTop (𝓝 a) := by
  exact ⟨tendsto_const_nhds, bounded_does_not_imply_convergent.1,
    by simpa using alternating_sequence_divergent⟩


/-- Ví dụ 2.4.12: hai dãy con của sin(nπ/2) hằng 0 và 1. -/
theorem sin_half_pi_subsequence_limits :
    Tendsto (fun k : ℕ ↦ Real.sin ((2 * k : ℕ) * Real.pi / 2)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ ↦ Real.sin ((4 * k + 1 : ℕ) * Real.pi / 2)) atTop (𝓝 1) := by
  have he : ∀ k : ℕ, Real.sin ((2 * k : ℕ) * Real.pi / 2) = 0 := by
    intro k
    have heq : ((2 * k : ℕ) : ℝ) * Real.pi / 2 = (k : ℝ) * Real.pi := by
      push_cast; ring
    rw [heq, Real.sin_nat_mul_pi]
  have ho : ∀ k : ℕ, Real.sin ((4 * k + 1 : ℕ) * Real.pi / 2) = 1 := by
    intro k
    have heq : ((4 * k + 1 : ℕ) : ℝ) * Real.pi / 2 =
        Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [heq, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  exact ⟨tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦ (he k).symm),
    tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦ (ho k).symm)⟩

/-- Ví dụ 2.4.12: không có giới hạn cho sin(nπ/2). -/
theorem sin_half_pi_sequence_divergent :
    ¬ ∃ a : ℝ, Tendsto (fun n : ℕ ↦ Real.sin (n * Real.pi / 2)) atTop (𝓝 a) := by
  rintro ⟨a, ha⟩
  have he := ha.comp ((show StrictMono (fun n : ℕ ↦ 2 * n)
    from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)
  have ho := ha.comp ((show StrictMono (fun n : ℕ ↦ 4 * n + 1)
    from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)
  have h0 := tendsto_nhds_unique sin_half_pi_subsequence_limits.1 he
  have h1 := tendsto_nhds_unique sin_half_pi_subsequence_limits.2 ho
  linarith

/-- Dãy trong ví dụ 2.4.15; tại chỉ số lẻ 2k−1 có giá trị 1/k. -/
noncomputable def interleavedReciprocal (n : ℕ) : ℝ :=
  if n % 2 = 0 then 0 else 1 / (((n + 1) / 2 : ℕ) : ℝ)

/-- Ví dụ 2.4.15: công thức số hạng chẵn và lẻ với k≥1. -/
theorem interleavedReciprocal_terms (k : ℕ) (hk : 1 ≤ k) :
    interleavedReciprocal (2 * k) = 0 ∧ interleavedReciprocal (2 * k - 1) = 1 / (k : ℝ) := by
  have he : (2 * k) % 2 = 0 := by omega
  have ho : (2 * k - 1) % 2 = 1 := by omega
  have hd : (2 * k - 1 + 1) / 2 = k := by omega
  simp [interleavedReciprocal, he, ho, hd]

/-- Ví dụ 2.4.15: dãy xen kẽ hội tụ về 0. -/
theorem interleavedReciprocal_tendsto_zero : Tendsto interleavedReciprocal atTop (𝓝 0) := by
  apply (tendsto_iff_even_and_odd _ _).mpr
  constructor
  · apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n ↦ by
      have he : (2 * n) % 2 = 0 := by omega
      simp [interleavedReciprocal, he]
  · have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp
        ((show StrictMono (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)
    apply hlim.congr'
    exact Eventually.of_forall fun n ↦ by
      have ho : (2 * n + 1) % 2 = 1 := by omega
      have hd : (2 * n + 1 + 1) / 2 = n + 1 := by omega
      simp [interleavedReciprocal, ho, hd]

/-- Bài 2.4.8: giới hạn xét k≥1. -/
theorem sequenceBounded_div_nat_pow_tendsto_zero (u : ℕ → ℝ) (hu : SequenceBounded u)
    (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ u n / (n : ℝ) ^ k) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ ^ k) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : k ≠ 0)] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow k
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    zero_mul_sequenceBounded (fun n : ℕ ↦ (n : ℝ)⁻¹ ^ k) u hi hu

/-- Nhận xét 2.4.18: uₙ<vₙ khi n đủ lớn vẫn cho phép hai dãy có cùng giới hạn. -/
theorem reciprocal_square_lt_reciprocal_same_limit :
    (∀ n : ℕ, 2 ≤ n → 1 / (n : ℝ) ^ 2 < 1 / (n : ℝ)) ∧
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  refine ⟨?_, ?_, tendsto_one_div_atTop_nhds_zero_nat⟩
  · intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < n)).mpr
    nlinarith
  · simpa only [one_div, inv_pow, zero_pow two_ne_zero] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

/-- Bài 2.4.10(a): thương có tử chứa sin tiến về 0. -/
theorem sine_polynomial_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.sin (((n : ℝ) ^ 4 + n + 1) / ((n : ℝ) ^ 2 + 1)) / n)
      atTop (𝓝 0) := by
  have hb : SequenceBounded (fun n : ℕ ↦
      Real.sin (((n : ℝ) ^ 4 + n + 1) / ((n : ℝ) ^ 2 + 1))) :=
    (sequenceBounded_iff_abs _).mpr ⟨1, by norm_num, fun n _ ↦ Real.abs_sin_le_one _⟩
  simpa only [pow_one] using sequenceBounded_div_nat_pow_tendsto_zero _ hb 1 (by norm_num)

/-- Bài 2.4.10(b): n/(n²+1)→0. -/
theorem nat_div_square_add_one_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) ^ 2 + 1)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun n ↦ by positivity
  · refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 2 + 1)
      (by positivity : (0 : ℝ) < n)).mpr
    nlinarith

/-- Bài 2.4.11(a): (3cos n+4sin n)/n→0. -/
theorem trig_combination_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (3 * Real.cos n + 4 * Real.sin n) / n) atTop (𝓝 0) := by
  have hb : SequenceBounded (fun n : ℕ ↦ 3 * Real.cos n + 4 * Real.sin n) := by
    apply (sequenceBounded_iff_abs _).mpr
    refine ⟨7, by norm_num, ?_⟩
    intro n hn
    have hc := Real.abs_cos_le_one (n : ℝ)
    have hs := Real.abs_sin_le_one (n : ℝ)
    calc
      |3 * Real.cos n + 4 * Real.sin n| ≤ |3 * Real.cos n| + |4 * Real.sin n| := abs_add_le _ _
      _ ≤ 7 := by rw [abs_mul, abs_mul]; norm_num; linarith
  simpa only [pow_one] using sequenceBounded_div_nat_pow_tendsto_zero _ hb 1 (by norm_num)

/-- Bài 2.4.9(d): (n²+1)cos n/n³→0. -/
theorem square_add_one_cos_div_cube_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (((n : ℝ) ^ 2 + 1) * Real.cos n) / (n : ℝ) ^ 3) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have h3 : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
    simpa using h1.pow 3
  have hb : SequenceBounded (fun n : ℕ ↦ Real.cos n) :=
    (sequenceBounded_iff_abs _).mpr ⟨1, by norm_num, fun n _ ↦ Real.abs_cos_le_one n⟩
  have hsum : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
    simpa using h1.add h3
  apply (zero_mul_sequenceBounded _ _ hsum hb).congr'
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hn0]


/-- Bài 2.4.17: biểu diễn cận trên bé nhất bằng cận trên và một dãy tiến tới nó. -/
theorem isLUB_iff_exists_sequence_tendsto (A : Set ℝ) (hA : A.Nonempty) (a : ℝ) :
    IsLUB A a ↔ a ∈ upperBounds A ∧
      ∃ u : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → u n ∈ A) ∧ Tendsto u atTop (𝓝 a) := by
  constructor
  · intro ha
    obtain ⟨u, _, _, hu, hmem⟩ := ha.exists_seq_monotone_tendsto hA
    exact ⟨ha.1, u, fun n _ ↦ hmem n, hu⟩
  · rintro ⟨ha, u, hmem, hu⟩
    refine ⟨ha, ?_⟩
    intro b hb
    exact le_of_tendsto hu (eventually_atTop.2 ⟨1, fun n hn ↦ hb (hmem n hn)⟩)

/-- Bài 2.4.18: cận dưới lớn nhất là cận dưới được xấp xỉ bởi một dãy trong tập. -/
theorem isGLB_iff_exists_sequence_tendsto (A : Set ℝ) (hA : A.Nonempty) (a : ℝ) :
    IsGLB A a ↔ a ∈ lowerBounds A ∧
      ∃ u : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → u n ∈ A) ∧ Tendsto u atTop (𝓝 a) := by
  constructor
  · intro ha
    obtain ⟨u, _, _, hu, hmem⟩ := ha.exists_seq_antitone_tendsto hA
    exact ⟨ha.1, u, fun n _ ↦ hmem n, hu⟩
  · rintro ⟨ha, u, hmem, hu⟩
    refine ⟨ha, ?_⟩
    intro b hb
    exact ge_of_tendsto hu (eventually_atTop.2 ⟨1, fun n hn ↦ hb (hmem n hn)⟩)


/-- Định lí 2.4.4. -/
theorem converges_sequenceBounded (u : ℕ → ℝ) (a : ℝ)
    (hu : Section03.ConvergesTo u a) : SequenceBounded u :=
  tendsto_sequenceBounded u a (Section03.convergesTo_iff_tendsto.mp hu)

/-- Định lí 2.4.9. -/
theorem converges_sequenceSubsequence (u v : ℕ → ℝ) (a : ℝ)
    (hu : Section03.ConvergesTo u a) (hv : IsSequenceSubsequence u v) :
    Section03.ConvergesTo v a :=
  Section03.convergesTo_iff_tendsto.mpr
    (tendsto_sequenceSubsequence u v a (Section03.convergesTo_iff_tendsto.mp hu) hv)

/-- Nhận xét 2.4.10. -/
theorem distinct_subsequence_limits_divergent (u v w : ℕ → ℝ) (a b : ℝ)
    (hv : IsSequenceSubsequence u v) (hw : IsSequenceSubsequence u w)
    (hva : Section03.ConvergesTo v a) (hwb : Section03.ConvergesTo w b) (hab : a ≠ b) :
    Section03.IsDivergent u := by
  rintro ⟨c, hc⟩
  exact distinct_subsequence_limits u v w a b hv hw
    (Section03.convergesTo_iff_tendsto.mp hva) (Section03.convergesTo_iff_tendsto.mp hwb) hab
    ⟨c, Section03.convergesTo_iff_tendsto.mp hc⟩

/-- Định lí 2.4.16. -/
theorem limit_le_of_converges (u v : ℕ → ℝ) (a b : ℝ)
    (hu : Section03.ConvergesTo u a) (hv : Section03.ConvergesTo v b)
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n) : a ≤ b :=
  limit_le_of_positive_terms u v a b
    (Section03.convergesTo_iff_tendsto.mp hu) (Section03.convergesTo_iff_tendsto.mp hv) huv

/-- Định lí 2.4.19. -/
theorem squeeze_converges (u v w : ℕ → ℝ) (a : ℝ)
    (hu : Section03.ConvergesTo u a) (hw : Section03.ConvergesTo w a)
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n)
    (hvw : ∀ n : ℕ, 1 ≤ n → v n ≤ w n) : Section03.ConvergesTo v a :=
  Section03.convergesTo_iff_tendsto.mpr
    (squeeze_positive_terms u v w a (Section03.convergesTo_iff_tendsto.mp hu)
      (Section03.convergesTo_iff_tendsto.mp hw) huv hvw)

/-- Định lí 2.4.21. -/
theorem zero_mul_sequenceBounded_converges (u v : ℕ → ℝ)
    (hu : Section03.ConvergesTo u 0) (hv : SequenceBounded v) :
    Section03.ConvergesTo (fun n ↦ u n * v n) 0 :=
  Section03.convergesTo_iff_tendsto.mpr
    (zero_mul_sequenceBounded u v (Section03.convergesTo_iff_tendsto.mp hu) hv)

/-- Hai dãy con chẵn/lẻ hội tụ cùng giới hạn khi và chỉ khi dãy ban đầu hội tụ giới hạn ấy. -/
theorem converges_iff_even_and_odd (u : ℕ → ℝ) (a : ℝ) :
    Section03.ConvergesTo u a ↔
      Section03.ConvergesTo (fun n ↦ u (2 * n)) a ∧
      Section03.ConvergesTo (fun n ↦ u (2 * n + 1)) a := by
  simpa only [Section03.convergesTo_iff_tendsto] using tendsto_iff_even_and_odd u a

/-- Bài 2.4.16. -/
theorem sqrt_sequence_converges (u : ℕ → ℝ) (a : ℝ)
    (hu_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n) (hu : Section03.ConvergesTo u a) :
    Section03.ConvergesTo (fun n ↦ √(u n)) (√a) :=
  Section03.convergesTo_iff_tendsto.mpr
    (sqrt_sequence_tendsto u a hu_nonneg (Section03.convergesTo_iff_tendsto.mp hu))

/-- Bài 2.4.17. -/
theorem isLUB_iff_exists_sequence_convergesTo (A : Set ℝ) (hA : A.Nonempty) (a : ℝ) :
    IsLUB A a ↔ a ∈ upperBounds A ∧
      ∃ u : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → u n ∈ A) ∧ Section03.ConvergesTo u a := by
  simpa only [Section03.convergesTo_iff_tendsto] using isLUB_iff_exists_sequence_tendsto A hA a

/-- Bài 2.4.18. -/
theorem isGLB_iff_exists_sequence_convergesTo (A : Set ℝ) (hA : A.Nonempty) (a : ℝ) :
    IsGLB A a ↔ a ∈ lowerBounds A ∧
      ∃ u : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → u n ∈ A) ∧ Section03.ConvergesTo u a := by
  simpa only [Section03.convergesTo_iff_tendsto] using isGLB_iff_exists_sequence_tendsto A hA a


/-- Lời văn dòng 1205: không bị chặn suy ra không có giới hạn thực hữu hạn. -/
theorem unbounded_divergent (u : ℕ → ℝ) (hu : ¬ SequenceBounded u) :
    Section03.IsDivergent u := by
  rintro ⟨a, ha⟩
  exact hu (tendsto_sequenceBounded u a (Section03.convergesTo_iff_tendsto.mp ha))

/-- Hai ví dụ phân kì sau định lí bị chặn. -/
theorem unbounded_examples_divergent :
    Section03.IsDivergent (fun n : ℕ ↦ (3 : ℝ) ^ n) ∧
    Section03.IsDivergent (fun n : ℕ ↦ (-1 : ℝ) ^ n * n) := by
  constructor
  · exact unbounded_divergent _ (fun h ↦ three_pow_sequence_bounds.2 h.1)
  · exact unbounded_divergent _ (fun h ↦ alternating_nat_sequence_unbounded.1 h.1)

/-- Nhận xét 2.4.7: các ví dụ dãy con. -/
theorem standard_sequenceSubsequences (u : ℕ → ℝ) :
    IsSequenceSubsequence u (fun n ↦ u (2 * n)) ∧
    IsSequenceSubsequence u (fun n ↦ u (2 * n - 1)) ∧
    IsSequenceSubsequence u (fun n ↦ u (10 * n)) := by
  refine ⟨⟨fun n ↦ 2 * n, ?_, standard_subsequence_indices.1, fun _ _ ↦ rfl⟩,
    ⟨fun n ↦ 2 * n - 1, ?_, standard_subsequence_indices.2.1, fun _ _ ↦ rfl⟩,
    ⟨fun n ↦ 10 * n, ?_, standard_subsequence_indices.2.2, fun _ _ ↦ rfl⟩⟩
  all_goals intro n hn; dsimp; omega

/-- Bài 2.4.3: từ a₁=0 và truy hồi suy ra 0≤aₙ≤4 với mọi n≥1. -/
theorem square_root_recurrence_bounded (u : ℕ → ℝ) (hfirst : u 1 = 0)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(4 + 3 * u n)) : SequenceBounded u := by
  have hmem : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 4 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [hfirst]
    | succ n hn ih =>
      rw [hnext n hn]
      exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 4)).mpr
        (by nlinarith [ih.2])⟩
  exact ⟨⟨4, fun n hn ↦ (hmem n hn).2⟩, ⟨0, fun n hn ↦ (hmem n hn).1⟩⟩

/-- Bài 2.4.6(a): dãy con chỉ số lẻ là hằng 0. -/
theorem nat_add_alternating_nat_has_subsequence_converging_zero :
    ∃ v : ℕ → ℝ, IsSequenceSubsequence (fun n : ℕ ↦ n + (-1 : ℝ) ^ (3 * n) * n) v ∧
      Section03.ConvergesTo v 0 := by
  refine ⟨fun _ ↦ 0, ⟨fun n ↦ 2 * n + 1, ?_, ?_, ?_⟩,
    Section03.constant_converges 0⟩
  · intro n hn; dsimp; omega
  · intro i hi j hj hij; dsimp; omega
  · intro n hn
    have heq : 3 * (2 * n + 1) = 2 * (3 * n + 1) + 1 := by omega
    simp [heq, pow_add, pow_mul]

/-- Dòng 1434: phản ví dụ cho cận của tích. -/
theorem zero_mul_printed_interval_counterexample :
    (0 : ℝ) < 1 ∧ |(0 : ℝ)| ≤ 1 ∧
      ¬ (-(1 : ℝ) * (-1) ≤ (-1 : ℝ) * 0 ∧ (-1 : ℝ) * 0 ≤ 1 * (-1)) := by
  norm_num

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S04-theorem-005.proof-sign-interval: từ `|b| ≤ M` suy ra `|a * b| ≤ M * |a|`. -/
theorem absolute_product_interval (a b M : ℝ) (_hM : 0 < M) (hb : |b| ≤ M) :
    -(M * |a|) ≤ a * b ∧ a * b ≤ M * |a| := by
  apply abs_le.mp
  rw [abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg a)

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S04-theorem-005.proof-sign-interval, dòng 1434: cận của tích trong lời giải gốc. -/
theorem source_zero_mul_signed_interval (u v : ℕ → ℝ) (M : ℝ)
    (hu : calculus.Chapter02.Section03.ConvergesTo u 0)
    (hM : 0 < M) (hv : ∀ n : ℕ, 1 ≤ n → |v n| ≤ M) :
    ∀ n : ℕ, 1 ≤ n → -(M * u n) ≤ u n * v n ∧ u n * v n ≤ M * u n := by
  sorry

/-- Bài 2.4.14: ba lớp chỉ số theo môđun 3 có cùng giới hạn khi và chỉ khi cả dãy hội tụ. -/
theorem tendsto_iff_three_residues (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a) ↔
      Tendsto (fun n ↦ u (3 * n)) atTop (𝓝 a) ∧
      Tendsto (fun n ↦ u (3 * n + 1)) atTop (𝓝 a) ∧
      Tendsto (fun n ↦ u (3 * n + 2)) atTop (𝓝 a) := by
  constructor
  · intro hu
    refine ⟨hu.comp ((show StrictMono (fun n : ℕ ↦ 3 * n)
      from fun _ _ h ↦ by dsimp; omega).tendsto_atTop),
      hu.comp ((show StrictMono (fun n : ℕ ↦ 3 * n + 1)
      from fun _ _ h ↦ by dsimp; omega).tendsto_atTop),
      hu.comp ((show StrictMono (fun n : ℕ ↦ 3 * n + 2)
      from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)⟩
  · rintro ⟨h0, h1, h2⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp h0 ε hε
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp h1 ε hε
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp h2 ε hε
    refine ⟨3 * max N0 (max N1 N2) + 2, ?_⟩
    intro n hn
    have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hg0 : N0 ≤ n / 3 := by omega
    have hg1 : N1 ≤ n / 3 := by omega
    have hg2 : N2 ≤ n / 3 := by omega
    rcases hmod with hm | hm | hm
    · have hidx : 3 * (n / 3) = n := by omega
      simpa only [hidx] using hN0 (n / 3) hg0
    · have hidx : 3 * (n / 3) + 1 = n := by omega
      simpa only [hidx] using hN1 (n / 3) hg1
    · have hidx : 3 * (n / 3) + 2 = n := by omega
      simpa only [hidx] using hN2 (n / 3) hg2

/-- Bài 2.4.14. -/
theorem converges_iff_three_residues (u : ℕ → ℝ) (a : ℝ) :
    Section03.ConvergesTo u a ↔
      Section03.ConvergesTo (fun n ↦ u (3 * n)) a ∧
      Section03.ConvergesTo (fun n ↦ u (3 * n + 1)) a ∧
      Section03.ConvergesTo (fun n ↦ u (3 * n + 2)) a := by
  simpa only [Section03.convergesTo_iff_tendsto] using tendsto_iff_three_residues u a


/-- Bài 2.4.10(c): (√(2n)+1)/(n+1)→0. -/
theorem sqrt_two_nat_add_one_div_succ_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (√(2 * (n : ℝ)) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ √(2 / (n : ℝ))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ ↦ 2 / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_inv_atTop_nhds_zero_nat
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hdiv
  have hbound : Tendsto (fun n : ℕ ↦ √(2 / (n : ℝ)) + 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_add] using hsqrt.add tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero' ?_ ?_ hbound
  · exact Eventually.of_forall fun n ↦ by positivity
  · refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hratio : √(2 * (n : ℝ)) / n = √(2 / (n : ℝ)) := by
      have hdiv : √((2 * (n : ℝ)) / (n : ℝ) ^ 2) = √(2 * (n : ℝ)) / n := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      rw [← hdiv]
      congr 1
      field_simp [hn0]
    calc
      (√(2 * (n : ℝ)) + 1) / ((n : ℝ) + 1) ≤ (√(2 * (n : ℝ)) + 1) / n :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = √(2 / (n : ℝ)) + 1 / (n : ℝ) := by rw [add_div, hratio]

/-- Bài 2.4.15: dãy con bình phương buộc hai giới hạn chẵn/lẻ phải bằng nhau. -/
theorem tendsto_of_even_odd_square (u : ℕ → ℝ) (a b c : ℝ)
    (he : Tendsto (fun n ↦ u (2 * n)) atTop (𝓝 a))
    (ho : Tendsto (fun n ↦ u (2 * n + 1)) atTop (𝓝 b))
    (hs : Tendsto (fun n ↦ u (n ^ 2)) atTop (𝓝 c)) : Tendsto u atTop (𝓝 a) := by
  have hsqr : StrictMono (fun n : ℕ ↦ n ^ 2) := Nat.pow_left_strictMono two_ne_zero
  have hphiE : StrictMono (fun n : ℕ ↦ 2 * n ^ 2) := by
    intro i j hij
    have hsq := hsqr hij
    dsimp at hsq ⊢
    omega
  have hphiO : StrictMono (fun n : ℕ ↦ 2 * n ^ 2 + 2 * n) := by
    intro i j hij
    have hsq := hsqr hij
    dsimp at hsq ⊢
    omega
  have hidxE : StrictMono (fun n : ℕ ↦ 2 * n) := fun _ _ h ↦ by dsimp; omega
  have hidxO : StrictMono (fun n : ℕ ↦ 2 * n + 1) := fun _ _ h ↦ by dsimp; omega
  have heSq : Tendsto (fun n : ℕ ↦ u ((2 * n) ^ 2)) atTop (𝓝 a) := by
    apply (he.comp hphiE.tendsto_atTop).congr'
    exact Eventually.of_forall fun n ↦ by dsimp; congr 1; ring
  have hoSq : Tendsto (fun n : ℕ ↦ u ((2 * n + 1) ^ 2)) atTop (𝓝 b) := by
    apply (ho.comp hphiO.tendsto_atTop).congr'
    exact Eventually.of_forall fun n ↦ by dsimp; congr 1; ring
  have hac : a = c := tendsto_nhds_unique heSq (hs.comp hidxE.tendsto_atTop)
  have hbc : b = c := tendsto_nhds_unique hoSq (hs.comp hidxO.tendsto_atTop)
  have hba : b = a := hbc.trans hac.symm
  exact (tendsto_iff_even_and_odd u a).mpr ⟨he, by simpa only [hba] using ho⟩

/-- Bài 2.4.15: các giới hạn chẵn, lẻ và bình phương phải bằng nhau. -/
theorem convergent_of_even_odd_square (u : ℕ → ℝ)
    (he : Section03.IsConvergent (fun n ↦ u (2 * n)))
    (ho : Section03.IsConvergent (fun n ↦ u (2 * n + 1)))
    (hs : Section03.IsConvergent (fun n ↦ u (n ^ 2))) : Section03.IsConvergent u := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := ho
  obtain ⟨c, hc⟩ := hs
  exact ⟨a, Section03.convergesTo_iff_tendsto.mpr
    (tendsto_of_even_odd_square u a b c (Section03.convergesTo_iff_tendsto.mp ha)
      (Section03.convergesTo_iff_tendsto.mp hb) (Section03.convergesTo_iff_tendsto.mp hc))⟩



theorem sequenceBounded_sequenceSubsequence (u v : ℕ → ℝ) (hu : SequenceBounded u)
    (hv : IsSequenceSubsequence u v) : SequenceBounded v := by
  obtain ⟨⟨M, hM⟩, ⟨m, hm⟩⟩ := hu
  obtain ⟨φ, hpos, _, hterms⟩ := hv
  exact ⟨⟨M, fun n hn ↦ by rw [hterms n hn]; exact hM _ (hpos n hn)⟩,
    ⟨m, fun n hn ↦ by rw [hterms n hn]; exact hm _ (hpos n hn)⟩⟩

/-- Bài 2.4.1: nghịch đảo ở chỉ số chẵn, bình phương ở chỉ số lẻ. -/
noncomputable def reciprocalEvenSquareOdd (n : ℕ) : ℝ :=
  if n % 2 = 0 then 1 / (n : ℝ) else (n : ℝ) ^ 2

/-- Bài 2.4.1(b): dãy con chẵn bị chặn bởi 0 và 1. -/
theorem reciprocalEvenSquareOdd_even_bounded :
    IsSequenceSubsequence reciprocalEvenSquareOdd (fun n ↦ reciprocalEvenSquareOdd (2 * n)) ∧
      SequenceBounded (fun n ↦ reciprocalEvenSquareOdd (2 * n)) := by
  refine ⟨(standard_sequenceSubsequences _).1, ⟨⟨1, ?_⟩, ⟨0, ?_⟩⟩⟩
  · intro n hn
    have he : (2 * n) % 2 = 0 := by omega
    have hden : (1 : ℝ) ≤ (2 * n : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
    simp only [reciprocalEvenSquareOdd, he, ite_true]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * n : ℕ))).mpr (by simpa using hden)
  · intro n hn
    have he : (2 * n) % 2 = 0 := by omega
    simp only [reciprocalEvenSquareOdd, he, ite_true]
    positivity

/-- Bài 2.4.1(c): hai dãy con chỉ số 2n+1 và 4n+1 đều không bị chặn trên. -/
theorem reciprocalEvenSquareOdd_odd_unbounded :
    ¬ SequenceBoundedAbove (fun n ↦ reciprocalEvenSquareOdd (2 * n + 1)) ∧
    ¬ SequenceBoundedAbove (fun n ↦ reciprocalEvenSquareOdd (4 * n + 1)) := by
  constructor
  all_goals
    rintro ⟨M, hM⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (|M| + 1)
    have hk1 : 1 ≤ k := by
      have hk' : (1 : ℝ) < k := lt_of_le_of_lt (by linarith [abs_nonneg M]) hk
      exact_mod_cast hk'.le
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hMabs := le_abs_self M
    have h := hM k hk1
  · have ho : (2 * k + 1) % 2 = 1 := by omega
    norm_num [reciprocalEvenSquareOdd, ho, Nat.cast_add, Nat.cast_mul] at h
    nlinarith
  · have ho : (4 * k + 1) % 2 = 1 := by omega
    norm_num [reciprocalEvenSquareOdd, ho, Nat.cast_add, Nat.cast_mul] at h
    nlinarith

/-- Bài 2.4.1(c): hai dãy con phân biệt, đều không bị chặn trên. -/
theorem reciprocalEvenSquareOdd_two_unbounded_subsequences :
    IsSequenceSubsequence reciprocalEvenSquareOdd (fun n ↦ reciprocalEvenSquareOdd (2 * n + 1)) ∧
    IsSequenceSubsequence reciprocalEvenSquareOdd (fun n ↦ reciprocalEvenSquareOdd (4 * n + 1)) ∧
    ¬ SequenceBounded (fun n ↦ reciprocalEvenSquareOdd (2 * n + 1)) ∧
    ¬ SequenceBounded (fun n ↦ reciprocalEvenSquareOdd (4 * n + 1)) ∧
    (fun n ↦ reciprocalEvenSquareOdd (2 * n + 1)) ≠
      (fun n ↦ reciprocalEvenSquareOdd (4 * n + 1)) := by
  refine ⟨⟨fun n ↦ 2 * n + 1, ?_, ?_, fun _ _ ↦ rfl⟩,
    ⟨fun n ↦ 4 * n + 1, ?_, ?_, fun _ _ ↦ rfl⟩,
    (fun h ↦ reciprocalEvenSquareOdd_odd_unbounded.1 h.1),
    (fun h ↦ reciprocalEvenSquareOdd_odd_unbounded.2 h.1), ?_⟩
  · intro n hn; dsimp; omega
  · intro i hi j hj hij; dsimp; omega
  · intro n hn; dsimp; omega
  · intro i hi j hj hij; dsimp; omega
  · intro h
    have h1 := congrFun h 1
    norm_num [reciprocalEvenSquareOdd] at h1

/-- Bài 2.4.1(a): dãy không bị chặn. -/
theorem reciprocalEvenSquareOdd_unbounded : ¬ SequenceBounded reciprocalEvenSquareOdd := by
  intro h
  exact reciprocalEvenSquareOdd_two_unbounded_subsequences.2.2.1
    (sequenceBounded_sequenceSubsequence _ _ h
      reciprocalEvenSquareOdd_two_unbounded_subsequences.1)


/-- Bài 2.4.5: n²≥1 và chỉ số bình phương tăng ngặt. -/
theorem square_sequenceSubsequence (u : ℕ → ℝ) :
    IsSequenceSubsequence u (fun n ↦ u (n ^ 2)) := by
  refine ⟨fun n ↦ n ^ 2, ?_, (Nat.pow_left_strictMono two_ne_zero).strictMonoOn (Ici 1), fun _ _ ↦ rfl⟩
  intro n hn
  simpa using Nat.pow_le_pow_left hn 2

/-- Bài 2.4.5: n²−n=0 tại n=1, ngoài miền chỉ số dương. -/
theorem pronic_indices_not_positive :
    (1 : ℕ) ^ 2 - 1 = 0 ∧ ¬ (∀ n : ℕ, 1 ≤ n → 1 ≤ n ^ 2 - n) := by
  constructor
  · norm_num
  · intro h
    have h1 := h 1 le_rfl
    norm_num at h1

end calculus.Chapter02.Section04
