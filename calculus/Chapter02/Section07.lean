import calculus.Chapter02.Section06
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 2.7. Dãy có giới hạn vô cùng

Nguồn: `source/Ch2_dayso.tex`, dòng 2212–2519; mã C02-S08.
-/

namespace calculus.Chapter02.Section07

open Filter Set
open scoped Topology

noncomputable section

/-- Định nghĩa 2.7.1: với mọi ngưỡng thực M, từ một chỉ số nào đó luôn có aₙ>M. -/
def SequenceTendsToPosInfinity (u : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → M < u n

/-- Định nghĩa 2.7.1: với mọi ngưỡng thực M, từ một chỉ số nào đó luôn có aₙ<M. -/
def SequenceTendsToNegInfinity (u : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → u n < M

/-- Giới hạn +∞ theo bất đẳng thức ngặt tương đương `Tendsto` tại `atTop`. -/
theorem sequenceTendsToPosInfinity_iff_tendsto (u : ℕ → ℝ) :
    SequenceTendsToPosInfinity u ↔ Tendsto u atTop atTop := by
  constructor
  · intro h
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, _, hN⟩ := h M
    exact eventually_atTop.2 ⟨N, fun n hn ↦ (hN n hn).le⟩
  · intro h M
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually_ge_atTop (M + 1))
    refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
    have := hN n (le_trans (le_max_left _ _) hn)
    linarith

/-- Giới hạn −∞ theo bất đẳng thức ngặt tương đương `Tendsto` tại `atBot`. -/
theorem sequenceTendsToNegInfinity_iff_tendsto (u : ℕ → ℝ) :
    SequenceTendsToNegInfinity u ↔ Tendsto u atTop atBot := by
  constructor
  · intro h
    apply tendsto_atBot.2
    intro M
    obtain ⟨N, _, hN⟩ := h M
    exact eventually_atTop.2 ⟨N, fun n hn ↦ (hN n hn).le⟩
  · intro h M
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually_le_atBot (M - 1))
    refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
    have := hN n (le_trans (le_max_left _ _) hn)
    linarith

/-- Nhận xét 2.7.4(ii): chỉ cần xét các ngưỡng dương cho +∞. -/
theorem sequenceTendsToPosInfinity_iff_positive_threshold (u : ℕ → ℝ) :
    SequenceTendsToPosInfinity u ↔
      ∀ M > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → M < u n := by
  constructor
  · exact fun h M _ ↦ h M
  · intro h M
    obtain ⟨N, hN, hbound⟩ := h (max M 0 + 1) (by positivity)
    refine ⟨N, hN, fun n hn ↦ ?_⟩
    have := hbound n hn
    have := le_max_left M 0
    linarith

/-- Nhận xét 2.7.4(ii): chỉ cần xét các ngưỡng âm cho −∞. -/
theorem sequenceTendsToNegInfinity_iff_negative_threshold (u : ℕ → ℝ) :
    SequenceTendsToNegInfinity u ↔
      ∀ M < 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → u n < M := by
  constructor
  · exact fun h M _ ↦ h M
  · intro h M
    obtain ⟨N, hN, hbound⟩ := h (min M 0 - 1) (by have := min_le_right M 0; linarith)
    refine ⟨N, hN, fun n hn ↦ ?_⟩
    have := hbound n hn
    have := min_le_left M 0
    linarith

/-- Nhận xét 2.7.4(iii): đổi dấu từ +∞ sang −∞. -/
theorem neg_tendsToNegInfinity_of_tendsToPosInfinity {u : ℕ → ℝ} (hu : SequenceTendsToPosInfinity u) :
    SequenceTendsToNegInfinity (fun n ↦ -u n) := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (-M)
  exact ⟨N, hN, fun n hn ↦ by have := hbound n hn; linarith⟩

/-- Nhận xét 2.7.4(iii): đổi dấu từ −∞ sang +∞. -/
theorem neg_tendsToPosInfinity_of_tendsToNegInfinity {u : ℕ → ℝ} (hu : SequenceTendsToNegInfinity u) :
    SequenceTendsToPosInfinity (fun n ↦ -u n) := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (-M)
  exact ⟨N, hN, fun n hn ↦ by have := hbound n hn; linarith⟩

/-- Định lí 2.7.9(i): dãy lớn hơn dãy tiến về +∞ cũng tiến về +∞. -/
theorem tendsToPosInfinity_of_le {u v : ℕ → ℝ}
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n) (hu : SequenceTendsToPosInfinity u) :
    SequenceTendsToPosInfinity v := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hu M
  exact ⟨N, hN, fun n hn ↦ (hbound n hn).trans_le (huv n (hN.trans hn))⟩

/-- Định lí 2.7.9(ii): so sánh dưới cho −∞. -/
theorem tendsToNegInfinity_of_le {u v : ℕ → ℝ}
    (huv : ∀ n : ℕ, 1 ≤ n → u n ≤ v n) (hv : SequenceTendsToNegInfinity v) :
    SequenceTendsToNegInfinity u := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hv M
  exact ⟨N, hN, fun n hn ↦ (huv n (hN.trans hn)).trans_lt (hbound n hn)⟩

/-- Nhận xét 2.7.4(iv): +∞ kéo theo giá trị tuyệt đối →+∞. -/
theorem abs_tendsToPosInfinity {u : ℕ → ℝ} (hu : SequenceTendsToPosInfinity u) :
    SequenceTendsToPosInfinity (fun n ↦ |u n|) :=
  tendsToPosInfinity_of_le (fun n _ ↦ le_abs_self (u n)) hu

/-- Nhận xét 2.7.4(iv): −∞ kéo theo giá trị tuyệt đối →+∞. -/
theorem abs_tendsToPosInfinity_of_tendsToNegInfinity {u : ℕ → ℝ} (hu : SequenceTendsToNegInfinity u) :
    SequenceTendsToPosInfinity (fun n ↦ |u n|) :=
  tendsToPosInfinity_of_le (fun n _ ↦ neg_le_abs (u n)) (neg_tendsToPosInfinity_of_tendsToNegInfinity hu)

/-- Ví dụ 2.7.2: n tiến về +∞. -/
theorem nat_tendsToPosInfinity : SequenceTendsToPosInfinity (fun n : ℕ ↦ (n : ℝ)) := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  exact hN.trans_le (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))

/-- Ví dụ 2.7.3: mẫu 2n dương tại n≥1. -/
theorem negative_quadratic_denominator_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < 2 * (n : ℝ) := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Ví dụ 2.7.3: (1−n²)/(2n) tiến về −∞. -/
theorem negative_quadratic_tendsToNegInfinity :
    SequenceTendsToNegInfinity (fun n : ℕ ↦ (1 - (n : ℝ) ^ 2) / (2 * n)) := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (1 - M))
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnrN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 1).trans hn
  have hden := negative_quadratic_denominator_pos n hn1
  apply (div_lt_iff₀ hden).mpr
  nlinarith

/-- Định lí 2.7.8(i), phần tổng. -/
theorem add_tendsToPosInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : SequenceTendsToPosInfinity v) :
    SequenceTendsToPosInfinity (fun n ↦ u n + v n) := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (M / 2)
  obtain ⟨K, _, hbound'⟩ := hv (M / 2)
  refine ⟨max N K, hN.trans (le_max_left _ _), fun n hn ↦ ?_⟩
  have := hbound n ((le_max_left _ _).trans hn)
  have := hbound' n ((le_max_right _ _).trans hn)
  linarith

/-- Định lí 2.7.8(i): tích hai dãy tiến về +∞; các thừa số dương khi chỉ số đủ lớn. -/
theorem mul_tendsToPosInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : SequenceTendsToPosInfinity v) :
    SequenceTendsToPosInfinity (fun n ↦ u n * v n) := by
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (max M 1)
  obtain ⟨K, _, hbound'⟩ := hv 1
  refine ⟨max N K, hN.trans (le_max_left _ _), fun n hn ↦ ?_⟩
  have ha := hbound n ((le_max_left _ _).trans hn)
  have hb := hbound' n ((le_max_right _ _).trans hn)
  have ha0 : 0 < u n := lt_trans (by positivity : 0 < max M 1) ha
  calc
    M ≤ max M 1 := le_max_left _ _
    _ < u n := ha
    _ = u n * 1 := (mul_one _).symm
    _ < u n * v n := mul_lt_mul_of_pos_left hb ha0

/-- Định lí 2.7.8(ii), phần tổng. -/
theorem add_tendsToNegInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToNegInfinity u) (hv : SequenceTendsToNegInfinity v) :
    SequenceTendsToNegInfinity (fun n ↦ u n + v n) := by
  have := neg_tendsToNegInfinity_of_tendsToPosInfinity (add_tendsToPosInfinity (neg_tendsToPosInfinity_of_tendsToNegInfinity hu) (neg_tendsToPosInfinity_of_tendsToNegInfinity hv))
  simpa only [neg_add, neg_neg] using this

/-- Định lí 2.7.8(ii), tích hai dãy về −∞. -/
theorem mul_tendsToPosInfinity_of_both_tendsToNegInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToNegInfinity u) (hv : SequenceTendsToNegInfinity v) :
    SequenceTendsToPosInfinity (fun n ↦ u n * v n) := by
  simpa only [neg_mul_neg] using mul_tendsToPosInfinity (neg_tendsToPosInfinity_of_tendsToNegInfinity hu) (neg_tendsToPosInfinity_of_tendsToNegInfinity hv)

/-- Định lí 2.7.8(iii), hiệu +∞−(−∞). -/
theorem sub_tendsToPosInfinity_of_pos_neg_infinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : SequenceTendsToNegInfinity v) :
    SequenceTendsToPosInfinity (fun n ↦ u n - v n) := by
  simpa only [sub_eq_add_neg] using add_tendsToPosInfinity hu (neg_tendsToPosInfinity_of_tendsToNegInfinity hv)

/-- Định lí 2.7.8(iii), tích +∞ và −∞. -/
theorem mul_tendsToNegInfinity_of_pos_neg_infinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : SequenceTendsToNegInfinity v) :
    SequenceTendsToNegInfinity (fun n ↦ u n * v n) := by
  have := neg_tendsToNegInfinity_of_tendsToPosInfinity (mul_tendsToPosInfinity hu (neg_tendsToPosInfinity_of_tendsToNegInfinity hv))
  simpa only [mul_neg, neg_neg] using this

/-- Định lí 2.7.5(i): nghịch đảo dãy tiến về ±∞ hội tụ về 0, với aₙ≠0. -/
theorem reciprocal_converges_zero {u : ℕ → ℝ}
    (hnz : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hu : SequenceTendsToPosInfinity (fun n ↦ |u n|)) :
    Section03.ConvergesTo (fun n ↦ 1 / u n) 0 := by
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hu (1 / ε)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have hpos : 0 < |u n| := abs_pos.mpr (hnz n (hN.trans hn))
  simpa only [sub_zero, abs_div, abs_one] using (one_div_lt hpos hε).mpr (hbound n hn)

/-- Định lí 2.7.5(ii): uₙ≠0 và uₙ→0 suy ra 1/|uₙ|→+∞. -/
theorem reciprocal_abs_tendsToPosInfinity {u : ℕ → ℝ}
    (hnz : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hu : Section03.ConvergesTo u 0) :
    SequenceTendsToPosInfinity (fun n ↦ 1 / |u n|) := by
  intro M
  have hε : 0 < 1 / (|M| + 1) := by positivity
  obtain ⟨N, hN, hbound⟩ := hu (1 / (|M| + 1)) hε
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have hb := hbound n hn
  rw [sub_zero] at hb
  have hpos : 0 < |u n| := abs_pos.mpr (hnz n (hN.trans hn))
  have hh := (lt_one_div (by positivity : 0 < |M| + 1) hpos).mpr hb
  have := le_abs_self M
  linarith

/-- Định lí 2.7.6(i): dãy tăng không bị chặn trên tiến về +∞. -/
theorem increasing_unbounded_tendsToPosInfinity {u : ℕ → ℝ}
    (hu : Section06.SequenceIncreasing u) (hb : ¬ Section04.SequenceBoundedAbove u) :
    SequenceTendsToPosInfinity u := by
  have hmono := (Section06.sequenceIncreasing_iff_monotoneOn u).mp hu
  have hunb : ∀ M : ℝ, ∃ N : ℕ, 1 ≤ N ∧ M < u N := by
    intro M
    by_contra h
    push Not at h
    exact hb ⟨M, fun n hn ↦ h n hn⟩
  intro M
  obtain ⟨N, hN, hbound⟩ := hunb M
  exact ⟨N, hN, fun n hn ↦ hbound.trans_le (hmono hN (hN.trans hn) hn)⟩

/-- Định lí 2.7.6(ii): dãy giảm không bị chặn dưới tiến về −∞. -/
theorem decreasing_unbounded_tendsToNegInfinity {u : ℕ → ℝ}
    (hu : Section06.SequenceDecreasing u) (hb : ¬ Section04.SequenceBoundedBelow u) :
    SequenceTendsToNegInfinity u := by
  have hmono := (Section06.sequenceDecreasing_iff_antitoneOn u).mp hu
  have hunb : ∀ M : ℝ, ∃ N : ℕ, 1 ≤ N ∧ u N < M := by
    intro M
    by_contra h
    push Not at h
    exact hb ⟨M, fun n hn ↦ h n hn⟩
  intro M
  obtain ⟨N, hN, hbound⟩ := hunb M
  exact ⟨N, hN, fun n hn ↦ (hmono hN (hN.trans hn) hn).trans_lt hbound⟩

/-- Mệnh đề 2.7.7(i): dãy con giữ giới hạn +∞. -/
theorem subsequence_tendsToPosInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : Section04.IsSequenceSubsequence u v) :
    SequenceTendsToPosInfinity v := by
  obtain ⟨φ, hpos, hmono, heq⟩ := hv
  apply (sequenceTendsToPosInfinity_iff_tendsto v).mpr
  exact ((sequenceTendsToPosInfinity_iff_tendsto u).mp hu |>.comp
    (Section04.subsequence_index_tendsto φ hpos hmono)).congr'
      (eventually_atTop.2 ⟨1, fun k hk ↦ (heq k hk).symm⟩)

/-- Mệnh đề 2.7.7(ii): dãy con giữ giới hạn −∞. -/
theorem subsequence_tendsToNegInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToNegInfinity u) (hv : Section04.IsSequenceSubsequence u v) :
    SequenceTendsToNegInfinity v := by
  obtain ⟨φ, hpos, hmono, heq⟩ := hv
  apply (sequenceTendsToNegInfinity_iff_tendsto v).mpr
  exact ((sequenceTendsToNegInfinity_iff_tendsto u).mp hu |>.comp
    (Section04.subsequence_index_tendsto φ hpos hmono)).congr'
      (eventually_atTop.2 ⟨1, fun k hk ↦ (heq k hk).symm⟩)

/-- Định lí 2.7.12(i): cộng dãy bị chặn dưới. -/
theorem add_bddBelow_tendsToPosInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : Section04.SequenceBoundedBelow v) :
    SequenceTendsToPosInfinity (fun n ↦ u n + v n) := by
  obtain ⟨B, hB⟩ := hv
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (M - B)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have := hbound n hn
  have := hB n (hN.trans hn)
  linarith

/-- Định lí 2.7.12(ii): nhân dãy tiến về +∞ với dãy có cận dưới dương. -/
theorem mul_pos_lower_bound_tendsToPosInfinity {u v : ℕ → ℝ} {B : ℝ}
    (hu : SequenceTendsToPosInfinity u) (hB : 0 < B)
    (hv : ∀ n : ℕ, 1 ≤ n → B ≤ v n) :
    SequenceTendsToPosInfinity (fun n ↦ u n * v n) := by
  apply (sequenceTendsToPosInfinity_iff_positive_threshold _).mpr
  intro M hM
  obtain ⟨N, hN, hbound⟩ := hu (M / B)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have ha := hbound n hn
  have hb := hv n (hN.trans hn)
  have ha0 : 0 < u n := (div_pos hM hB).trans ha
  calc
    M < u n * B := (div_lt_iff₀ hB).mp ha
    _ ≤ u n * v n := mul_le_mul_of_nonneg_left hb ha0.le

/-- Định lí 2.7.12(iii): cộng dãy bị chặn trên vào dãy về −∞. -/
theorem add_bddAbove_tendsToNegInfinity {u v : ℕ → ℝ}
    (hu : SequenceTendsToNegInfinity u) (hv : Section04.SequenceBoundedAbove v) :
    SequenceTendsToNegInfinity (fun n ↦ u n + v n) := by
  obtain ⟨B, hB⟩ := hv
  intro M
  obtain ⟨N, hN, hbound⟩ := hu (M - B)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have := hbound n hn
  have := hB n (hN.trans hn)
  linarith

/-- Định lí 2.7.12(iv): nhân dãy tiến về −∞ với dãy có cận dưới dương. -/
theorem mul_pos_lower_bound_tendsToNegInfinity {u v : ℕ → ℝ} {B : ℝ}
    (hu : SequenceTendsToNegInfinity u) (hB : 0 < B)
    (hv : ∀ n : ℕ, 1 ≤ n → B ≤ v n) :
    SequenceTendsToNegInfinity (fun n ↦ u n * v n) := by
  have := neg_tendsToNegInfinity_of_tendsToPosInfinity (mul_pos_lower_bound_tendsToPosInfinity (neg_tendsToPosInfinity_of_tendsToNegInfinity hu) hB hv)
  simpa only [neg_mul, neg_neg] using this

/-- Hệ quả 2.7.14(i): cộng dãy hội tụ không thay đổi giới hạn vô cùng. -/
theorem add_convergent_tendsToPosInfinity {u v : ℕ → ℝ} {b : ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : Section03.ConvergesTo v b) :
    SequenceTendsToPosInfinity (fun n ↦ u n + v n) :=
  add_bddBelow_tendsToPosInfinity hu (Section04.tendsto_sequenceBounded v b
    (Section03.convergesTo_iff_tendsto.mp hv)).2

/-- Hệ quả 2.7.14(ii): nhân dãy tiến về +∞ với dãy hội tụ về b>0. -/
theorem mul_convergent_pos_tendsToPosInfinity {u v : ℕ → ℝ} {b : ℝ}
    (hu : SequenceTendsToPosInfinity u) (hv : Section03.ConvergesTo v b) (hb : 0 < b) :
    SequenceTendsToPosInfinity (fun n ↦ u n * v n) := by
  apply (sequenceTendsToPosInfinity_iff_tendsto _).mpr
  exact ((sequenceTendsToPosInfinity_iff_tendsto u).mp hu).atTop_mul_pos hb
    (Section03.convergesTo_iff_tendsto.mp hv)

/-- Hệ quả 2.7.14(ii): trường hợp hằng số α>0. -/
theorem const_mul_tendsToPosInfinity {u : ℕ → ℝ} {a : ℝ}
    (hu : SequenceTendsToPosInfinity u) (ha : 0 < a) :
    SequenceTendsToPosInfinity (fun n ↦ a * u n) := by
  apply (sequenceTendsToPosInfinity_iff_tendsto _).mpr
  exact ((sequenceTendsToPosInfinity_iff_tendsto u).mp hu).const_mul_atTop ha

/-- Hệ quả 2.7.14(iii): nhân dãy về −∞ với dãy hội tụ giới hạn dương. -/
theorem mul_convergent_pos_tendsToNegInfinity {u v : ℕ → ℝ} {b : ℝ}
    (hu : SequenceTendsToNegInfinity u) (hv : Section03.ConvergesTo v b) (hb : 0 < b) :
    SequenceTendsToNegInfinity (fun n ↦ u n * v n) := by
  have := neg_tendsToNegInfinity_of_tendsToPosInfinity (mul_convergent_pos_tendsToPosInfinity (neg_tendsToPosInfinity_of_tendsToNegInfinity hu) hv hb)
  simpa only [neg_mul, neg_neg] using this

/-- Hệ quả 2.7.14(iii): hằng α>0 và dãy về −∞. -/
theorem const_mul_tendsToNegInfinity {u : ℕ → ℝ} {a : ℝ}
    (hu : SequenceTendsToNegInfinity u) (ha : 0 < a) :
    SequenceTendsToNegInfinity (fun n ↦ a * u n) := by
  have := neg_tendsToNegInfinity_of_tendsToPosInfinity (const_mul_tendsToPosInfinity (neg_tendsToPosInfinity_of_tendsToNegInfinity hu) ha)
  simpa only [mul_neg, neg_neg] using this

/-- Hệ quả 2.7.14(iv): nếu |uₙ|→+∞ và uₙ≠0, thì vₙ/uₙ→0 với v bị chặn. -/
theorem bounded_div_converges_zero {u v : ℕ → ℝ}
    (hnz : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hu : SequenceTendsToPosInfinity (fun n ↦ |u n|)) (hv : Section04.SequenceBounded v) :
    Section03.ConvergesTo (fun n ↦ v n / u n) 0 := by
  have hi := reciprocal_converges_zero hnz hu
  apply Section03.convergesTo_iff_tendsto.mpr
  have hm := Section04.zero_mul_sequenceBounded
    (fun n ↦ 1 / u n) v (Section03.convergesTo_iff_tendsto.mp hi) hv
  simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one, one_mul] using hm


theorem positive_cast {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < n := by
  exact_mod_cast (by omega : 0 < n)

/-- Mệnh đề 2.7.11(i), Bài 2(b): aⁿ→+∞ với a>1. -/
theorem geometric_tendsToPosInfinity (a : ℝ) (ha : 1 < a) :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ a ^ n) := by
  intro M
  have ha0 : 0 < a - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((M - 1) / (a - 1))
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 1).trans hn
  have hlinear : M < 1 + (n : ℝ) * (a - 1) := by
    have hh := (div_lt_iff₀ ha0).mp (hN.trans_le hnr)
    linarith
  exact hlinear.trans_le (one_add_mul_sub_le_pow (by linarith : -1 ≤ a) n)

/-- Bài 2(a): nᵏ→+∞ với k≥1. -/
theorem nat_power_tendsToPosInfinity (k : ℕ) (hk : 1 ≤ k) :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ (n : ℝ) ^ k) := by
  apply tendsToPosInfinity_of_le (fun n hn ↦ ?_) nat_tendsToPosInfinity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa using (pow_le_pow_right₀ hnR hk : (n : ℝ) ^ 1 ≤ (n : ℝ) ^ k)

/-- Mệnh đề 2.7.11(ii): aⁿ/nᵐ→+∞ với a>1, kể cả m=0. -/
theorem geometric_div_power_tendsToPosInfinity (a : ℝ) (ha : 1 < a) (m : ℕ) :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ a ^ n / (n : ℝ) ^ m) := by
  have hconv : Section03.ConvergesTo (fun n : ℕ ↦ (n : ℝ) ^ m / a ^ n) 0 :=
    Section03.convergesTo_iff_tendsto.mpr (tendsto_pow_const_div_const_pow_of_one_lt m ha)
  have hnz : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ m / a ^ n ≠ 0 := by
    intro n hn
    exact (div_pos (pow_pos (positive_cast hn) m) (pow_pos (by linarith : 0 < a) n)).ne'
  have hh := reciprocal_abs_tendsToPosInfinity hnz hconv
  intro M
  obtain ⟨N, hN, hbound⟩ := hh M
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have hp := div_pos (pow_pos (positive_cast (hN.trans hn)) m)
    (pow_pos (by linarith : 0 < a) n)
  simpa only [abs_of_pos hp, one_div_div] using hbound n hn

/-- Bài 2(c): log n tiến về +∞. -/
theorem log_nat_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ Real.log n) := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp M)
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  have hh : Real.exp M < n := hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hn)
  exact (Real.lt_log_iff_exp_lt (positive_cast ((le_max_right N 1).trans hn))).mpr hh

/-- Ví dụ 15(a). -/
theorem sin_add_nat_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ Real.sin n + n) := by
  have := add_bddBelow_tendsToPosInfinity nat_tendsToPosInfinity
    (show Section04.SequenceBoundedBelow (fun n : ℕ ↦ Real.sin n) from
      ⟨-1, fun n _ ↦ Real.neg_one_le_sin n⟩)
  simpa only [add_comm] using this

/-- Ví dụ 15(b). -/
theorem sin_sub_nat_tendsToNegInfinity :
    SequenceTendsToNegInfinity (fun n : ℕ ↦ Real.sin n - n) := by
  have := add_bddAbove_tendsToNegInfinity (neg_tendsToNegInfinity_of_tendsToPosInfinity nat_tendsToPosInfinity)
    (show Section04.SequenceBoundedAbove (fun n : ℕ ↦ Real.sin n) from
      ⟨1, fun n _ ↦ Real.sin_le_one n⟩)
  simpa only [add_comm, sub_eq_add_neg] using this

/-- Ví dụ 15(c): 2n³+n²+2025→+∞. -/
theorem cubic_polynomial_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ 2 * (n : ℝ) ^ 3 + (n : ℝ) ^ 2 + 2025) := by
  apply tendsToPosInfinity_of_le (fun n hn ↦ ?_) (nat_power_tendsToPosInfinity 3 (by norm_num))
  have := pow_nonneg (positive_cast hn).le 3
  have := sq_nonneg (n : ℝ)
  linarith

/-- Ví dụ 15(d): −2ⁿ+n²+1→−∞. -/
theorem exponential_negative_tendsToNegInfinity :
    SequenceTendsToNegInfinity (fun n : ℕ ↦ -(2 : ℝ) ^ n + (n : ℝ) ^ 2 + 1) := by
  have hsum := add_convergent_tendsToPosInfinity
    (geometric_div_power_tendsToPosInfinity 2 (by norm_num) 2)
    (show Section03.ConvergesTo (fun n : ℕ ↦ -1 - 1 / (n : ℝ) ^ 2) (-1) by
      apply Section03.convergesTo_iff_tendsto.mpr
      have hi : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using tendsto_const_nhds.sub hi)
  have hprod := mul_tendsToNegInfinity_of_pos_neg_infinity hsum
    (neg_tendsToNegInfinity_of_tendsToPosInfinity (nat_power_tendsToPosInfinity 2 (by norm_num)))
  apply (sequenceTendsToNegInfinity_iff_tendsto _).mpr
  exact ((sequenceTendsToNegInfinity_iff_tendsto _).mp hprod).congr'
    (eventually_atTop.2 ⟨1, fun n hn ↦ by
      have hn0 : (n : ℝ) ≠ 0 := (positive_cast hn).ne'
      field_simp
      ring⟩)

/-- Ví dụ 15(e): biểu thức chứa căn có cận dưới n. -/
theorem sqrt_sum_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ √((n : ℝ)^2 + 1) + √((n : ℝ)^4 + 2)) := by
  apply tendsToPosInfinity_of_le (fun n hn ↦ ?_) nat_tendsToPosInfinity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)^2 + 1)
  have hp := Real.sqrt_nonneg ((n : ℝ)^2 + 1)
  have hq := Real.sqrt_nonneg ((n : ℝ)^4 + 2)
  have hn0 := positive_cast hn
  nlinarith

/-- Bài 3(a): cos bị chặn dưới, nên n+cos n→+∞. -/
theorem nat_add_cos_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n : ℕ ↦ n + Real.cos n) :=
  add_bddBelow_tendsToPosInfinity nat_tendsToPosInfinity ⟨-1, fun n _ ↦ Real.neg_one_le_cos n⟩

/-- Bài 3(b): mẫu n+cos n dương tại n≥1. -/
theorem nat_add_cos_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (n : ℝ) + Real.cos n := by
  by_cases hn2 : 2 ≤ n
  · have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have := Real.neg_one_le_cos (n : ℝ)
    linarith
  · have hn1 : n = 1 := by omega
    subst n
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 1)
      (le_rfl : Real.pi ≤ Real.pi) (by linarith [Real.two_le_pi] : (1 : ℝ) < Real.pi)
    rw [Real.cos_pi] at hh
    norm_num only [Nat.cast_one]
    linarith

/-- Bài 3(b): cả hai nhiễu lượng giác chia n tiến về 0. -/
theorem trigonometric_ratio_converges_one :
    Section03.ConvergesTo (fun n : ℕ ↦
      ((n : ℝ) + Real.sin ((n : ℝ)^2)) / ((n : ℝ) + Real.cos n)) 1 := by
  have hsin : Tendsto (fun n : ℕ ↦ Real.sin ((n : ℝ)^2) / n) atTop (𝓝 0) := by
    have hb : Section04.SequenceBounded (fun n : ℕ ↦ Real.sin ((n : ℝ)^2)) :=
      (Section04.sequenceBounded_iff_abs _).mpr
        ⟨1, by norm_num, fun n _ ↦ Real.abs_sin_le_one _⟩
    simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one, one_mul] using
      Section04.zero_mul_sequenceBounded (fun n : ℕ ↦ 1 / (n : ℝ)) _
        tendsto_one_div_atTop_nhds_zero_nat hb
  have hcos : Tendsto (fun n : ℕ ↦ Real.cos n / n) atTop (𝓝 0) := by
    have hb : Section04.SequenceBounded (fun n : ℕ ↦ Real.cos n) :=
      (Section04.sequenceBounded_iff_abs _).mpr
        ⟨1, by norm_num, fun n _ ↦ Real.abs_cos_le_one _⟩
    simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one, one_mul] using
      Section04.zero_mul_sequenceBounded (fun n : ℕ ↦ 1 / (n : ℝ)) _
        tendsto_one_div_atTop_nhds_zero_nat hb
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add hsin).div ((tendsto_const_nhds (x := (1 : ℝ))).add hcos)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)
  apply Section03.convergesTo_iff_tendsto.mpr
  have hnorm : Tendsto (fun n : ℕ ↦
      (1 + Real.sin ((n : ℝ)^2) / n) / (1 + Real.cos n / n)) atTop (𝓝 1) := by
    simpa only [Pi.div_def, add_zero, div_one] using hh
  exact hnorm.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ by
    have hn0 : (n : ℝ) ≠ 0 := (positive_cast hn).ne'
    have hd : (n : ℝ) + Real.cos n ≠ 0 := (nat_add_cos_pos n hn).ne'
    field_simp⟩)

/-- Nhận xét 2.7.4(iv): dãy luân phiên dấu, độ lớn bằng n. -/
def alternatingLinear (n : ℕ) : ℝ := (-1 : ℝ) ^ n * n

/-- Độ lớn của dãy luân phiên bằng n. -/
theorem abs_alternatingLinear (n : ℕ) : |alternatingLinear n| = n := by
  simp [alternatingLinear, abs_mul, abs_pow]


theorem alternatingLinear_even (n : ℕ) : alternatingLinear (2 * n) = 2 * n := by
  simp [alternatingLinear, pow_mul]


theorem alternatingLinear_odd (n : ℕ) : alternatingLinear (2 * n + 1) = -(2 * n + 1) := by
  simp [alternatingLinear, pow_add, pow_mul]

/-- Nhận xét 2.7.4(iv): độ lớn tiến về +∞. -/
theorem abs_alternatingLinear_tendsToPosInfinity :
    SequenceTendsToPosInfinity (fun n ↦ |alternatingLinear n|) := by
  simpa only [abs_alternatingLinear] using nat_tendsToPosInfinity

/-- Chiều ngược từ |aₙ|→∞ sang aₙ→+∞ sai. -/
theorem alternatingLinear_not_tendsToPosInfinity : ¬ SequenceTendsToPosInfinity alternatingLinear := by
  intro h
  obtain ⟨N, hN, hbound⟩ := h 0
  have hh := hbound (2 * N + 1) (by omega)
  rw [alternatingLinear_odd] at hh
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- Chiều ngược từ |aₙ|→∞ sang aₙ→−∞ cũng sai. -/
theorem alternatingLinear_not_tendsToNegInfinity : ¬ SequenceTendsToNegInfinity alternatingLinear := by
  intro h
  obtain ⟨N, hN, hbound⟩ := h 0
  have hh := hbound (2 * N) (by omega)
  rw [alternatingLinear_even] at hh
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- Bài 1: dãy luân phiên không bị chặn, hai hướng vô cùng đều không tồn tại. -/
theorem alternatingLinear_unbounded_example :
    ¬ Section04.SequenceBounded alternatingLinear ∧
      ¬ SequenceTendsToPosInfinity alternatingLinear ∧ ¬ SequenceTendsToNegInfinity alternatingLinear := by
  refine ⟨?_, alternatingLinear_not_tendsToPosInfinity, alternatingLinear_not_tendsToNegInfinity⟩
  intro hb
  obtain ⟨M, _, hM⟩ := (Section04.sequenceBounded_iff_abs _).mp hb
  obtain ⟨N, hN, hbound⟩ := abs_alternatingLinear_tendsToPosInfinity M
  exact (not_lt_of_ge (hM N hN)) (hbound N le_rfl)

/-- Cận dưới lớn nhất trong nhận xét 13 chỉ được xét khi tồn tại trong ℝ. -/
theorem positive_lower_bound_iff_positive_infimum (u : ℕ → ℝ) :
    (∃ B > 0, ∀ n : ℕ, 1 ≤ n → B ≤ u n) ↔
      ∃ b : ℝ, IsGLB (Section04.sequenceRangeFromOne u) b ∧ 0 < b := by
  constructor
  · rintro ⟨B, hB, hbound⟩
    have hne := Section06.sequenceRangeFromOne_nonempty u
    have hb : BddBelow (Section04.sequenceRangeFromOne u) :=
      (Section04.sequenceBoundedBelow_iff u).mp ⟨B, hbound⟩
    refine ⟨sInf (Section04.sequenceRangeFromOne u), isGLB_csInf hne hb, ?_⟩
    have hle : B ≤ sInf (Section04.sequenceRangeFromOne u) := by
      apply le_csInf hne
      rintro x ⟨n, hn, rfl⟩
      exact hbound n hn
    exact hB.trans_le hle
  · rintro ⟨b, hglb, hb⟩
    exact ⟨b, hb, fun n hn ↦ hglb.1 ⟨n, hn, rfl⟩⟩

/-- Nhận xét 13: nếu dãy bị chặn dưới, `sInf` của tập số hạng tại n≥1
là cận dưới lớn nhất trong ℝ. -/
theorem positive_lower_bound_iff_sInf_pos (u : ℕ → ℝ)
    (hb : Section04.SequenceBoundedBelow u) :
    (∃ B > 0, ∀ n : ℕ, 1 ≤ n → B ≤ u n) ↔ 0 < sInf (Section04.sequenceRangeFromOne u) := by
  constructor
  · rintro ⟨B, hB, hbound⟩
    exact hB.trans_le (le_csInf (Section06.sequenceRangeFromOne_nonempty u) (by
      rintro x ⟨n, hn, rfl⟩
      exact hbound n hn))
  · intro hpos
    exact ⟨_, hpos, fun n hn ↦ csInf_le ((Section04.sequenceBoundedBelow_iff u).mp hb) ⟨n, hn, rfl⟩⟩

/-- Nhận xét 13: bₙ=1/n² dương, nhưng n·bₙ=1/n→0. -/
theorem positive_terms_insufficient_counterexample :
    (∀ n : ℕ, 1 ≤ n → 0 < 1 / (n : ℝ)^2) ∧
      Section03.ConvergesTo (fun n : ℕ ↦ (n : ℝ) * (1 / (n : ℝ)^2)) 0 := by
  constructor
  · exact fun n hn ↦ one_div_pos.mpr (pow_pos (positive_cast hn) 2)
  · apply Section03.convergesTo_iff_tendsto.mpr
    exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr'
      (eventually_atTop.2 ⟨1, fun n hn ↦ by
        have hn0 := (positive_cast hn).ne'
        field_simp⟩)

/-- Bỏ một phần đầu hữu hạn của dãy không bị chặn trên vẫn cho dãy không bị chặn trên. -/
theorem exists_larger_index_above {u : ℕ → ℝ} (hu : ¬ Section04.SequenceBoundedAbove u)
    (M : ℝ) (N : ℕ) : ∃ k : ℕ, N < k ∧ M < u k := by
  classical
  have hfinite : ((Finset.range (N + 1) : Finset ℕ) : Set ℕ).Finite := Finset.finite_toSet _
  obtain ⟨B, hB⟩ := (hfinite.image u).bddAbove
  have hunb : ∃ k : ℕ, 1 ≤ k ∧ max M B < u k := by
    by_contra h
    push Not at h
    exact hu ⟨max M B, fun k hk ↦ h k hk⟩
  obtain ⟨k, _, hk⟩ := hunb
  refine ⟨k, ?_, (le_max_left M B).trans_lt hk⟩
  by_contra h
  have hkN : k ≤ N := by omega
  have hh : u k ≤ B := hB ⟨k, by simpa using (show k < N + 1 by omega), rfl⟩
  exact (not_lt_of_ge hh) ((le_max_right M B).trans_lt hk)

/-- Mệnh đề 2.7.10(i): dãy không bị chặn trên có dãy con tiến về +∞. -/
theorem exists_subsequence_tendsToPosInfinity {u : ℕ → ℝ} (hu : ¬ Section04.SequenceBoundedAbove u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ SequenceTendsToPosInfinity v := by
  classical
  let step (M : ℝ) (N : ℕ) : ℕ := (exists_larger_index_above hu M N).choose
  have hstep (M : ℝ) (N : ℕ) : N < step M N ∧ M < u (step M N) :=
    (exists_larger_index_above hu M N).choose_spec
  let φ : ℕ → ℕ := Nat.rec (step 0 0) (fun k i ↦ step (k + 1) i)
  have hφ0 : φ 0 = step 0 0 := rfl
  have hφnext (k : ℕ) : φ (k + 1) = step (k + 1) (φ k) := rfl
  have hmono : StrictMono φ := strictMono_nat_of_lt_succ fun k ↦ by
    rw [hφnext]
    exact (hstep _ _).1
  have hφpos (k : ℕ) : 1 ≤ φ k := by
    have h0 : 0 < φ 0 := by rw [hφ0]; exact (hstep _ _).1
    exact le_trans (by omega : 1 ≤ φ 0) (hmono.monotone (Nat.zero_le k))
  have hvalue (k : ℕ) : (k : ℝ) < u (φ k) := by
    cases k with
    | zero => simpa only [Nat.cast_zero, hφ0] using (hstep 0 0).2
    | succ k => simpa only [hφnext, Nat.cast_add, Nat.cast_one] using (hstep (k + 1) (φ k)).2
  refine ⟨fun k ↦ u (φ k), ⟨φ, fun k _ ↦ hφpos k, hmono.strictMonoOn _, fun _ _ ↦ rfl⟩, ?_⟩
  exact tendsToPosInfinity_of_le (fun n _ ↦ (hvalue n).le) nat_tendsToPosInfinity

/-- Mệnh đề 2.7.10(ii): dãy không bị chặn dưới có dãy con tiến về −∞. -/
theorem exists_subsequence_tendsToNegInfinity {u : ℕ → ℝ} (hu : ¬ Section04.SequenceBoundedBelow u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ SequenceTendsToNegInfinity v := by
  have hneg : ¬ Section04.SequenceBoundedAbove (fun n ↦ -u n) := by
    rintro ⟨B, hB⟩
    exact hu ⟨-B, fun n hn ↦ by have := hB n hn; linarith⟩
  obtain ⟨v, ⟨φ, hpos, hmono, heq⟩, hv⟩ := exists_subsequence_tendsToPosInfinity hneg
  refine ⟨fun n ↦ -v n, ⟨φ, hpos, hmono, fun n hn ↦ ?_⟩, neg_tendsToNegInfinity_of_tendsToPosInfinity hv⟩
  change -v n = u (φ n)
  simp only [heq n hn, neg_neg]

/-- Mọi hạng căn bậc ba trong ví dụ F thuộc miền dương của căn thực. -/
theorem cube_root_example_domain (n : ℕ) (hn : 1 ≤ n) :
    0 < 8 * (n : ℝ)^3 - 1 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ hnr
  linarith

/-- Ví dụ 15(f): căn bậc ba có cận dưới 3n/2. -/
theorem cube_root_example_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    3 / 2 * (n : ℝ) ≤ (8 * (n : ℝ)^3 - 1) ^ (1 / (3 : ℝ)) := by
  have hn0 := positive_cast hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ hnr
  have hh := (Real.le_rpow_inv_iff_of_pos
    (by positivity : 0 ≤ 3 / 2 * (n : ℝ))
    (cube_root_example_domain n hn).le (by norm_num : (0 : ℝ) < 3))
  rw [inv_eq_one_div] at hh
  apply hh.mpr
  norm_num only [Real.rpow_ofNat]
  nlinarith

/-- Ví dụ 15(f): giới hạn của biểu thức chứa căn bậc ba. -/
theorem sqrt_sub_cube_root_tendsToNegInfinity :
    SequenceTendsToNegInfinity (fun n : ℕ ↦
      √((n : ℝ)^2 + 1) - (8 * (n : ℝ)^3 - 1) ^ (1 / (3 : ℝ))) := by
  have hlin : SequenceTendsToNegInfinity (fun n : ℕ ↦ 1 - (1 / 2) * (n : ℝ)) := by
    have hh := add_bddAbove_tendsToNegInfinity
      (const_mul_tendsToNegInfinity (neg_tendsToNegInfinity_of_tendsToPosInfinity nat_tendsToPosInfinity)
        (by norm_num : (0 : ℝ) < 1 / 2))
      (show Section04.SequenceBoundedAbove (fun _ : ℕ ↦ (1 : ℝ)) from ⟨1, fun _ _ ↦ le_rfl⟩)
    simpa only [mul_neg, add_comm, sub_eq_add_neg] using hh
  apply tendsToNegInfinity_of_le (fun n hn ↦ ?_) hlin
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)^2 + 1)
  have hn0 := positive_cast hn
  have hroot := Real.sqrt_nonneg ((n : ℝ)^2 + 1)
  have hlower := cube_root_example_lower_bound n hn
  have hupp : √((n : ℝ)^2 + 1) ≤ n + 1 := by nlinarith
  linarith

/-- Dòng 2443: đổi dấu n² trong C không phải một đẳng thức đa thức. -/
theorem cubic_printed_factor_counterexample :
    2 * (1 : ℝ)^3 + 1^2 + 2025 ≠ 1^3 * (2 - 1/1 + 2025/1^3) := by norm_num

/-- Dòng 2447–2448: mẫu n của 2ⁿ trong thừa số D sai tại n=2. -/
theorem exponential_printed_factor_counterexample :
    -(2 : ℝ)^2 + 2^2 + 1 ≠ -(2^2) * (2^2/2 - 1 - 1/2^2) := by norm_num

/-- Dòng 2450: căn bậc ba không bằng căn bậc hai trong F, ngay tại n=1. -/
theorem cube_root_printed_sqrt_counterexample :
    √((1 : ℝ)^2 + 1) - (8 * 1^3 - 1) ^ (1 / (3 : ℝ)) ≠
      1 * (√(1 + 1/1^2) - √(8 - 1/1^3)) := by
  norm_num only [one_pow, mul_one, one_div_one, sub_self, add_zero] at *
  intro h
  have hroot : (7 : ℝ) ^ (1 / (3 : ℝ)) = √7 := by linarith
  have hc : ((7 : ℝ) ^ (1 / (3 : ℝ))) ^ (3 : ℕ) = 7 := by
    simpa only [inv_eq_one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7) (by norm_num : (3 : ℕ) ≠ 0)
  rw [hroot] at hc
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hp := Real.sqrt_nonneg (7 : ℝ)
  have hm : √(7 : ℝ)^3 = 7 * √7 := by nlinarith [hs]
  have hval : √(7 : ℝ) = 1 := by linarith
  rw [hval] at hs
  norm_num at hs

/-- Tiêu chuẩn tỉ số: uₙ>0 và uₙ₊₁/uₙ→ℓ>1 suy ra uₙ→+∞. -/
theorem ratio_test_tendsToPosInfinity_corrected {u : ℕ → ℝ} {l : ℝ}
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < u n)
    (hlim : Section03.ConvergesTo (fun n ↦ u (n + 1) / u n) l) (hl : 1 < l) :
    SequenceTendsToPosInfinity u := by
  let s : ℝ := (l + 1) / 2
  have hs : 1 < s := by dsimp [s]; linarith
  have hε : 0 < (l - 1) / 2 := by linarith
  obtain ⟨N, hN, hbound⟩ := hlim ((l - 1) / 2) hε
  have hstep (n : ℕ) (hn : N ≤ n) : s * u n ≤ u (n + 1) := by
    have hh := (abs_lt.mp (hbound n hn)).1
    have hn0 := hpos n (hN.trans hn)
    have hratio : s < u (n + 1) / u n := by dsimp [s]; linarith
    have := (lt_div_iff₀ hn0).mp hratio
    simpa only [mul_comm] using this.le
  have hgrowth (k : ℕ) : u N * s ^ k ≤ u (N + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        u N * s ^ (k + 1) = s * (u N * s ^ k) := by ring
        _ ≤ s * u (N + k) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ u (N + k + 1) := hstep _ (by omega)
        _ = u (N + (k + 1)) := by congr 1
  have hh := const_mul_tendsToPosInfinity (geometric_tendsToPosInfinity s hs) (hpos N hN)
  intro M
  obtain ⟨K, _, hK⟩ := hh M
  refine ⟨N + K, by omega, fun n hn ↦ ?_⟩
  have hkn : K ≤ n - N := by omega
  have hsplit : N + (n - N) = n := by omega
  have hg := hgrowth (n - N)
  rw [hsplit] at hg
  exact (hK (n - N) hkn).trans_le hg

/-- Dòng 2465: tỉ số lớn hơn s từ một chỉ số trở đi chưa cho cận hình học bắt đầu tại a₁. -/
def ratioAnchorCounterexample (n : ℕ) : ℝ := if n = 1 then 100 else 2 ^ n

/-- Phản ví dụ còn thỏa tính dương và giới hạn tỉ số 2>1. -/
theorem ratio_printed_initial_anchor_counterexample :
    (∀ n : ℕ, 1 ≤ n → 0 < ratioAnchorCounterexample n) ∧
      Section03.ConvergesTo (fun n ↦ ratioAnchorCounterexample (n + 1) /
        ratioAnchorCounterexample n) 2 ∧
      ¬ ratioAnchorCounterexample 1 * (3 / 2 : ℝ)^2 < ratioAnchorCounterexample 3 := by
  refine ⟨fun n _ ↦ ?_, ?_, ?_⟩
  · unfold ratioAnchorCounterexample
    split_ifs <;> positivity
  · apply Section03.convergesTo_iff_tendsto.mpr
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨2, fun n hn ↦ by
      have hn1 : n ≠ 1 := by omega
      have hns1 : n + 1 ≠ 1 := by omega
      change (2 : ℝ) = ratioAnchorCounterexample (n + 1) / ratioAnchorCounterexample n
      unfold ratioAnchorCounterexample
      rw [if_neg hns1, if_neg hn1, pow_succ]
      field_simp⟩)
  · norm_num [ratioAnchorCounterexample]

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S08-theorem-006.proof-initial-anchor: cận `u N * s ^ k` bắt đầu từ số hạng `u N`. -/
theorem ratio_tail_anchor (u : ℕ → ℝ) (s : ℝ) (hs : 0 ≤ s) (N : ℕ)
    (hstep : ∀ n : ℕ, N ≤ n → s * u n ≤ u (n + 1)) :
    ∀ k : ℕ, u N * s ^ k ≤ u (N + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      u N * s ^ (k + 1) = s * (u N * s ^ k) := by ring
      _ ≤ s * u (N + k) := mul_le_mul_of_nonneg_left ih hs
      _ ≤ u (N + k + 1) := hstep _ (by omega)
      _ = u (N + (k + 1)) := by congr 1

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S08-theorem-006.proof-initial-anchor, dòng 2465: cận hình học lấy số hạng đầu làm mốc trong lời giải gốc. -/
theorem source_ratio_initial_anchor (u : ℕ → ℝ) (s : ℝ) (N : ℕ)
    (hs : 1 < s) (hN : 1 ≤ N)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < u n)
    (hstep : ∀ n : ℕ, N ≤ n → s * u (n - 1) < u n) :
    ∀ n : ℕ, N ≤ n → u 1 * s ^ (n - 1) < u n := by
  sorry

/-- Bài 5(a): tổng điều hòa từ k=1 đến n. -/
def harmonicPartialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)


theorem harmonicPartialSum_eq_range (n : ℕ) :
    harmonicPartialSum n = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp [harmonicPartialSum]
  | succ n ih =>
    rw [harmonicPartialSum, Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    simpa only [Nat.cast_add, Nat.cast_one, harmonicPartialSum] using
      congrArg (fun x : ℝ ↦ x + 1 / ((n : ℝ) + 1)) ih

/-- Bài 5(a): tổng điều hòa tiến về +∞. -/
theorem harmonicPartialSum_tendsToPosInfinity : SequenceTendsToPosInfinity harmonicPartialSum := by
  apply (sequenceTendsToPosInfinity_iff_tendsto _).mpr
  convert Real.tendsto_sum_range_one_div_nat_succ_atTop using 1
  funext n
  exact harmonicPartialSum_eq_range n

/-- Bài 5(b): mẫu ln k dương từ k=2. -/
def reciprocalLogPartialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 2 n, 1 / Real.log k

/-- Với k≥2, ta có 0<ln k và 1/k≤1/ln k. -/
theorem reciprocal_log_ge_reciprocal (k : ℕ) (hk : 2 ≤ k) :
    0 < Real.log k ∧ 1 / (k : ℝ) ≤ 1 / Real.log k := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 < Real.log k := Real.log_pos (by linarith)
  have hle : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  exact ⟨hlog, one_div_le_one_div_of_le hlog hle⟩

/-- Bài 5(b): tổng 1/ln k, k=2,…,n, tiến về +∞. -/
theorem reciprocalLogPartialSum_tendsToPosInfinity : SequenceTendsToPosInfinity reciprocalLogPartialSum := by
  have htail : SequenceTendsToPosInfinity (fun n ↦ harmonicPartialSum n - 1) := by
    have hh := add_bddBelow_tendsToPosInfinity harmonicPartialSum_tendsToPosInfinity
      (show Section04.SequenceBoundedBelow (fun _ : ℕ ↦ (-1 : ℝ)) from ⟨-1, fun _ _ ↦ le_rfl⟩)
    simpa only [sub_eq_add_neg] using hh
  apply tendsToPosInfinity_of_le (fun n hn ↦ ?_) htail
  have hsplit : harmonicPartialSum n = 1 + ∑ k ∈ Finset.Icc 2 n, 1 / (k : ℝ) := by
    induction n, hn using Nat.le_induction with
    | base => norm_num [harmonicPartialSum]
    | succ n hn ih =>
      calc
        harmonicPartialSum (n + 1) = harmonicPartialSum n + 1 / ((n + 1 : ℕ) : ℝ) := by
          exact Finset.sum_Icc_succ_top (by omega) _
        _ = 1 + ((∑ k ∈ Finset.Icc 2 n, 1 / (k : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) := by
          rw [ih]
          ring
        _ = 1 + ∑ k ∈ Finset.Icc 2 (n + 1), 1 / (k : ℝ) := by
          rw [Finset.sum_Icc_succ_top (by omega)]
  rw [hsplit]
  simp only [add_sub_cancel_left, reciprocalLogPartialSum]
  exact Finset.sum_le_sum fun k hk ↦ (reciprocal_log_ge_reciprocal k (Finset.mem_Icc.mp hk).1).2

/-- Bài 4(a): uₙ=2n,vₙ=−n cho tổng n→+∞. -/
theorem opposite_infinities_sum_tendsToPosInfinity_example :
    ∃ u v : ℕ → ℝ, SequenceTendsToPosInfinity u ∧ SequenceTendsToNegInfinity v ∧
      SequenceTendsToPosInfinity (fun n ↦ u n + v n) := by
  refine ⟨fun n : ℕ ↦ 2 * (n : ℝ), fun n : ℕ ↦ -(n : ℝ),
    const_mul_tendsToPosInfinity nat_tendsToPosInfinity (by norm_num), neg_tendsToNegInfinity_of_tendsToPosInfinity nat_tendsToPosInfinity, ?_⟩
  simpa only [two_mul, add_neg_cancel_right] using nat_tendsToPosInfinity

/-- Bài 4(b): uₙ=n+1,vₙ=−n cho tổng hằng 1. -/
theorem opposite_infinities_sum_one_example :
    ∃ u v : ℕ → ℝ, SequenceTendsToPosInfinity u ∧ SequenceTendsToNegInfinity v ∧
      Section03.ConvergesTo (fun n ↦ u n + v n) 1 := by
  refine ⟨fun n : ℕ ↦ (n : ℝ) + 1, fun n : ℕ ↦ -(n : ℝ),
    add_bddBelow_tendsToPosInfinity nat_tendsToPosInfinity ⟨1, fun _ _ ↦ le_rfl⟩,
    neg_tendsToNegInfinity_of_tendsToPosInfinity nat_tendsToPosInfinity, ?_⟩
  apply Section03.convergesTo_iff_tendsto.mpr
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)) using 1
  simp


theorem alternating_unit_no_infinite_limit :
    ¬ SequenceTendsToPosInfinity (fun n : ℕ ↦ (-1 : ℝ)^n) ∧
      ¬ SequenceTendsToNegInfinity (fun n : ℕ ↦ (-1 : ℝ)^n) := by
  constructor
  · intro h
    obtain ⟨N, _, hbound⟩ := h 2
    have hh := hbound N le_rfl
    have habs : |(-1 : ℝ)^N| = 1 := by simp [abs_pow]
    have := le_abs_self ((-1 : ℝ)^N)
    linarith
  · intro h
    obtain ⟨N, _, hbound⟩ := h (-2)
    have hh := hbound N le_rfl
    have habs : |(-1 : ℝ)^N| = 1 := by simp [abs_pow]
    have := neg_abs_le ((-1 : ℝ)^N)
    linarith

/-- Bài 4(c): nhiễu ±1 của v=−n cho tổng không có giới hạn nào. -/
theorem opposite_infinities_sum_divergent_example :
    ∃ u v : ℕ → ℝ, SequenceTendsToPosInfinity u ∧ SequenceTendsToNegInfinity v ∧
      Section03.IsDivergent (fun n ↦ u n + v n) ∧
      ¬ SequenceTendsToPosInfinity (fun n ↦ u n + v n) ∧
      ¬ SequenceTendsToNegInfinity (fun n ↦ u n + v n) := by
  have hv : SequenceTendsToNegInfinity (fun n : ℕ ↦ -(n : ℝ) + (-1 : ℝ)^n) := by
    apply add_bddAbove_tendsToNegInfinity (neg_tendsToNegInfinity_of_tendsToPosInfinity nat_tendsToPosInfinity)
    refine ⟨1, fun n _ ↦ ?_⟩
    have hh : |(-1 : ℝ)^n| = 1 := by simp [abs_pow]
    have := le_abs_self ((-1 : ℝ)^n)
    linarith
  refine ⟨fun n : ℕ ↦ (n : ℝ), fun n : ℕ ↦ -(n : ℝ) + (-1 : ℝ)^n,
    nat_tendsToPosInfinity, hv, ?_, ?_, ?_⟩
  · simp only [add_neg_cancel_left]
    intro h
    obtain ⟨a, ha⟩ := h
    exact Section04.alternating_sequence_divergent ⟨a, Section03.convergesTo_iff_tendsto.mp ha⟩
  · simpa only [add_neg_cancel_left] using alternating_unit_no_infinite_limit.1
  · simpa only [add_neg_cancel_left] using alternating_unit_no_infinite_limit.2

end

end calculus.Chapter02.Section07
