import calculus.Chapter02.Section04
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Data.Int.Cast.Lemmas

/-!
# 2.9. Dãy Cauchy

Nguồn: `source/Ch2_dayso.tex`, dòng 2669–2929; mã C02-S10.
-/

namespace calculus.Chapter02.Section09

open Filter Set
open scoped Topology BigOperators

/-- Định nghĩa 2.9.1: hai chỉ số cùng vượt một ngưỡng phụ thuộc ε. -/
def SequenceCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧
    ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n → |u m - u n| < ε

/-- Điều kiện Cauchy theo ε–N tương đương `CauchySeq`. -/
theorem sequenceCauchy_iff {u : ℕ → ℝ} : SequenceCauchy u ↔ CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, _, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn ↦ by simpa only [Real.dist_eq] using hN m hm n hn⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max 1 N, le_max_left _ _, fun m hm n hn ↦ ?_⟩
    simpa only [Real.dist_eq] using
      hN m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)

/-- Định lí 2.9.3: dãy hội tụ là dãy Cauchy. -/
theorem converges_sequenceCauchy {u : ℕ → ℝ} {a : ℝ}
    (h : Section03.ConvergesTo u a) : SequenceCauchy u := by
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := h (ε / 2) (by positivity)
  refine ⟨N, hN, fun m hm n hn ↦ ?_⟩
  have ht := abs_sub_le (u m) a (u n)
  rw [abs_sub_comm a] at ht
  linarith [hsmall m hm, hsmall n hn]

/-- Ví dụ 2.9.2: nghịch đảo có giới hạn 0, nên là Cauchy. -/
theorem reciprocal_sequenceCauchy : SequenceCauchy (fun n : ℕ ↦ 1 / (n : ℝ)) :=
  converges_sequenceCauchy Section03.reciprocal_converges

/-- Định lí 2.9.4: dãy Cauchy bị chặn. -/
theorem sequenceCauchy_bounded {u : ℕ → ℝ} (h : SequenceCauchy u) :
    Section04.SequenceBounded u := by
  obtain ⟨R, hR, hdist⟩ := cauchySeq_bdd (sequenceCauchy_iff.mp h)
  apply (Section04.sequenceBounded_iff_abs u).mpr
  refine ⟨R + |u 1|, by positivity, fun n _ ↦ ?_⟩
  have ht := abs_sub_le (u n) (u 1) 0
  simp only [sub_zero] at ht
  have hd : |u n - u 1| < R := by simpa only [Real.dist_eq] using hdist n 1
  linarith

/-- Bổ đề 2.9.5: dãy con hội tụ buộc cả dãy Cauchy có cùng giới hạn. -/
theorem sequenceCauchy_converges_of_subsequence {u v : ℕ → ℝ} {a : ℝ}
    (hu : SequenceCauchy u) (hv : Section04.IsSequenceSubsequence u v)
    (ha : Section03.ConvergesTo v a) : Section03.ConvergesTo u a := by
  obtain ⟨φ, hpos, hmono, hterms⟩ := hv
  intro ε hε
  obtain ⟨N, hN, hpair⟩ := hu (ε / 2) (by positivity)
  obtain ⟨K, _, hnear⟩ := ha (ε / 2) (by positivity)
  refine ⟨max N K, hN.trans (le_max_left _ _), fun n hn ↦ ?_⟩
  have hnN := (le_max_left N K).trans hn
  have hnpos := hN.trans hnN
  have hidx := Section04.subsequence_index_ge φ hpos hmono n hnpos
  have hleft := hpair n hnN (φ n) (hnN.trans hidx)
  have hright := hnear n ((le_max_right N K).trans hn)
  rw [hterms n hnpos] at hright
  exact lt_of_le_of_lt (abs_sub_le (u n) (u (φ n)) a) (by linarith)

/-- Nhận xét 2.9.6: có thể xét mọi khoảng tăng p≥1 từ cùng số hạng. -/
theorem sequenceCauchy_iff_forward {u : ℕ → ℝ} : SequenceCauchy u ↔
    ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ p : ℕ, 1 ≤ p → |u (n + p) - u n| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hpair⟩ := h ε hε
    exact ⟨N, hN, fun n hn p _ ↦ hpair (n + p) (by omega) n hn⟩
  · intro h ε hε
    obtain ⟨N, hN, hforward⟩ := h ε hε
    refine ⟨N, hN, fun m hm n hn ↦ ?_⟩
    rcases lt_trichotomy m n with hmn | rfl | hnm
    · have heq : m + (n - m) = n := Nat.add_sub_of_le hmn.le
      have hp := hforward m hm (n - m) (by omega)
      rw [heq, abs_sub_comm] at hp
      exact hp
    · simpa using hε
    · have heq : n + (m - n) = m := Nat.add_sub_of_le hnm.le
      simpa only [heq] using hforward n hn (m - n) (by omega)

/-- Định lí 2.9.7: dãy thực hội tụ khi và chỉ khi là Cauchy. -/
theorem sequenceCauchy_iff_convergent {u : ℕ → ℝ} :
    SequenceCauchy u ↔ Section03.IsConvergent u := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (sequenceCauchy_iff.mp h)
    exact ⟨a, Section03.convergesTo_iff_tendsto.mpr ha⟩
  · rintro ⟨a, ha⟩
    exact converges_sequenceCauchy ha


theorem summable_partial_sums_sequenceCauchy (f : ℕ → ℝ) (hf : Summable f) :
    SequenceCauchy (fun n ↦ ∑ k ∈ Finset.range n, f k) :=
  sequenceCauchy_iff.mpr hf.tendsto_sum_tsum_nat.cauchySeq

/-- Ví dụ 2.9.8: tổng 1/1!+⋯+1/n!. -/
noncomputable def reciprocalFactorialPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1).factorial : ℝ)

/-- Ví dụ 2.9.8: tổng riêng từ 1/1! đến 1/n! là dãy Cauchy. -/
theorem reciprocal_factorial_partial_sums_sequenceCauchy : SequenceCauchy reciprocalFactorialPartialSum := by
  apply summable_partial_sums_sequenceCauchy
  have hs := (summable_nat_add_iff (f := fun n : ℕ ↦ (1 : ℝ) ^ n / n.factorial) 1).mpr
    (Real.summable_pow_div_factorial 1)
  simpa only [one_pow] using hs

/-- Kết luận hội tụ của ví dụ 2.9.8. -/
theorem reciprocal_factorial_partial_sums_convergent : Section03.IsConvergent reciprocalFactorialPartialSum :=
  sequenceCauchy_iff_convergent.mp reciprocal_factorial_partial_sums_sequenceCauchy

/-- Bài 2.9.1(a): tổng luân phiên từ k=1 đến n, với dấu đầu dương. -/
noncomputable def alternatingReciprocalFactorialPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / ((k + 1).factorial : ℝ)

/-- Bài 2.9.1(a): tổng riêng luân phiên của 1/k! là dãy Cauchy. -/
theorem alternating_reciprocal_factorial_sequenceCauchy : SequenceCauchy alternatingReciprocalFactorialPartialSum := by
  apply summable_partial_sums_sequenceCauchy
  have hs := ((summable_nat_add_iff
    (f := fun n : ℕ ↦ (-1 : ℝ) ^ n / n.factorial) 1).mpr
    (Real.summable_pow_div_factorial (-1))).neg
  have heq : (fun k : ℕ ↦ -((-1 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ))) =
      (fun k : ℕ ↦ (-1 : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
    funext k
    rw [pow_succ]
    ring
  rw [heq] at hs
  exact hs

/-- Bài 2.9.1(b): n+(−1)ⁿ/n không bị chặn, nên không Cauchy. -/
theorem nat_add_alternating_reciprocal_not_sequenceCauchy :
    ¬ SequenceCauchy (fun n : ℕ ↦ (n : ℝ) + (-1 : ℝ) ^ n / n) := by
  intro hc
  obtain ⟨M, _, hM⟩ := (Section04.sequenceBounded_iff_abs _).mp (sequenceCauchy_bounded hc)
  obtain ⟨n, hn⟩ := exists_nat_gt (|M| + 2)
  have hnpos : 1 ≤ n := by
    have : (0 : ℝ) < n := by linarith [abs_nonneg M]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt this)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hb : |(-1 : ℝ) ^ n / n| ≤ 1 := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity : (0 : ℝ) < n)).mpr hnreal
  have hlow := neg_abs_le ((-1 : ℝ) ^ n / n)
  have hupp := le_abs_self ((n : ℝ) + (-1 : ℝ) ^ n / n)
  have := hM n hnpos
  linarith [le_abs_self M]

/-- Bài 2.9.2(a): dãy luân phiên ±1 không thỏa điều kiện Cauchy. -/
theorem alternating_not_sequenceCauchy : ¬ SequenceCauchy (fun n ↦ (-1 : ℝ) ^ n) := by
  intro h
  exact Section03.alternating_isDivergent (sequenceCauchy_iff_convergent.mp h)

/-- Bài 2.9.2(b). -/
theorem alternating_reciprocal_sequenceCauchy :
    SequenceCauchy (fun n : ℕ ↦ (-1 : ℝ) ^ n / n) :=
  converges_sequenceCauchy Section03.alternating_reciprocal_converges

/-- Bài 2.9.2(c): n/(n+1)→1, với mẫu dương. -/
theorem nat_div_succ_converges : Section03.ConvergesTo (fun n : ℕ ↦ (n : ℝ) / (n + 1)) 1 := by
  apply Section03.convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have heq : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
  rw [heq, abs_neg, abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le hnpos (by linarith)

/-- Kết luận Cauchy của bài 2.9.2(c). -/
theorem nat_div_succ_sequenceCauchy : SequenceCauchy (fun n : ℕ ↦ (n : ℝ) / (n + 1)) :=
  converges_sequenceCauchy nat_div_succ_converges

/-- Bài 2.9.2(d). -/
theorem cosine_div_sequenceCauchy : SequenceCauchy (fun n : ℕ ↦ Real.cos (n : ℝ) / n) :=
  converges_sequenceCauchy Section03.cosine_div_converges

/-- Bài 2.9.4: tổng hai dãy Cauchy là dãy Cauchy. -/
theorem sequenceCauchy_add {u v : ℕ → ℝ} (hu : SequenceCauchy u) (hv : SequenceCauchy v) :
    SequenceCauchy (fun n ↦ u n + v n) := by
  obtain ⟨a, ha⟩ := sequenceCauchy_iff_convergent.mp hu
  obtain ⟨b, hb⟩ := sequenceCauchy_iff_convergent.mp hv
  exact sequenceCauchy_iff.mpr
    (((Section03.convergesTo_iff_tendsto.mp ha).add
      (Section03.convergesTo_iff_tendsto.mp hb)).cauchySeq)

/-- Bài 2.9.4: tích hai dãy Cauchy là dãy Cauchy. -/
theorem sequenceCauchy_mul {u v : ℕ → ℝ} (hu : SequenceCauchy u) (hv : SequenceCauchy v) :
    SequenceCauchy (fun n ↦ u n * v n) := by
  obtain ⟨a, ha⟩ := sequenceCauchy_iff_convergent.mp hu
  obtain ⟨b, hb⟩ := sequenceCauchy_iff_convergent.mp hv
  exact sequenceCauchy_iff.mpr
    (((Section03.convergesTo_iff_tendsto.mp ha).mul
      (Section03.convergesTo_iff_tendsto.mp hb)).cauchySeq)

/-- Bài 2.9.5: |uₙ|≤(n+1)/(2n²+n+1) suy ra u là dãy Cauchy. -/
theorem sequenceCauchy_of_rational_bound {u : ℕ → ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |u n| ≤ (1 + n) / (1 + n + 2 * (n : ℝ) ^ 2)) :
    SequenceCauchy u := by
  apply converges_sequenceCauchy (a := 0)
  apply Section03.convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sub_zero]
  apply (h n hn).trans
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + n + 2 * (n : ℝ) ^ 2)
    (by positivity : (0 : ℝ) < n)).mpr
  nlinarith

/-- Bài 2.9.6: dãy Cauchy nguyên là dãy hằng từ một ngưỡng. -/
theorem integer_sequenceCauchy_eventually_constant {u : ℕ → ℝ}
    (hc : SequenceCauchy u) (hi : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, u n = z) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, ∀ n : ℕ, N ≤ n → u n = C := by
  obtain ⟨N, hN, hnear⟩ := hc 1 (by norm_num)
  obtain ⟨zN, hzN⟩ := hi N hN
  refine ⟨N, hN, u N, fun n hn ↦ ?_⟩
  obtain ⟨zn, hzn⟩ := hi n (hN.trans hn)
  have habs := hnear n hn N le_rfl
  rw [hzn, hzN] at habs
  have hz : |zn - zN| < (1 : ℤ) := by exact_mod_cast habs
  have hb := abs_lt.mp hz
  have heq : zn = zN := by omega
  simp [hzn, hzN, heq]

/-- Bài 2.9.7: nếu u là dãy Cauchy và |vₘ−vₙ|≤k|uₘ−uₙ|, k>0, thì v là dãy Cauchy. -/
theorem sequenceCauchy_of_distance_bound {u v : ℕ → ℝ} {k : ℝ}
    (hu : SequenceCauchy u) (hk : 0 < k)
    (h : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n → |v m - v n| ≤ k * |u m - u n|) :
    SequenceCauchy v := by
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := hu (ε / k) (div_pos hε hk)
  refine ⟨N, hN, fun m hm n hn ↦ ?_⟩
  apply lt_of_le_of_lt (h m (hN.trans hm) n (hN.trans hn))
  have hlt := mul_lt_mul_of_pos_left (hsmall m hm n hn) hk
  simpa only [mul_div_cancel₀ ε (ne_of_gt hk)] using hlt

/-- Bài 2.9.8: với k cố định, cận 1/(nk) cho giới hạn uₖ. -/
theorem reciprocal_product_distance_converges {u : ℕ → ℝ}
    (h : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n → |u m - u n| ≤ 1 / ((m : ℝ) * n))
    (k : ℕ) (hk : 1 ≤ k) : Section03.ConvergesTo u (u k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  apply Section03.convergesTo_of_error_le_const_div (C := 1 / (k : ℝ)) (by positivity)
  intro n hn
  simpa only [div_div, mul_comm] using h n hn k hk

/-- Bài 2.9.8(b): dãy hằng trên miền chỉ số n≥1. -/
theorem reciprocal_product_distance_constant {u : ℕ → ℝ}
    (h : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n → |u m - u n| ≤ 1 / ((m : ℝ) * n)) :
    ∀ n : ℕ, 1 ≤ n → u n = u 1 := by
  intro n hn
  exact Section03.limit_unique (reciprocal_product_distance_converges h n hn)
    (reciprocal_product_distance_converges h 1 le_rfl)

/-- Bài 2.9.8(a): dãy hội tụ và là Cauchy. -/
theorem reciprocal_product_distance_sequenceCauchy {u : ℕ → ℝ}
    (h : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n → |u m - u n| ≤ 1 / ((m : ℝ) * n)) :
    SequenceCauchy u :=
  converges_sequenceCauchy (reciprocal_product_distance_converges h 1 le_rfl)


theorem sequenceCauchy_of_summable_increments {u : ℕ → ℝ} {d : ℕ → ℝ}
    (hd : Summable d)
    (h : ∀ n : ℕ, 1 ≤ n → |u (n + 1) - u n| ≤ d n) : SequenceCauchy u := by
  have hs : Summable (fun n : ℕ ↦ d (n + 1)) := (summable_nat_add_iff 1).mpr hd
  have hc : CauchySeq (fun n : ℕ ↦ u (n + 1)) := by
    apply cauchySeq_of_dist_le_of_summable (fun n ↦ d (n + 1)) _ hs
    intro n
    simpa only [Real.dist_eq, abs_sub_comm, Nat.succ_eq_add_one] using h (n + 1) (by omega)
  exact sequenceCauchy_iff.mpr ((cauchySeq_shift 1).mp hc)

/-- Bài 2.9.10: sai phân ≤1/(n+1)! là khả tổng. -/
theorem factorial_increment_sequenceCauchy {u : ℕ → ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |u (n + 1) - u n| ≤ 1 / ((n + 1).factorial : ℝ)) :
    SequenceCauchy u := by
  apply sequenceCauchy_of_summable_increments (d := fun n ↦ 1 / ((n + 1).factorial : ℝ)) _ h
  simpa only [one_pow] using
    (summable_nat_add_iff (f := fun n : ℕ ↦ (1 : ℝ) ^ n / n.factorial) 1).mpr
      (Real.summable_pow_div_factorial 1)

/-- Bài 2.9.11: dãy có sai phân bị chặn bởi cấp số nhân, với 0<r<1. -/
theorem geometric_increment_sequenceCauchy {u : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (h : ∀ n : ℕ, 1 ≤ n → |u (n + 1) - u n| ≤ r ^ n) : SequenceCauchy u :=
  sequenceCauchy_of_summable_increments (summable_geometric_of_lt_one hr0.le hr1) h

/-- Bài 2.9.12: trị tuyệt đối của hiệu hai dãy Cauchy là dãy Cauchy. -/
theorem abs_difference_sequenceCauchy {u v : ℕ → ℝ} (hu : SequenceCauchy u) (hv : SequenceCauchy v) :
    SequenceCauchy (fun n ↦ |u n - v n|) := by
  obtain ⟨a, ha⟩ := sequenceCauchy_iff_convergent.mp hu
  obtain ⟨b, hb⟩ := sequenceCauchy_iff_convergent.mp hv
  exact sequenceCauchy_iff.mpr (((Section03.convergesTo_iff_tendsto.mp ha).sub
    (Section03.convergesTo_iff_tendsto.mp hb)).abs.cauchySeq)

/-- Bài 2.9.3: |n cos(3n²+2n+1)/(n+1)|≤1. -/
theorem cosine_fraction_mem_interval (n : ℕ) :
    (n : ℝ) * Real.cos (3 * (n : ℝ) ^ 2 + 2 * n + 1) / (n + 1) ∈ Icc (-1) 1 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hb : |(n : ℝ) * Real.cos (3 * (n : ℝ) ^ 2 + 2 * n + 1) / (n + 1)| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg hn, abs_of_pos hden]
    apply (div_le_one hden).mpr
    have := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (3 * (n : ℝ) ^ 2 + 2 * n + 1)) hn
    linarith
  exact abs_le.mp hb

/-- Bài 2.9.3: tồn tại dãy con hội tụ. -/
theorem cosine_fraction_convergent_subsequence :
    ∃ v : ℕ → ℝ,
      Section04.IsSequenceSubsequence
        (fun n : ℕ ↦ (n : ℝ) * Real.cos (3 * (n : ℝ) ^ 2 + 2 * n + 1) / (n + 1)) v ∧
      Section03.IsConvergent v := by
  let u := fun n : ℕ ↦ (n : ℝ) * Real.cos (3 * (n : ℝ) ^ 2 + 2 * n + 1) / (n + 1)
  obtain ⟨a, _, φ, hφ, ht⟩ :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).tendsto_subseq cosine_fraction_mem_interval
  refine ⟨u ∘ φ, ⟨φ, fun k hk ↦ hk.trans (hφ.id_le k), ?_, fun _ _ ↦ rfl⟩,
    a, Section03.convergesTo_iff_tendsto.mpr ht⟩
  exact fun _ _ _ _ hij ↦ hφ hij

/-- Bài 2.9.9: tổng điều hòa. -/
noncomputable def harmonicPartialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

/-- Bài 2.9.9: cận sai phân của tổng điều hòa. -/
theorem harmonic_increment_bound (n : ℕ) :
    |harmonicPartialSum (n + 1) - harmonicPartialSum n| ≤ 1 / ((n : ℝ) + 1) := by
  simp only [harmonicPartialSum, Finset.sum_range_succ, add_sub_cancel_left]
  rw [abs_of_nonneg (by positivity)]

/-- Tổng điều hòa tiến về +∞. -/
theorem harmonic_partial_sums_tendsto_atTop : Tendsto harmonicPartialSum atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n : ℕ ↦ by positivity : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1))).mp
  intro hs
  have hs' : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hs')

/-- Bài 2.9.9: cận sai phân điều hòa không bảo đảm dãy là Cauchy. -/
theorem harmonic_not_sequenceCauchy : ¬ SequenceCauchy harmonicPartialSum := by
  intro hc
  obtain ⟨M, hM⟩ := (sequenceCauchy_bounded hc).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_atTop.mp harmonic_partial_sums_tendsto_atTop (M + 1))
  have hlarge := hN (max N 1) (le_max_left _ _)
  have hsmall := hM (max N 1) (le_max_right _ _)
  linarith

/-- Dòng 2683: n=1,m=2 là phản ví dụ cho đẳng thức lặp chỉ số n. -/
theorem reciprocal_proof_typo_counterexample :
    |(1 : ℝ) / 1 - 1 / 2| ≠ |(1 : ℝ) / 1 - 1 / 1| := by norm_num

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S10-example-001.proof-repeated-index: hiệu hai số hạng dùng hai chỉ số `n`, `m`. -/
theorem reciprocal_distinct_index_identity (n m : ℕ) :
    |(fun k : ℕ ↦ 1 / (k : ℝ)) n - (fun k : ℕ ↦ 1 / (k : ℝ)) m| =
      |1 / (n : ℝ) - 1 / (m : ℝ)| := rfl

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S10-example-001.proof-repeated-index, dòng 2683: đẳng thức lặp chỉ số trong lời giải gốc. -/
theorem source_reciprocal_repeated_index_identity (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |1 / (n : ℝ) - 1 / (m : ℝ)| = |1 / (n : ℝ) - 1 / (n : ℝ)| := by
  sorry

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S10-exercise-013: dãy Cauchy nhận giá trị nguyên dương thì hằng từ một chỉ số. -/
theorem positive_natural_cauchy_eventually_constant (x : ℕ → ℕ)
    (hpositive : ∀ n : ℕ, 1 ≤ n → 1 ≤ x n)
    (hc : calculus.Chapter02.Section09.SourceCauchy (fun n ↦ (x n : ℝ))) :
    ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → x n = a := by
  obtain ⟨N, hN, htail⟩ :=
    calculus.Chapter02.Section09.natural_sourceCauchy_eventually_constant x hc
  exact ⟨x N, N, hpositive N hN, hN, htail⟩

end calculus.SourceCorrectionsChapter12

namespace calculus.SourceIssues

open Filter Topology

/-- Dãy xₙ=n không hằng từ một chỉ số nào. -/
theorem natural_sequence_not_eventually_constant :
    ¬ ∃ a N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n = a := by
  rintro ⟨a, N, _, h⟩
  have hN := h N le_rfl
  have hnext := h (N + 1) (Nat.le_succ N)
  omega


end calculus.SourceIssues

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- Bài 2.9.13, dòng 2881–2883: khẳng định gốc rằng dãy nhận giá trị tự nhiên là dãy hằng từ một chỉ số trở đi. -/
theorem source_natural_sequence_eventually_constant (x : ℕ → ℕ)
    (hx : ∀ n : ℕ, 1 ≤ n → 1 ≤ x n) :
    ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → x n = a := by
  sorry

/-- Bài 2.9.13: dãy Cauchy nhận giá trị tự nhiên là dãy hằng từ một chỉ số trở đi. -/
theorem natural_sequenceCauchy_eventually_constant (x : ℕ → ℕ)
    (hc : SequenceCauchy (fun n ↦ (x n : ℝ))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → x n = x N := by
  obtain ⟨N, hN, C, hC⟩ := integer_sequenceCauchy_eventually_constant hc
    (fun n _ ↦ ⟨(x n : ℤ), by norm_cast⟩)
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have heq : (x n : ℝ) = x N := (hC n hn).trans (hC N le_rfl).symm
  exact_mod_cast heq

/-
namespace calculus.SourceIssues

open Filter Topology

theorem half_natural_step (n : ℕ) :
    |((n + 1 : ℕ) : ℝ) / 2 - (n : ℝ) / 2| = 1 / (2 : ℝ) := by
  have h : ((n + 1 : ℕ) : ℝ) / 2 - (n : ℝ) / 2 = 1 / 2 := by
    push_cast
    ring
  rw [h]
  norm_num

/-- Bước bị chặn bởi hằng `1/a` với `a>1` không bảo đảm hội tụ. -/
theorem bounded_steps_do_not_imply_convergence :
    ∃ a : ℝ, 1 < a ∧ ∃ x : ℕ → ℝ,
      (∀ k : ℕ, 0 < k → |x (k + 1) - x k| ≤ 1 / a) ∧
      ¬ ∃ l : ℝ, Tendsto x atTop (𝓝 l) := by
  refine ⟨2, by norm_num, fun n ↦ (n : ℝ) / 2, ?_, ?_⟩
  · intro k _
    exact (half_natural_step k).le
  · rintro ⟨l, hl⟩
    have htop : Tendsto (fun n : ℕ ↦ (n : ℝ) / 2) atTop atTop := by
      simpa only [div_eq_mul_inv, mul_comm] using
        tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2⁻¹)
    exact not_tendsto_nhds_of_tendsto_atTop htop l hl

end calculus.SourceIssues

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- Bài 2.9.14, dòng 2885–2886: khẳng định gốc rằng cận sai phân 1/a, với a>1, bảo đảm hội tụ. -/
theorem source_convergent_of_bounded_steps {x : ℕ → ℝ} {a : ℝ}
    (ha : 1 < a)
    (hstep : ∀ k : ℕ, 1 ≤ k → |x (k + 1) - x k| ≤ 1 / a) :
    Section03.IsConvergent x := by
  sorry

/-- Bài 2.9.14: cận sai phân hình học a⁻ⁿ, với a>1, bảo đảm hội tụ. -/
theorem convergent_of_reciprocal_geometric_increments {u : ℕ → ℝ} {a : ℝ}
    (ha : 1 < a)
    (h : ∀ n : ℕ, 1 ≤ n → |u (n + 1) - u n| ≤ (1 / a) ^ n) :
    Section03.IsConvergent u := by
  apply sequenceCauchy_iff_convergent.mp
  exact geometric_increment_sequenceCauchy (by positivity) ((div_lt_one (by positivity)).mpr ha) h

end calculus.Chapter02.Section09
