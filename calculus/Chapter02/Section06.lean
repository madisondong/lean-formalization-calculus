import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Instances.Real.Lemmas
import calculus.Chapter02.Section04
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# 2.6. Dãy đơn điệu

Nguồn: `source/Ch2_dayso.tex`, dòng 1874–2102.
-/

namespace calculus.Chapter02.Section06

open Filter Set
open scoped Topology BigOperators

/-- Định nghĩa 2.6.1: dãy tăng thỏa uₙ≤uₙ₊₁. -/
def SequenceIncreasing (u : ℕ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → u n ≤ u (n + 1)

/-- Định nghĩa 2.6.1: giảm nghĩa là uₙ₊₁≤uₙ. -/
def SequenceDecreasing (u : ℕ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → u (n + 1) ≤ u n

/-- Đơn điệu là tăng hoặc giảm, cho phép dấu bằng. -/
def SequenceMonotonic (u : ℕ → ℝ) : Prop := SequenceIncreasing u ∨ SequenceDecreasing u

/-- Dãy tăng tại các chỉ số n≥1 khi và chỉ khi thỏa `MonotoneOn` trên `Ici 1`. -/
theorem sequenceIncreasing_iff_monotoneOn (u : ℕ → ℝ) :
    SequenceIncreasing u ↔ MonotoneOn u (Ici 1) := by
  constructor
  · intro hu i hi j hj hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (hi.trans hij)).trans (hu j (hi.trans hij))
  · intro hu n hn
    exact hu hn (by omega : 1 ≤ n + 1) (by omega : n ≤ n + 1)

/-- Dãy giảm tại n≥1 khi và chỉ khi thỏa `AntitoneOn` trên `Ici 1`. -/
theorem sequenceDecreasing_iff_antitoneOn (u : ℕ → ℝ) :
    SequenceDecreasing u ↔ AntitoneOn u (Ici 1) := by
  constructor
  · intro hu i hi j hj hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hu j (hi.trans hij)).trans (ih (hi.trans hij))
  · intro hu n hn
    exact hu hn (by omega : 1 ≤ n + 1) (by omega : n ≤ n + 1)

/-- Nhận xét 2.6.3(1): xét hiệu liên tiếp. -/
theorem sequenceIncreasing_iff_nonneg_difference (u : ℕ → ℝ) :
    SequenceIncreasing u ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ u (n + 1) - u n := by
  simp only [SequenceIncreasing, sub_nonneg]

/-- Nhận xét 2.6.3(2): xét tỉ số chỉ khi các số hạng dương. -/
theorem sequenceIncreasing_iff_one_le_ratio (u : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < u n) :
    SequenceIncreasing u ↔ ∀ n : ℕ, 1 ≤ n → 1 ≤ u (n + 1) / u n := by
  constructor
  · intro hu n hn
    exact (le_div_iff₀ (hpos n hn)).mpr (by simpa using hu n hn)
  · intro hu n hn
    simpa using (le_div_iff₀ (hpos n hn)).mp (hu n hn)

/-- Nhận xét 2.6.3(2): tỉ số không vượt 1 cho dãy giảm dương. -/
theorem sequenceDecreasing_iff_ratio_le_one (u : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < u n) :
    SequenceDecreasing u ↔ ∀ n : ℕ, 1 ≤ n → u (n + 1) / u n ≤ 1 := by
  constructor
  · intro hu n hn
    exact (div_le_iff₀ (hpos n hn)).mpr (by simpa using hu n hn)
  · intro hu n hn
    simpa using (div_le_iff₀ (hpos n hn)).mp (hu n hn)

/-- Ví dụ 2.6.2: dãy nghịch đảo giảm ngặt trên miền chỉ số dương. -/
theorem reciprocal_strict_decrease :
    ∀ n : ℕ, 1 ≤ n → 1 / ((n + 1 : ℕ) : ℝ) < 1 / (n : ℝ) := by
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))
    (by positivity : (0 : ℝ) < n)).mpr
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Ví dụ 2.6.2: dãy bình phương tăng ngặt trên miền chỉ số dương. -/
theorem squares_strict_increase :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 2 < ((n + 1 : ℕ) : ℝ) ^ 2 := by
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Ví dụ 2.6.2: dãy nghịch đảo giảm, dãy bình phương tăng. -/
theorem basic_monotone_examples :
    SequenceDecreasing (fun n : ℕ ↦ 1 / (n : ℝ)) ∧
      SequenceIncreasing (fun n : ℕ ↦ (n : ℝ) ^ 2) :=
  ⟨fun n hn ↦ (reciprocal_strict_decrease n hn).le,
    fun n hn ↦ (squares_strict_increase n hn).le⟩


theorem sequenceRangeFromOne_nonempty (u : ℕ → ℝ) : (Section04.sequenceRangeFromOne u).Nonempty :=
  ⟨u 1, ⟨1, by simp, rfl⟩⟩

/-- Định lí 2.6.5(i), Nhận xét 2.6.6: dãy tăng bị chặn trên hội tụ về cận trên bé nhất của tập số hạng. -/
theorem increasing_converges_sup (u : ℕ → ℝ) (hu : SequenceIncreasing u)
    (hb : Section04.SequenceBoundedAbove u) :
    Section03.ConvergesTo u (sSup (Section04.sequenceRangeFromOne u)) ∧
      IsLUB (Section04.sequenceRangeFromOne u) (sSup (Section04.sequenceRangeFromOne u)) := by
  have hs := isLUB_csSup (sequenceRangeFromOne_nonempty u) ((Section04.sequenceBoundedAbove_iff u).mp hb)
  have hm := (sequenceIncreasing_iff_monotoneOn u).mp hu
  refine ⟨?_, hs⟩
  intro ε hε
  obtain ⟨x, hx, hlow, _⟩ := hs.exists_between
    (by linarith : sSup (Section04.sequenceRangeFromOne u) - ε < sSup (Section04.sequenceRangeFromOne u))
  obtain ⟨N, hN, rfl⟩ := hx
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hnpos : 1 ≤ n := hN.trans hn
  have hmono := hm hN hnpos hn
  have hupp := hs.1 ⟨n, hnpos, rfl⟩
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Mọi dãy tăng bị chặn trên hội tụ về một số thực. -/
theorem increasing_bounded_convergent (u : ℕ → ℝ) (hu : SequenceIncreasing u)
    (hb : Section04.SequenceBoundedAbove u) : Section03.IsConvergent u :=
  ⟨_, (increasing_converges_sup u hu hb).1⟩

/-- Định lí 2.6.5(ii) và nhận xét 2.6.6: giới hạn bằng cận dưới lớn nhất. -/
theorem decreasing_converges_inf (u : ℕ → ℝ) (hu : SequenceDecreasing u)
    (hb : Section04.SequenceBoundedBelow u) :
    Section03.ConvergesTo u (sInf (Section04.sequenceRangeFromOne u)) ∧
      IsGLB (Section04.sequenceRangeFromOne u) (sInf (Section04.sequenceRangeFromOne u)) := by
  have hs := isGLB_csInf (sequenceRangeFromOne_nonempty u) ((Section04.sequenceBoundedBelow_iff u).mp hb)
  have hm := (sequenceDecreasing_iff_antitoneOn u).mp hu
  refine ⟨?_, hs⟩
  intro ε hε
  obtain ⟨x, hx, _, hupp⟩ := hs.exists_between
    (by linarith : sInf (Section04.sequenceRangeFromOne u) < sInf (Section04.sequenceRangeFromOne u) + ε)
  obtain ⟨N, hN, rfl⟩ := hx
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hnpos : 1 ≤ n := hN.trans hn
  have hmono := hm hN hnpos hn
  have hlow := hs.1 ⟨n, hnpos, rfl⟩
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Mọi dãy giảm bị chặn dưới hội tụ về một số thực. -/
theorem decreasing_bounded_convergent (u : ℕ → ℝ) (hu : SequenceDecreasing u)
    (hb : Section04.SequenceBoundedBelow u) : Section03.IsConvergent u :=
  ⟨_, (decreasing_converges_inf u hu hb).1⟩

/-- Ví dụ 2.6.4: điều kiện đầu a₁=1 làm dãy Newton này hằng 1. -/
theorem reciprocal_average_recurrence_constant (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n + 1 / u n) / 2) :
    ∀ n : ℕ, 1 ≤ n → u n = 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih => rw [hnext n hn, ih]; norm_num

/-- Ví dụ 2.6.4: dãy hằng 1 là dãy giảm. -/
theorem reciprocal_average_recurrence_decreasing (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n + 1 / u n) / 2) :
    SequenceDecreasing u := by
  intro n hn
  rw [reciprocal_average_recurrence_constant u hfirst hnext n hn,
    reciprocal_average_recurrence_constant u hfirst hnext (n + 1) (by omega)]

/-- Ví dụ 2.6.8: dãy hằng 1 hội tụ về 1. -/
theorem reciprocal_average_recurrence_converges (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n + 1 / u n) / 2) :
    Section03.ConvergesTo u 1 := by
  intro ε hε
  refine ⟨1, le_rfl, ?_⟩
  intro n hn
  simpa only [reciprocal_average_recurrence_constant u hfirst hnext n hn, sub_self, abs_zero] using hε


/-- Ví dụ 2.6.7: dãy truy hồi afin giảm và có cận dưới 1/2. -/
theorem third_affine_recurrence_bounds_decreasing (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n + 1) / 3) :
    (∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 < u n) ∧ SequenceDecreasing u := by
  have hlower : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 < u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfirst]; norm_num
    | succ n hn ih => rw [hnext n hn]; linarith
  refine ⟨hlower, fun n hn ↦ ?_⟩
  rw [hnext n hn]
  have h := hlower n hn
  linarith

/-- Ví dụ 2.6.7: dãy truy hồi afin hội tụ. -/
theorem third_affine_recurrence_converges (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n + 1) / 3) :
    Section03.ConvergesTo u ((1 : ℝ) / 2) := by
  obtain ⟨hlower, hdec⟩ := third_affine_recurrence_bounds_decreasing u hfirst hnext
  obtain ⟨a, ha⟩ := decreasing_bounded_convergent u hdec ⟨1 / 2, fun n hn ↦ (hlower n hn).le⟩
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hshift := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hright : Tendsto (fun n ↦ (u n + 1) / 3) atTop (𝓝 ((a + 1) / 3)) :=
    (ht.add tendsto_const_nhds).div_const 3
  have hleft : Tendsto (fun n ↦ (u n + 1) / 3) atTop (𝓝 a) :=
    hshift.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ hnext n hn⟩)
  have heq : a = (a + 1) / 3 := tendsto_nhds_unique hleft hright
  have haeq : a = (1 : ℝ) / 2 := by linarith
  simpa only [haeq] using ha

/-- Bài 2.6.1(a): n/2ⁿ giảm, với hai số hạng đầu bằng nhau. -/
theorem nat_div_two_pow_decreasing : SequenceDecreasing (fun n : ℕ ↦ (n : ℝ) / 2 ^ n) := by
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)
    (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') (by positivity : (0 : ℝ) ≤ 2 ^ n)]

/-- Bài 2.6.1(b): n/2ⁿ tiến về 0. -/
theorem nat_div_two_pow_converges :
    Section03.ConvergesTo (fun n : ℕ ↦ (n : ℝ) / 2 ^ n) 0 :=
  Section03.convergesTo_iff_tendsto.mpr Section04.nat_div_two_pow_tendsto_zero


/-- Bài 2.6.2(a): 0<aₙ<2 khi a₁=√2. -/
theorem sqrt_add_two_recurrence_bounds (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(u n + 2)) :
    ∀ n : ℕ, 1 ≤ n → 0 < u n ∧ u n < 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [hfirst]
    exact ⟨Real.sqrt_pos.mpr (by norm_num),
      (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        (by norm_num)⟩
  | succ n hn ih =>
    rw [hnext n hn]
    exact ⟨Real.sqrt_pos.mpr (by linarith [ih.1]),
      (Real.sqrt_lt (by linarith [ih.1] : 0 ≤ u n + 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        (by linarith [ih.2])⟩

/-- Bài 2.6.2(b): dãy tăng. -/
theorem sqrt_add_two_recurrence_increasing (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(u n + 2)) : SequenceIncreasing u := by
  intro n hn
  obtain ⟨hl, hu⟩ := sqrt_add_two_recurrence_bounds u hfirst hnext n hn
  rw [hnext n hn]
  apply Real.le_sqrt_of_sq_le
  have hprod := mul_neg_of_neg_of_pos (sub_neg.mpr hu) (by linarith : 0 < u n + 1)
  nlinarith

/-- Bài 2.6.2(c): giới hạn bằng 2. -/
theorem sqrt_add_two_recurrence_converges (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(u n + 2)) : Section03.ConvergesTo u 2 := by
  have hbounds := sqrt_add_two_recurrence_bounds u hfirst hnext
  have hinc := sqrt_add_two_recurrence_increasing u hfirst hnext
  obtain ⟨a, ha⟩ := increasing_bounded_convergent u hinc ⟨2, fun n hn ↦ (hbounds n hn).2.le⟩
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hshift := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hnonneg : 0 ≤ a := Section04.limit_le_of_converges (fun _ ↦ 0) u 0 a
    (Section03.constant_converges 0) ha (fun n hn ↦ (hbounds n hn).1.le)
  have hsq : Tendsto (fun n ↦ u n + 2) atTop (𝓝 (a ^ 2)) := by
    apply (hshift.pow 2).congr'
    refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    dsimp
    rw [hnext n hn, Real.sq_sqrt (by linarith [(hbounds n hn).1] : 0 ≤ u n + 2)]
  have heq : a ^ 2 = a + 2 := tendsto_nhds_unique hsq (ht.add tendsto_const_nhds)
  have hfactor : (a - 2) * (a + 1) = 0 := by nlinarith
  have haeq : a = 2 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  simpa only [haeq] using ha

/-- Cận dùng trong bài 2.6.3: với c>2 và x≥c², (x−c)²>x. -/
theorem shifted_square_gt_self (c : ℝ) (hc : 2 < c) (x : ℝ) (hx : c ^ 2 ≤ x) :
    x < (x - c) ^ 2 := by
  have hc2 : 2 * c < c ^ 2 := by nlinarith
  have hx4 : 4 < x := by nlinarith
  have hhalf : x / 2 ≤ x - c := by linarith
  have hs := mul_self_le_mul_self (by linarith : 0 ≤ x / 2) hhalf
  have hp := mul_pos (by linarith : 0 < x) (by linarith : 0 < x - 4)
  nlinarith

/-- Bài 2.6.3(a): với c>2, dãy tăng và mọi số hạng không nhỏ hơn c². -/
theorem shifted_square_recurrence_increasing (u : ℕ → ℝ) (c : ℝ) (hc : 2 < c)
    (hfirst : u 1 = c ^ 2) (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n - c) ^ 2) :
    (∀ n : ℕ, 1 ≤ n → c ^ 2 ≤ u n) ∧ SequenceIncreasing u := by
  have hlower : ∀ n : ℕ, 1 ≤ n → c ^ 2 ≤ u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfirst]
    | succ n hn ih =>
      rw [hnext n hn]
      exact ih.trans (shifted_square_gt_self c hc (u n) ih).le
  exact ⟨hlower, fun n hn ↦ by
    rw [hnext n hn]
    exact (shifted_square_gt_self c hc (u n) (hlower n hn)).le⟩

/-- Bài 2.6.3(b): dãy không có giới hạn thực hữu hạn. -/
theorem shifted_square_recurrence_divergent (u : ℕ → ℝ) (c : ℝ) (hc : 2 < c)
    (hfirst : u 1 = c ^ 2) (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = (u n - c) ^ 2) :
    Section03.IsDivergent u := by
  rintro ⟨a, ha⟩
  have hlower := (shifted_square_recurrence_increasing u c hc hfirst hnext).1
  have hca : c ^ 2 ≤ a := Section04.limit_le_of_converges (fun _ ↦ c ^ 2) u (c ^ 2) a
    (Section03.constant_converges _) ha hlower
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hshift := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hright : Tendsto (fun n ↦ (u n - c) ^ 2) atTop (𝓝 ((a - c) ^ 2)) :=
    (ht.sub tendsto_const_nhds).pow 2
  have hleft : Tendsto (fun n ↦ (u n - c) ^ 2) atTop (𝓝 a) :=
    hshift.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ hnext n hn⟩)
  exact (shifted_square_gt_self c hc a hca).ne (tendsto_nhds_unique hleft hright)


/-- Bài 2.6.6: dãy bị chặn thỏa uₙ−2⁻ⁿ≤uₙ₊₁ thì hội tụ. -/
theorem convergent_of_bounded_almost_increasing (u : ℕ → ℝ) (hb : Section04.SequenceBounded u)
    (hnext : ∀ n : ℕ, 1 ≤ n → u n - 1 / (2 : ℝ) ^ n ≤ u (n + 1)) :
    Section03.IsConvergent u := by
  let v : ℕ → ℝ := fun n ↦ u n - 2 * ((1 : ℝ) / 2) ^ n
  have hinc : SequenceIncreasing v := by
    intro n hn
    have h := hnext n hn
    have herr : (1 : ℝ) / 2 ^ n = ((1 : ℝ) / 2) ^ n := by simp
    rw [herr] at h
    dsimp [v]
    rw [pow_succ]
    linarith
  obtain ⟨M, hM⟩ := hb.1
  have hvbound : Section04.SequenceBoundedAbove v := by
    refine ⟨M, fun n hn ↦ ?_⟩
    dsimp [v]
    have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    have h := hM n hn
    linarith
  obtain ⟨a, ha⟩ := increasing_bounded_convergent v hinc hvbound
  have hgeo : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  refine ⟨a, Section03.convergesTo_iff_tendsto.mpr ?_⟩
  have hv := Section03.convergesTo_iff_tendsto.mp ha
  have hsum : Tendsto (fun n ↦ v n + 2 * ((1 : ℝ) / 2) ^ n) atTop (𝓝 a) := by
    simpa only [mul_zero, add_zero] using hv.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hgeo)
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by dsimp [v]; ring

/-- Bài 2.6.12: uₙ=1+(u₀−1)2⁻ⁿ. -/
theorem half_affine_recurrence_formula (u : ℕ → ℝ)
    (hnext : ∀ n : ℕ, u (n + 1) = (1 + u n) / 2) :
    ∀ n : ℕ, u n = 1 + (u 0 - 1) * ((1 : ℝ) / 2) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [hnext n, ih, pow_succ]; ring

/-- Bài 2.6.12: mọi giá trị đầu thực x₀ đều cho giới hạn 1. -/
theorem half_affine_recurrence_converges (u : ℕ → ℝ)
    (hnext : ∀ n : ℕ, u (n + 1) = (1 + u n) / 2) : Section03.ConvergesTo u 1 := by
  have hgeo : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  apply Section03.convergesTo_iff_tendsto.mpr
  have ht : Tendsto (fun n ↦ 1 + (u 0 - 1) * ((1 : ℝ) / 2) ^ n) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := u 0 - 1)).mul hgeo)
  exact ht.congr' (Eventually.of_forall fun n ↦ (half_affine_recurrence_formula u hnext n).symm)

/-- Bài 2.6.14(a): truy hồi a₁=2, aₙ₊₁=3+aₙ/2 tăng và không vượt 6. -/
theorem three_add_half_recurrence_bounds (u : ℕ → ℝ) (hfirst : u 1 = 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 3 + u n / 2) :
    (∀ n : ℕ, 1 ≤ n → u n ≤ 6) ∧ SequenceIncreasing u := by
  have hupper : ∀ n : ℕ, 1 ≤ n → u n ≤ 6 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfirst]; norm_num
    | succ n hn ih => rw [hnext n hn]; linarith
  refine ⟨hupper, fun n hn ↦ ?_⟩
  rw [hnext n hn]
  have h := hupper n hn
  linarith

/-- Bài 2.6.14(b): giới hạn bằng 6. -/
theorem three_add_half_recurrence_converges (u : ℕ → ℝ) (hfirst : u 1 = 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 3 + u n / 2) : Section03.ConvergesTo u 6 := by
  obtain ⟨hupper, hinc⟩ := three_add_half_recurrence_bounds u hfirst hnext
  obtain ⟨a, ha⟩ := increasing_bounded_convergent u hinc ⟨6, hupper⟩
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hshift := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hright : Tendsto (fun n ↦ 3 + u n / 2) atTop (𝓝 (3 + a / 2)) :=
    tendsto_const_nhds.add (ht.div_const 2)
  have hleft : Tendsto (fun n ↦ 3 + u n / 2) atTop (𝓝 a) :=
    hshift.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ hnext n hn⟩)
  have heq : a = 3 + a / 2 := tendsto_nhds_unique hleft hright
  have haeq : a = 6 := by linarith
  simpa only [haeq] using ha


/-- Bài 2.6.16: dãy hữu tỉ tăng ngặt hội tụ đến một số thực tùy ý. -/
theorem exists_strictly_increasing_rational_sequence (x : ℝ) :
    ∃ r : ℕ → ℚ, StrictMono r ∧ Section03.ConvergesTo (fun n ↦ (r n : ℝ)) x := by
  obtain ⟨r, hr, _, hlim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto
    Rat.cast_strictMono.monotone x
  exact ⟨r, hr, Section03.convergesTo_iff_tendsto.mpr (by simpa only [Function.comp_def] using hlim)⟩

/-- Bài 2.6.18: dãy vô tỉ tăng ngặt hội tụ đến một số thực tùy ý. -/
theorem exists_strictly_increasing_irrational_sequence (x : ℝ) :
    ∃ s : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → Irrational (s n)) ∧ StrictMono s ∧
      Section03.ConvergesTo s x := by
  obtain ⟨s, hs, hmem, hlim⟩ := dense_irrational.exists_seq_strictMono_tendsto x
  exact ⟨s, fun n _ ↦ (hmem n).2, hs, Section03.convergesTo_iff_tendsto.mpr hlim⟩


/-- Dãy tổng riêng từ k=1 đến n. -/
noncomputable def partialSumFromOne (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, f k


theorem partialSumFromOne_convergent (f : ℕ → ℝ) (hf : ∀ n : ℕ, 0 ≤ f n)
    (hs : Summable f) : Section03.IsConvergent (partialSumFromOne f) := by
  have hinc : SequenceIncreasing (partialSumFromOne f) := by
    intro n hn
    dsimp [partialSumFromOne]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    exact le_add_of_nonneg_right (hf (n + 1))
  have hb : Section04.SequenceBoundedAbove (partialSumFromOne f) :=
    ⟨∑' n, f n, fun n _ ↦ hs.sum_le_tsum (Finset.Icc 1 n) (fun i _ ↦ hf i)⟩
  exact increasing_bounded_convergent _ hinc hb

/-- Bài 2.6.4(b): tổng 1+1/2²+…+1/n² hội tụ. -/
theorem reciprocal_square_partial_sums_convergent :
    Section03.IsConvergent (partialSumFromOne (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2)) :=
  partialSumFromOne_convergent _ (fun _ ↦ by positivity)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

/-- Bài 2.6.4(c): tổng riêng 1/kᵏ hội tụ; với k≥2, số hạng không vượt 1/k². -/
theorem reciprocal_self_power_partial_sums_convergent :
    Section03.IsConvergent (partialSumFromOne (fun k : ℕ ↦ 1 / (k : ℝ) ^ k)) := by
  have hs : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hself : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ k) := by
    apply hs.of_norm_bounded_eventually_nat
    refine eventually_atTop.2 ⟨2, fun k hk ↦ ?_⟩
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ) ^ k)]
    exact one_div_le_one_div_of_le (by positivity : 0 < (k : ℝ) ^ 2)
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ k) hk)
  exact partialSumFromOne_convergent _ (fun _ ↦ by positivity) hself


theorem dyadic_tail_sum_formula (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2) ^ k) = 1 - ((1 : ℝ) / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, pow_succ]
    ring

/-- Bài 2.6.4(a): tích của (1+1/2^k), k=1,…,n. -/
noncomputable def dyadicPerturbationProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (1 + 1 / (2 : ℝ) ^ k)

/-- Bài 2.6.4(a): tích tăng và không vượt exp(1). -/
theorem dyadicPerturbationProduct_increasing_bounded :
    SequenceIncreasing dyadicPerturbationProduct ∧ Section04.SequenceBoundedAbove dyadicPerturbationProduct := by
  constructor
  · intro n hn
    dsimp [dyadicPerturbationProduct]
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hprod : 0 ≤ ∏ k ∈ Finset.Icc 1 n, (1 + 1 / (2 : ℝ) ^ k) :=
      Finset.prod_nonneg (fun _ _ ↦ by positivity)
    have hp : 0 ≤ 1 / (2 : ℝ) ^ (n + 1) := by positivity
    nlinarith
  · refine ⟨Real.exp 1, fun n hn ↦ ?_⟩
    calc
      dyadicPerturbationProduct n ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, 1 / (2 : ℝ) ^ k) :=
        Real.prod_one_add_le_exp_sum _ (fun _ ↦ by positivity)
      _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hsum := dyadic_tail_sum_formula n
        have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
        have hle : (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2) ^ k) ≤ 1 := by linarith
        simpa only [one_div, inv_pow] using hle

/-- Bài 2.6.4(a): dãy tích hữu hạn hội tụ. -/
theorem dyadicPerturbationProduct_convergent : Section03.IsConvergent dyadicPerturbationProduct :=
  increasing_bounded_convergent _ dyadicPerturbationProduct_increasing_bounded.1
    dyadicPerturbationProduct_increasing_bounded.2

/-- Bài 2.6.5: tích các căn bậc 2,4,…,2ⁿ của 2. -/
noncomputable def dyadicRootProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (2 : ℝ) ^ (((2 : ℝ) ^ k)⁻¹)

/-- Bài 2.6.5: tích các căn bằng 2^(1−2⁻ⁿ). -/
theorem dyadicRootProduct_formula (n : ℕ) :
    dyadicRootProduct n = (2 : ℝ) ^ (1 - ((1 : ℝ) / 2) ^ n) := by
  induction n with
  | zero => simp [dyadicRootProduct]
  | succ n ih =>
    dsimp [dyadicRootProduct] at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    have hexp : ((2 : ℝ) ^ (n + 1))⁻¹ = ((1 : ℝ) / 2) ^ (n + 1) := by simp
    rw [hexp, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [pow_succ]
    ring

/-- Bài 2.6.5: giới hạn tích căn bằng 2. -/
theorem dyadicRootProduct_converges : Section03.ConvergesTo dyadicRootProduct 2 := by
  have hgeo : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hexp : Tendsto (fun n : ℕ ↦ 1 - ((1 : ℝ) / 2) ^ n) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hgeo
  have ht : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (1 - ((1 : ℝ) / 2) ^ n)) atTop (𝓝 2) := by
    simpa only [Real.rpow_one] using
      (tendsto_const_nhds (x := (2 : ℝ))).rpow hexp (Or.inl (by norm_num : (2 : ℝ) ≠ 0))
  exact Section03.convergesTo_iff_tendsto.mpr
    (ht.congr' (Eventually.of_forall fun n ↦ (dyadicRootProduct_formula n).symm))


/-- Bài 2.6.13(a,b): dãy giảm và aₙ≤2. -/
theorem quadratic_seven_recurrence_bounds_decreasing (u : ℕ → ℝ) (hfirst : u 1 = 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → 7 * u (n + 1) = 2 * (u n) ^ 2 + 3) :
    (∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 < u n ∧ u n ≤ 2) ∧ SequenceDecreasing u := by
  have hbounds : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 < u n ∧ u n ≤ 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfirst]; norm_num
    | succ n hn ih =>
      have h := hnext n hn
      have hl := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) ih.1
      have hu := mul_self_le_mul_self (by linarith [ih.1] : 0 ≤ u n) ih.2
      constructor <;> nlinarith
  refine ⟨hbounds, fun n hn ↦ ?_⟩
  obtain ⟨hl, hu⟩ := hbounds n hn
  have hp := mul_neg_of_pos_of_neg (by linarith : 0 < u n - 1 / 2)
    (by linarith : u n - 3 < 0)
  have h := hnext n hn
  nlinarith

/-- Bài 2.6.13(a): 1/2<aₙ<3. -/
theorem quadratic_seven_recurrence_half_lt_and_lt_three (u : ℕ → ℝ) (hfirst : u 1 = 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → 7 * u (n + 1) = 2 * (u n) ^ 2 + 3) :
    ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 < u n ∧ u n < 3 := by
  intro n hn
  obtain ⟨hl, hu⟩ := (quadratic_seven_recurrence_bounds_decreasing u hfirst hnext).1 n hn
  exact ⟨hl, by linarith⟩

/-- Bài 2.6.13(c): giới hạn bằng 1/2. -/
theorem quadratic_seven_recurrence_converges (u : ℕ → ℝ) (hfirst : u 1 = 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → 7 * u (n + 1) = 2 * (u n) ^ 2 + 3) :
    Section03.ConvergesTo u ((1 : ℝ) / 2) := by
  obtain ⟨hbounds, hdec⟩ := quadratic_seven_recurrence_bounds_decreasing u hfirst hnext
  obtain ⟨a, ha⟩ := decreasing_bounded_convergent u hdec ⟨1 / 2, fun n hn ↦ (hbounds n hn).1.le⟩
  have haup : a ≤ 2 := Section04.limit_le_of_converges u (fun _ ↦ 2) a 2 ha
    (Section03.constant_converges 2) (fun n hn ↦ (hbounds n hn).2)
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hshift := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hright : Tendsto (fun n ↦ 2 * (u n) ^ 2 + 3) atTop (𝓝 (2 * a ^ 2 + 3)) :=
    ((ht.pow 2).const_mul 2).add tendsto_const_nhds
  have hleft : Tendsto (fun n ↦ 2 * (u n) ^ 2 + 3) atTop (𝓝 (7 * a)) := by
    apply (hshift.const_mul 7).congr'
    refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    exact hnext n hn
  have heq : 7 * a = 2 * a ^ 2 + 3 := tendsto_nhds_unique hleft hright
  have hfactor : (2 * a - 1) * (a - 3) = 0 := by nlinarith
  have haeq : a = (1 : ℝ) / 2 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  simpa only [haeq] using ha

/-- Ví dụ 2.6.9: giới hạn dãy định nghĩa e bằng exp(1). -/
theorem euler_sequence_converges :
    Section03.ConvergesTo (fun n : ℕ ↦ (1 + 1 / (n : ℝ)) ^ n) (Real.exp 1) := by
  simpa only [one_div] using
    Section03.convergesTo_iff_tendsto.mpr (Real.tendsto_one_add_div_pow_exp (1 : ℝ))

/-- Ví dụ 2.6.9: mọi số hạng tại n≥1 nhỏ hơn 3. -/
theorem euler_sequence_lt_three :
    ∀ n : ℕ, 1 ≤ n → (1 + 1 / (n : ℝ)) ^ n < 3 := by
  intro n hn
  exact lt_of_le_of_lt (by simpa only [one_div] using Real.one_add_inv_pow_le_exp (n := n))
    Real.exp_one_lt_three

/-- Ví dụ 2.6.9: khoảng hữu tỉ xác nhận 12 chữ số sau dấu phẩy của e. -/
theorem euler_printed_decimal_interval :
    (2718281828459 : ℝ) / 10 ^ 12 < Real.exp 1 ∧
      Real.exp 1 < (2718281828460 : ℝ) / 10 ^ 12 := by
  have h := abs_le.mp Real.exp_one_near_20
  have hl : (2718281828459 : ℝ) / 10 ^ 12 <
      (363916618873 : ℝ) / 133877442384 - 1 / 10 ^ 20 := by norm_num
  have hu : (363916618873 : ℝ) / 133877442384 + 1 / 10 ^ 20 <
      (2718281828460 : ℝ) / 10 ^ 12 := by norm_num
  constructor <;> linarith [h.1, h.2]


/-- Dòng 1946: dấu < trong cận hình học sai tại n=1. -/
theorem euler_printed_strict_bound_counterexample :
    (1 + 1 / (1 : ℝ)) ^ (1 : ℕ) = 2 ∧
      ¬ ((1 + 1 / (1 : ℝ)) ^ (1 : ℕ) <
        2 + ∑ k ∈ Finset.Icc 1 0, ((1 : ℝ) / 2) ^ k) := by
  norm_num

end calculus.Chapter02.Section06
