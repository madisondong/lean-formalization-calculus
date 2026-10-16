import calculus.Chapter03.Section02OneSided
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
§3.2 — giới hạn vô hạn

Nguồn: dòng 1766–1971.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided


theorem tendsto_nhdsWithin_atTop_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    Tendsto f (𝓝[D] a) atTop ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ D, |x - a| < δ → M < f x := by
  rw [tendsto_atTop]
  constructor
  · intro h M
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp (h (M + 1))
    refine ⟨δ, hδ, fun x hx hdist ↦ ?_⟩
    have hh := hd ⟨by simpa only [Metric.mem_ball, Real.dist_eq] using hdist, hx⟩
    exact lt_of_lt_of_le (by linarith : M < M + 1) hh
  · intro h M
    obtain ⟨δ, hδ, hd⟩ := h M
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    exact (hd x hx.2 (by simpa only [Metric.mem_ball, Real.dist_eq] using hx.1)).le

theorem tendsto_nhdsWithin_atBot_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    Tendsto f (𝓝[D] a) atBot ↔
      ∀ m : ℝ, ∃ δ > 0, ∀ x ∈ D, |x - a| < δ → f x < m := by
  rw [tendsto_atBot]
  constructor
  · intro h m
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp (h (m - 1))
    refine ⟨δ, hδ, fun x hx hdist ↦ ?_⟩
    have hh := hd ⟨by simpa only [Metric.mem_ball, Real.dist_eq] using hdist, hx⟩
    exact lt_of_le_of_lt hh (by linarith : m - 1 < m)
  · intro h m
    obtain ⟨δ, hδ, hd⟩ := h m
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    exact (hd x hx.2 (by simpa only [Metric.mem_ball, Real.dist_eq] using hx.1)).le

/-- Định nghĩa 3.2.28 và 3.2.30: giới hạn vô hạn một phía tại điểm tụ tương ứng. -/
def DomainRightTopLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  RightAccumulationPointOf D a ∧ Tendsto f (𝓝[D ∩ Ioi a] a) atTop

def DomainRightBotLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  RightAccumulationPointOf D a ∧ Tendsto f (𝓝[D ∩ Ioi a] a) atBot

def DomainLeftTopLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  LeftAccumulationPointOf D a ∧ Tendsto f (𝓝[D ∩ Iio a] a) atTop

def DomainLeftBotLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  LeftAccumulationPointOf D a ∧ Tendsto f (𝓝[D ∩ Iio a] a) atBot

/-- Định nghĩa 3.2.32: giới hạn vô hạn hai phía tại điểm tụ. -/
def DomainPointTopLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  AccumulationPointOf D a ∧ Tendsto f (𝓝[D \ {a}] a) atTop

def DomainPointBotLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  AccumulationPointOf D a ∧ Tendsto f (𝓝[D \ {a}] a) atBot

/-- Định nghĩa 3.2.28(a): điều kiện trên khoảng với bất đẳng thức ngặt. -/
theorem domainRightTopLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainRightTopLimit D f a ↔ RightAccumulationPointOf D a ∧
      ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → M < f x := by
  rw [DomainRightTopLimit, tendsto_nhdsWithin_atTop_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h M <;> obtain ⟨δ, hδ, hd⟩ := h M <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hl hr
    exact hd x ⟨hx, hl⟩ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · intro x hx hdistance
    exact hd x hx.1 hx.2 (by linarith [(abs_lt.mp hdistance).2])

theorem domainRightBotLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainRightBotLimit D f a ↔ RightAccumulationPointOf D a ∧
      ∀ m : ℝ, ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → f x < m := by
  rw [DomainRightBotLimit, tendsto_nhdsWithin_atBot_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h m <;> obtain ⟨δ, hδ, hd⟩ := h m <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hl hr
    exact hd x ⟨hx, hl⟩ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · intro x hx hdistance
    exact hd x hx.1 hx.2 (by linarith [(abs_lt.mp hdistance).2])

theorem domainLeftTopLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainLeftTopLimit D f a ↔ LeftAccumulationPointOf D a ∧
      ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ D, a - δ < x → x < a → M < f x := by
  rw [DomainLeftTopLimit, tendsto_nhdsWithin_atTop_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h M <;> obtain ⟨δ, hδ, hd⟩ := h M <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hl hr
    exact hd x ⟨hx, hr⟩ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · intro x hx hdistance
    exact hd x hx.1 (by linarith [(abs_lt.mp hdistance).1]) hx.2

theorem domainLeftBotLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainLeftBotLimit D f a ↔ LeftAccumulationPointOf D a ∧
      ∀ m : ℝ, ∃ δ > 0, ∀ x ∈ D, a - δ < x → x < a → f x < m := by
  rw [DomainLeftBotLimit, tendsto_nhdsWithin_atBot_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h m <;> obtain ⟨δ, hδ, hd⟩ := h m <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hl hr
    exact hd x ⟨hx, hr⟩ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · intro x hx hdistance
    exact hd x hx.1 (by linarith [(abs_lt.mp hdistance).1]) hx.2

theorem domainPointTopLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainPointTopLimit D f a ↔ AccumulationPointOf D a ∧
      ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ D, 0 < |x - a| → |x - a| < δ → M < f x := by
  rw [DomainPointTopLimit, tendsto_nhdsWithin_atTop_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h M <;> obtain ⟨δ, hδ, hd⟩ := h M <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hn hdist
    exact hd x ⟨hx, by simpa only [mem_singleton_iff] using sub_ne_zero.mp (abs_pos.mp hn)⟩ hdist
  · intro x hx hdist
    exact hd x hx.1 (abs_pos.mpr (sub_ne_zero.mpr (by simpa using hx.2))) hdist

theorem domainPointBotLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainPointBotLimit D f a ↔ AccumulationPointOf D a ∧
      ∀ m : ℝ, ∃ δ > 0, ∀ x ∈ D, 0 < |x - a| → |x - a| < δ → f x < m := by
  rw [DomainPointBotLimit, tendsto_nhdsWithin_atBot_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h m <;> obtain ⟨δ, hδ, hd⟩ := h m <;> refine ⟨δ, hδ, ?_⟩
  · intro x hx hn hdist
    exact hd x ⟨hx, by simpa only [mem_singleton_iff] using sub_ne_zero.mp (abs_pos.mp hn)⟩ hdist
  · intro x hx hdist
    exact hd x hx.1 (abs_pos.mpr (sub_ne_zero.mpr (by simpa using hx.2))) hdist

/-- Mệnh đề 3.2.36(i): nghịch đảo lũy thừa chẵn tiến đến +∞ tại điểm kì dị. -/
theorem reciprocal_even_power_point_top (a : ℝ) (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    DomainPointTopLimit (univ \ {a}) (fun x ↦ 1 / (x - a) ^ n) a := by
  refine ⟨univ_diff_accumulation a, ?_⟩
  have hd : (univ \ {a}) \ {a} = ({a}ᶜ : Set ℝ) := by ext x; simp
  rw [hd]
  have hn0 : n ≠ 0 := by omega
  have hbase : Tendsto (fun x : ℝ ↦ x - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ ↦ x - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using
      (show ContinuousAt (fun x : ℝ ↦ x - a) a from hc.continuousAt).tendsto
  have hzero : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[≠] a) (𝓝 0) := by
    simpa only [zero_pow hn0] using (hbase.pow n).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ x in 𝓝[≠] a, 0 < (x - a) ^ n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact he.pow_pos (sub_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using hx))
  have hpow : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[≠] a) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  exact hpow.inv_tendsto_nhdsGT_zero.congr fun x ↦ by simp only [Pi.inv_apply, one_div]


theorem reciprocal_power_right_top (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    DomainRightTopLimit (univ \ {a}) (fun x ↦ 1 / (x - a) ^ n) a := by
  refine ⟨rightAccumulation_univ_diff a, ?_⟩
  have hd : (univ \ {a}) ∩ Ioi a = Ioi a := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff, mem_univ, mem_singleton_iff, mem_Ioi, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_gt h, h⟩⟩
  rw [hd]
  have hn0 : n ≠ 0 := by omega
  have hbase : Tendsto (fun x : ℝ ↦ x - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ ↦ x - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using
      (show ContinuousAt (fun x : ℝ ↦ x - a) a from hc.continuousAt).tendsto
  have hzero : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[>] a) (𝓝 0) := by
    simpa only [zero_pow hn0] using (hbase.pow n).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ x in 𝓝[>] a, 0 < (x - a) ^ n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.mpr hx) n
  have hpow : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[>] a) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  exact hpow.inv_tendsto_nhdsGT_zero.congr fun x ↦ by simp only [Pi.inv_apply, one_div]

/-- Mệnh đề 3.2.36(ii): nghịch đảo lũy thừa lẻ tiến đến −∞ từ bên trái. -/
theorem reciprocal_odd_power_left_bot (a : ℝ) (n : ℕ) (hn : 1 ≤ n) (ho : Odd n) :
    DomainLeftBotLimit (univ \ {a}) (fun x ↦ 1 / (x - a) ^ n) a := by
  refine ⟨leftAccumulation_univ_diff a, ?_⟩
  have hd : (univ \ {a}) ∩ Iio a = Iio a := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff, mem_univ, mem_singleton_iff, mem_Iio, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_lt h, h⟩⟩
  rw [hd]
  have hn0 : n ≠ 0 := by omega
  have hbase : Tendsto (fun x : ℝ ↦ x - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ ↦ x - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using
      (show ContinuousAt (fun x : ℝ ↦ x - a) a from hc.continuousAt).tendsto
  have hzero : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[<] a) (𝓝 0) := by
    simpa only [zero_pow hn0] using (hbase.pow n).mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ x in 𝓝[<] a, (x - a) ^ n < 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ho.pow_neg_iff.mpr (sub_neg.mpr hx)
  have hpow : Tendsto (fun x : ℝ ↦ (x - a) ^ n) (𝓝[<] a) (𝓝[<] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hneg⟩
  exact hpow.inv_tendsto_nhdsLT_zero.congr fun x ↦ by simp only [Pi.inv_apply, one_div]

/-- Ví dụ 3.2.29, 3.2.31 và 3.2.33: các trường hợp n=1 và n=2. -/
theorem reciprocal_right_top : DomainRightTopLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 := by
  simpa only [sub_zero, pow_one] using reciprocal_power_right_top 0 1 le_rfl

theorem reciprocal_left_bot : DomainLeftBotLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 := by
  simpa only [sub_zero, pow_one] using reciprocal_odd_power_left_bot 0 1 le_rfl (by decide)

theorem reciprocal_square_point_top : DomainPointTopLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x ^ 2) 0 := by
  simpa only [sub_zero] using reciprocal_even_power_point_top 0 2 (by omega) (by decide)

/-- Dòng 1783: hàm nghịch đảo bác bỏ công thức lượng từ đã in. -/
theorem printed_right_top_formula_false :
    DomainRightTopLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 ∧
      ¬ (∀ M : ℝ, ∃ δ > 0, ∀ x ∈ univ \ {(0 : ℝ)},
        0 < x → x < x + δ → M < 1 / x) := by
  refine ⟨reciprocal_right_top, ?_⟩
  intro h
  obtain ⟨δ, hδ, hh⟩ := h 2
  have he := hh 1 (by simp) zero_lt_one (by linarith)
  norm_num at he


theorem domainRightTopLimit_iff_positive_thresholds {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainRightTopLimit D f a ↔ RightAccumulationPointOf D a ∧
      ∀ M > 0, ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → M < f x := by
  rw [domainRightTopLimit_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · exact fun h M _ ↦ h M
  · intro h M
    obtain ⟨δ, hδ, hd⟩ := h (max M 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    exact ⟨δ, hδ, fun x hx hl hr ↦ lt_of_le_of_lt (le_max_left _ _) (hd x hx hl hr)⟩

theorem domainRightBotLimit_iff_negative_thresholds {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} :
    DomainRightBotLimit D f a ↔ RightAccumulationPointOf D a ∧
      ∀ m < 0, ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → f x < m := by
  rw [domainRightBotLimit_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · exact fun h m _ ↦ h m
  · intro h m
    obtain ⟨δ, hδ, hd⟩ := h (min m (-1)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    exact ⟨δ, hδ, fun x hx hl hr ↦ lt_of_lt_of_le (hd x hx hl hr) (min_le_left _ _)⟩


theorem punctured_domain_eq_sides (D : Set ℝ) (a : ℝ) :
    D \ {a} = (D ∩ Iio a) ∪ (D ∩ Ioi a) := by
  ext x
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff, mem_Iio, mem_Ioi]
  constructor
  · rintro ⟨hx, hn⟩
    exact (lt_or_gt_of_ne hn).imp (fun h ↦ ⟨hx, h⟩) (fun h ↦ ⟨hx, h⟩)
  · rintro (⟨hx, hl⟩ | ⟨hx, hr⟩)
    · exact ⟨hx, ne_of_lt hl⟩
    · exact ⟨hx, ne_of_gt hr⟩

/-- Mệnh đề 3.2.34: giới hạn vô hạn hai phía tương đương hai giới hạn một phía cùng dấu. -/
theorem domainPointTopLimit_iff_sides {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hl : LeftAccumulationPointOf D a) (hr : RightAccumulationPointOf D a) :
    DomainPointTopLimit D f a ↔ DomainLeftTopLimit D f a ∧ DomainRightTopLimit D f a := by
  have ha := accumulationPointOf_iff_left_or_right.mpr (Or.inl hl)
  simp only [DomainPointTopLimit, DomainLeftTopLimit, DomainRightTopLimit,
    ha, hl, hr, true_and, punctured_domain_eq_sides, nhdsWithin_union, tendsto_sup]

/-- dòng 1858: kết quả tương ứng cho giới hạn bằng −∞. -/
theorem domainPointBotLimit_iff_sides {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hl : LeftAccumulationPointOf D a) (hr : RightAccumulationPointOf D a) :
    DomainPointBotLimit D f a ↔ DomainLeftBotLimit D f a ∧ DomainRightBotLimit D f a := by
  have ha := accumulationPointOf_iff_left_or_right.mpr (Or.inl hl)
  simp only [DomainPointBotLimit, DomainLeftBotLimit, DomainRightBotLimit,
    ha, hl, hr, true_and, punctured_domain_eq_sides, nhdsWithin_union, tendsto_sup]

/-- Ví dụ 3.2.35: không có giới hạn hai phía hữu hạn, bằng +∞ hoặc bằng −∞. -/
theorem reciprocal_no_point_limits :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 ∧
      ¬ DomainPointTopLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 ∧
      ¬ DomainPointBotLimit (univ \ {(0 : ℝ)}) (fun x ↦ 1 / x) 0 := by
  have hLset : (univ \ {(0 : ℝ)}) ∩ Iio 0 = Iio 0 := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff, mem_univ, mem_singleton_iff, mem_Iio, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_lt h, h⟩⟩
  have hRset : (univ \ {(0 : ℝ)}) ∩ Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff, mem_univ, mem_singleton_iff, mem_Ioi, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_gt h, h⟩⟩
  have hleft := reciprocal_left_bot.2
  have hright := reciprocal_right_top.2
  rw [hLset] at hleft
  rw [hRset] at hright
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    have hl := ((domainLimit_iff_left_right (leftAccumulation_univ_diff 0)
      (rightAccumulation_univ_diff 0)).mp hL).1
    have hf := (domainLeftLimit_iff_tendsto (leftAccumulation_univ_diff 0)).mp hl
    rw [hLset] at hf
    exact not_tendsto_nhds_of_tendsto_atBot hleft L hf
  · intro h
    have hh := ((domainPointTopLimit_iff_sides (leftAccumulation_univ_diff 0)
      (rightAccumulation_univ_diff 0)).mp h).1.2
    rw [hLset] at hh
    exact hleft.not_tendsto disjoint_atBot_atTop hh
  · intro h
    have hh := ((domainPointBotLimit_iff_sides (leftAccumulation_univ_diff 0)
      (rightAccumulation_univ_diff 0)).mp h).2.2
    rw [hRset] at hh
    exact hright.not_tendsto disjoint_atTop_atBot hh

/-- Định nghĩa 3.2.37: giới hạn hữu hạn tại +∞, kèm điều kiện miền không bị chặn trên. -/
def DomainAtTopLimit (D : Set ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ¬ BddAbove D ∧ ∀ ε > 0, ∃ M : ℝ, ∀ x ∈ D, M < x → |f x - L| < ε

/-- Định nghĩa 3.2.37: giới hạn hữu hạn tại −∞, kèm điều kiện miền không bị chặn dưới. -/
def DomainAtBotLimit (D : Set ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ¬ BddBelow D ∧ ∀ ε > 0, ∃ M : ℝ, ∀ x ∈ D, x < M → |f x - L| < ε

theorem domainAtTopLimit_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ¬ BddAbove D) : DomainAtTopLimit D f L ↔ Tendsto f (atTop ⊓ 𝓟 D) (𝓝 L) := by
  simp only [DomainAtTopLimit, hD, not_false_eq_true, true_and, Metric.tendsto_nhds, Real.dist_eq,
    eventually_inf_principal]
  constructor
  · intro h ε hε
    obtain ⟨M, hd⟩ := h ε hε
    exact eventually_atTop.mpr ⟨M + 1, fun x hx hD ↦ hd x hD (by linarith)⟩
  · intro h ε hε
    obtain ⟨M, hd⟩ := eventually_atTop.mp (h ε hε)
    exact ⟨M, fun x hx hMx ↦ hd x hMx.le hx⟩

theorem domainAtBotLimit_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ¬ BddBelow D) : DomainAtBotLimit D f L ↔ Tendsto f (atBot ⊓ 𝓟 D) (𝓝 L) := by
  simp only [DomainAtBotLimit, hD, not_false_eq_true, true_and, Metric.tendsto_nhds, Real.dist_eq,
    eventually_inf_principal]
  constructor
  · intro h ε hε
    obtain ⟨M, hd⟩ := h ε hε
    exact eventually_atBot.mpr ⟨M - 1, fun x hx hD ↦ hd x hD (by linarith)⟩
  · intro h ε hε
    obtain ⟨M, hd⟩ := eventually_atBot.mp (h ε hε)
    exact ⟨M, fun x hx hxM ↦ hd x hxM.le hx⟩

/-- Định nghĩa 3.2.40: giới hạn bằng +∞ tại +∞ trên miền không bị chặn trên. -/
def DomainAtTopTopLimit (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ¬ BddAbove D ∧ Tendsto f (atTop ⊓ 𝓟 D) atTop

/-- Định nghĩa 3.2.40: giới hạn bằng −∞ tại +∞. -/
def DomainAtTopBotLimit (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ¬ BddAbove D ∧ Tendsto f (atTop ⊓ 𝓟 D) atBot

theorem domainAtTopTopLimit_iff {D : Set ℝ} {f : ℝ → ℝ} :
    DomainAtTopTopLimit D f ↔ ¬ BddAbove D ∧
      ∀ A > 0, ∃ B > 0, ∀ x ∈ D, B < x → A < f x := by
  rw [DomainAtTopTopLimit, tendsto_atTop]
  refine and_congr_right fun _ ↦ ?_
  simp only [eventually_inf_principal]
  constructor
  · intro h A _
    obtain ⟨M, hd⟩ := eventually_atTop.mp (h (A + 1))
    refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx hBx ↦ ?_⟩
    exact lt_of_lt_of_le (by linarith : A < A + 1)
      (hd x (le_trans (le_max_left _ _) hBx.le) hx)
  · intro h M
    obtain ⟨B, _, hd⟩ := h (max M 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    exact eventually_atTop.mpr ⟨B + 1, fun x hx hD ↦
      le_trans (le_max_left _ _) (hd x hD (by linarith)).le⟩

theorem domainAtTopBotLimit_iff {D : Set ℝ} {f : ℝ → ℝ} :
    DomainAtTopBotLimit D f ↔ ¬ BddAbove D ∧
      ∀ A > 0, ∃ B > 0, ∀ x ∈ D, B < x → f x < -A := by
  rw [DomainAtTopBotLimit, tendsto_atBot]
  refine and_congr_right fun _ ↦ ?_
  simp only [eventually_inf_principal]
  constructor
  · intro h A _
    obtain ⟨M, hd⟩ := eventually_atTop.mp (h (-A - 1))
    refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx hBx ↦ ?_⟩
    exact lt_of_le_of_lt (hd x (le_trans (le_max_left _ _) hBx.le) hx)
      (by linarith : -A - 1 < -A)
  · intro h m
    obtain ⟨B, _, hd⟩ := h (max (-m) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    refine eventually_atTop.mpr ⟨B + 1, fun x hx hD ↦ ?_⟩
    have hh := hd x hD (by linarith : B < x)
    have hm := le_max_left (-m) (1 : ℝ)
    linarith


theorem reciprocal_sqrt_atBot_limit :
    DomainAtBotLimit (Iio (1 : ℝ)) (fun x ↦ 1 / Real.sqrt (1 - x)) 0 := by
  have hD : ¬ BddBelow (Iio (1 : ℝ)) := by
    rintro ⟨m, hm⟩
    have hx : min m 1 - 1 < 1 := by linarith [min_le_right m (1 : ℝ)]
    have hh := hm hx
    linarith [min_le_left m (1 : ℝ)]
  apply (domainAtBotLimit_iff_tendsto hD).mpr
  have hlin : Tendsto (fun x : ℝ ↦ 1 - x) atBot atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_left atBot (1 : ℝ) tendsto_neg_atBot_atTop
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.sqrt (1 - x)) atBot atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hlin
  have hinv : Tendsto (fun x : ℝ ↦ 1 / Real.sqrt (1 - x)) atBot (𝓝 0) := by
    exact hsqrt.inv_tendsto_atTop.congr fun x ↦ by simp only [Pi.inv_apply, one_div]
  exact hinv.mono_left inf_le_left

/-- Ví dụ 3.2.39: giới hạn của phân thức tại vô cực. -/
theorem quadratic_ratio_atTop_limit :
    DomainAtTopLimit univ (fun x ↦ 3 * x ^ 2 / (2 * x ^ 2 + 1)) (3 / 2) := by
  apply (domainAtTopLimit_iff_tendsto not_bddAbove_univ).mpr
  have hi : Tendsto (fun x : ℝ ↦ 1 / x ^ 2) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).inv_tendsto_atTop.congr
      fun x ↦ by simp only [Pi.inv_apply, one_div]
  have hr : Tendsto (fun x : ℝ ↦ 3 / (2 + 1 / x ^ 2)) atTop (𝓝 (3 / 2)) := by
    have hh := (tendsto_const_nhds (x := (3 : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).add hi) (by norm_num : (2 : ℝ) + 0 ≠ 0)
    change Tendsto (fun x : ℝ ↦ 3 / (2 + 1 / x ^ 2)) atTop (𝓝 (3 / (2 + 0))) at hh
    simpa only [add_zero] using hh
  have heq : (fun x : ℝ ↦ 3 / (2 + 1 / x ^ 2)) =ᶠ[atTop]
      (fun x ↦ 3 * x ^ 2 / (2 * x ^ 2 + 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hd : 2 * x ^ 2 + 1 ≠ 0 := by positivity
    field_simp [hx0, hd]
  exact (hr.congr' heq).mono_left inf_le_left

/-- Ví dụ 3.2.41(a): giới hạn bằng +∞ trên miền xác định của căn bậc hai. -/
theorem sqrt_atTop_top_limit : DomainAtTopTopLimit (Ici (0 : ℝ)) Real.sqrt := by
  have hD : ¬ BddAbove (Ici (0 : ℝ)) := by
    rintro ⟨m, hm⟩
    have hx : 0 ≤ max m 0 + 1 := by linarith [le_max_right m (0 : ℝ)]
    have hh := hm hx
    linarith [le_max_left m (0 : ℝ)]
  refine ⟨hD, ?_⟩
  have h : Tendsto Real.sqrt atTop atTop := by
    change Tendsto (fun x : ℝ ↦ Real.sqrt x) atTop atTop
    simpa only [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))
  exact h.mono_left inf_le_left

/-- Ví dụ 3.2.41(b): giới hạn của aˣ tại +∞, với a>1. -/
theorem real_power_atTop_top_limit {a : ℝ} (ha : 1 < a) :
    DomainAtTopTopLimit univ (fun x ↦ a ^ x) :=
  ⟨not_bddAbove_univ, (tendsto_rpow_atTop_of_base_gt_one a ha).mono_left inf_le_left⟩

end calculus.Chapter03.Section02Infinite
