import calculus.Chapter03.Section02
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
§3.2 — giới hạn hữu hạn một phía

Nguồn: dòng 1670–1765.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02 calculus.Chapter02.Section03

/-- Định nghĩa 3.2.19: giới hạn trái, kèm giả thiết điểm tụ trái. -/
def DomainLeftLimit (D : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  LeftAccumulationPointOf D a ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, a - δ < x → x < a → |f x - L| < ε


def DomainRightLimit (D : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  RightAccumulationPointOf D a ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → |f x - L| < ε

theorem leftAccumulation_iff_restricted {D : Set ℝ} {a : ℝ} :
    LeftAccumulationPointOf D a ↔ AccumulationPointOf (D ∩ Iio a) a := by
  constructor
  · intro h δ hδ
    obtain ⟨x, hx, hl, hr⟩ := h δ hδ
    exact ⟨x, ⟨hx, hr⟩, ne_of_lt hr, hl, by linarith⟩
  · intro h δ hδ
    obtain ⟨x, hx, _, hl, _⟩ := h δ hδ
    exact ⟨x, hx.1, hl, hx.2⟩

theorem rightAccumulation_iff_restricted {D : Set ℝ} {a : ℝ} :
    RightAccumulationPointOf D a ↔ AccumulationPointOf (D ∩ Ioi a) a := by
  constructor
  · intro h δ hδ
    obtain ⟨x, hx, hl, hr⟩ := h δ hδ
    exact ⟨x, ⟨hx, hl⟩, ne_of_gt hl, by linarith, hr⟩
  · intro h δ hδ
    obtain ⟨x, hx, _, _, hr⟩ := h δ hδ
    exact ⟨x, hx.1, hx.2, hr⟩


theorem domainLeftLimit_iff_restricted {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ} :
    DomainLeftLimit D f a L ↔ DomainLimit (D ∩ Iio a) f a L := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨leftAccumulation_iff_restricted.mp ha, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hD _ hdist ↦ hx x hD.1 ?_ hD.2⟩
    linarith [(abs_lt.mp hdist).1]
  · rintro ⟨ha, h⟩
    refine ⟨leftAccumulation_iff_restricted.mpr ha, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hD hl hr ↦ hx x ⟨hD, hr⟩ ?_ ?_⟩
    · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hr))
    · exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem domainRightLimit_iff_restricted {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ} :
    DomainRightLimit D f a L ↔ DomainLimit (D ∩ Ioi a) f a L := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨rightAccumulation_iff_restricted.mp ha, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hD _ hdist ↦ hx x hD.1 hD.2 ?_⟩
    linarith [(abs_lt.mp hdist).2]
  · rintro ⟨ha, h⟩
    refine ⟨rightAccumulation_iff_restricted.mpr ha, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hD hl hr ↦ hx x ⟨hD, hl⟩ ?_ ?_⟩
    · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hl))
    · exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem domainLeftLimit_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (ha : LeftAccumulationPointOf D a) :
    DomainLeftLimit D f a L ↔ Tendsto f (𝓝[D ∩ Iio a] a) (𝓝 L) := by
  rw [domainLeftLimit_iff_restricted, domainLimit_iff_tendsto
    (leftAccumulation_iff_restricted.mp ha)]
  have hs : (D ∩ Iio a) \ {a} = D ∩ Iio a := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Iio, mem_singleton_iff]
    constructor
    · exact fun h ↦ h.1
    · exact fun h ↦ ⟨h, ne_of_lt h.2⟩
  rw [hs]

theorem domainRightLimit_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (ha : RightAccumulationPointOf D a) :
    DomainRightLimit D f a L ↔ Tendsto f (𝓝[D ∩ Ioi a] a) (𝓝 L) := by
  rw [domainRightLimit_iff_restricted, domainLimit_iff_tendsto
    (rightAccumulation_iff_restricted.mp ha)]
  have hs : (D ∩ Ioi a) \ {a} = D ∩ Ioi a := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioi, mem_singleton_iff]
    constructor
    · exact fun h ↦ h.1
    · exact fun h ↦ ⟨h, ne_of_gt h.2⟩
  rw [hs]

theorem leftAccumulation_univ (a : ℝ) : LeftAccumulationPointOf univ a := by
  intro δ hδ
  exact ⟨a - δ / 2, mem_univ _, by linarith, by linarith⟩

theorem rightAccumulation_univ (a : ℝ) : RightAccumulationPointOf univ a := by
  intro δ hδ
  exact ⟨a + δ / 2, mem_univ _, by linarith, by linarith⟩

/-- Định lí 3.2.24: giới hạn hai phía tương đương hai giới hạn một phía bằng nhau. -/
theorem domainLimit_iff_left_right {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (hl : LeftAccumulationPointOf D a) (hr : RightAccumulationPointOf D a) :
    DomainLimit D f a L ↔ DomainLeftLimit D f a L ∧ DomainRightLimit D f a L := by
  constructor
  · rintro ⟨_, h⟩
    constructor
    · refine ⟨hl, fun ε hε ↦ ?_⟩
      obtain ⟨δ, hδ, hx⟩ := h ε hε
      refine ⟨δ, hδ, fun x hD hxl hxr ↦ hx x hD ?_ ?_⟩
      · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hxr))
      · exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · refine ⟨hr, fun ε hε ↦ ?_⟩
      obtain ⟨δ, hδ, hx⟩ := h ε hε
      refine ⟨δ, hδ, fun x hD hxl hxr ↦ hx x hD ?_ ?_⟩
      · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hxl))
      · exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨⟨_, hL⟩, ⟨_, hR⟩⟩
    refine ⟨accumulationPointOf_iff_left_or_right.mpr (Or.inl hl), fun ε hε ↦ ?_⟩
    obtain ⟨δL, hdL, hxL⟩ := hL ε hε
    obtain ⟨δR, hdR, hxR⟩ := hR ε hε
    refine ⟨min δL δR, lt_min hdL hdR, fun x hD hn hdist ↦ ?_⟩
    have hne : x ≠ a := sub_ne_zero.mp (abs_pos.mp hn)
    rcases lt_or_gt_of_ne hne with hxa | hax
    · apply hxL x hD _ hxa
      have hh := (abs_lt.mp (hdist.trans_le (min_le_left _ _))).1
      linarith
    · apply hxR x hD hax
      have hh := (abs_lt.mp (hdist.trans_le (min_le_right _ _))).2
      linarith

/-- Định lí 3.2.27: tiêu chuẩn dãy cho giới hạn phải. -/
theorem domainRightLimit_iff_sequences {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (ha : RightAccumulationPointOf D a) :
    DomainRightLimit D f a L ↔ ∀ u : ℕ → ℝ,
      (∀ n, 1 ≤ n → u n ∈ D ∧ u n ≠ a ∧ a < u n) → ConvergesTo u a →
      ConvergesTo (fun n ↦ f (u n)) L := by
  rw [domainRightLimit_iff_restricted, domainLimit_iff_sequences
    (rightAccumulation_iff_restricted.mp ha)]
  constructor
  · intro h u hu ht
    exact h u (fun n hn ↦ ⟨⟨(hu n hn).1, (hu n hn).2.2⟩, (hu n hn).2.1⟩) ht
  · intro h u hu ht
    exact h u (fun n hn ↦ ⟨(hu n hn).1.1, (hu n hn).2, (hu n hn).1.2⟩) ht

/-- Ví dụ 3.2.20: hai giới hạn một phía của hàm dấu. -/
theorem sign_one_sided_limits :
    DomainLeftLimit univ Real.sign 0 (-1) ∧ DomainRightLimit univ Real.sign 0 1 := by
  constructor
  · refine ⟨leftAccumulation_univ 0, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
    intro x _ _ hx
    rw [Real.sign_of_neg hx, sub_self, abs_zero]
    exact hε
  · refine ⟨rightAccumulation_univ 0, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
    intro x _ hx _
    rw [Real.sign_of_pos hx, sub_self, abs_zero]
    exact hε

/-- Ví dụ 3.2.21: hai giới hạn một phía của hàm phần nguyên. -/
theorem floor_one_sided_limits :
    DomainLeftLimit univ (fun x ↦ (⌊x⌋ : ℝ)) 1 0 ∧
      DomainRightLimit univ (fun x ↦ (⌊x⌋ : ℝ)) 1 1 := by
  constructor
  · refine ⟨leftAccumulation_univ 1, fun ε hε ↦ ⟨1 / 2, by norm_num, ?_⟩⟩
    intro x _ hx hx1
    have hf : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by simpa using hx1⟩
    simpa only [hf, Int.cast_zero, sub_zero, abs_zero] using hε
  · refine ⟨rightAccumulation_univ 1, fun ε hε ↦ ⟨1 / 2, by norm_num, ?_⟩⟩
    intro x _ hx1 hx
    have hf : ⌊x⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hx1.le, by norm_num; linarith⟩
    simpa only [hf, Int.cast_one, sub_self, abs_zero] using hε

/-- Ví dụ 3.2.23: hai giới hạn một phía, với mọi a>1. -/
theorem real_power_right_limit {a : ℝ} (ha : 1 < a) :
    DomainRightLimit univ (fun x ↦ a ^ x) 0 1 := by
  apply (domainRightLimit_iff_tendsto (rightAccumulation_univ 0)).mpr
  have h : ContinuousAt (fun x : ℝ ↦ a ^ x) 0 :=
    (Real.continuous_const_rpow (show a ≠ 0 by linarith)).continuousAt
  simpa only [inter_univ, univ_inter, Real.rpow_zero] using
    h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

theorem leftAccumulation_univ_diff (a : ℝ) : LeftAccumulationPointOf (univ \ {a}) a := by
  intro δ hδ
  refine ⟨a - δ / 2, ?_, by linarith, by linarith⟩
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
  linarith

theorem rightAccumulation_univ_diff (a : ℝ) : RightAccumulationPointOf (univ \ {a}) a := by
  intro δ hδ
  refine ⟨a + δ / 2, ?_, by linarith, by linarith⟩
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
  linarith

theorem domainLeftLimit_unique {D : Set ℝ} {f : ℝ → ℝ} {a A B : ℝ}
    (hA : DomainLeftLimit D f a A) (hB : DomainLeftLimit D f a B) : A = B :=
  domainLimit_unique (domainLeftLimit_iff_restricted.mp hA) (domainLeftLimit_iff_restricted.mp hB)

theorem domainRightLimit_unique {D : Set ℝ} {f : ℝ → ℝ} {a A B : ℝ}
    (hA : DomainRightLimit D f a A) (hB : DomainRightLimit D f a B) : A = B :=
  domainLimit_unique (domainRightLimit_iff_restricted.mp hA) (domainRightLimit_iff_restricted.mp hB)

/-- Ví dụ 3.2.22: giới hạn một phía trên miền tự nhiên. -/
noncomputable def absoluteQuadraticQuotient (x : ℝ) : ℝ := |x ^ 2 - 4| / (x - 2)

theorem absoluteQuadraticQuotient_left {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2) :
    absoluteQuadraticQuotient x = -(x + 2) := by
  unfold absoluteQuadraticQuotient
  rw [abs_of_neg (by nlinarith : x ^ 2 - 4 < 0)]
  apply (div_eq_iff (by linarith : x - 2 ≠ 0)).mpr
  ring

theorem absoluteQuadraticQuotient_right {x : ℝ} (hx2 : 2 < x) :
    absoluteQuadraticQuotient x = x + 2 := by
  unfold absoluteQuadraticQuotient
  rw [abs_of_pos (by nlinarith : 0 < x ^ 2 - 4)]
  apply (div_eq_iff (by linarith : x - 2 ≠ 0)).mpr
  ring

theorem absoluteQuadraticQuotient_limits :
    DomainLeftLimit (univ \ {(2 : ℝ)}) absoluteQuadraticQuotient 2 (-4) ∧
      DomainRightLimit (univ \ {(2 : ℝ)}) absoluteQuadraticQuotient 2 4 := by
  constructor
  · refine ⟨leftAccumulation_univ_diff 2, fun ε hε ↦
      ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩⟩
    intro x _ hxδ hx2
    have hx1 : 1 < x := by linarith [min_le_left (1 : ℝ) ε]
    rw [absoluteQuadraticQuotient_left hx1 hx2]
    have he : -(x + 2) - (-4) = 2 - x := by ring
    rw [he, abs_of_pos (by linarith : 0 < 2 - x)]
    linarith [min_le_right (1 : ℝ) ε]
  · refine ⟨rightAccumulation_univ_diff 2, fun ε hε ↦ ⟨ε, hε, ?_⟩⟩
    intro x _ hx2 hxδ
    rw [absoluteQuadraticQuotient_right hx2]
    have he : x + 2 - 4 = x - 2 := by ring
    rw [he, abs_of_pos (by linarith : 0 < x - 2)]
    linarith

/-- Ví dụ 3.2.25: hai giới hạn một phía khác nhau. -/
theorem absolute_div_self_limits :
    DomainLeftLimit (univ \ {(0 : ℝ)}) (fun x ↦ |x| / x) 0 (-1) ∧
      DomainRightLimit (univ \ {(0 : ℝ)}) (fun x ↦ |x| / x) 0 1 := by
  constructor
  · refine ⟨leftAccumulation_univ_diff 0, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
    intro x _ _ hx
    change |(abs x) / x - (-1)| < ε
    rw [abs_of_neg hx, neg_div, div_self (ne_of_lt hx), sub_self, abs_zero]
    exact hε
  · refine ⟨rightAccumulation_univ_diff 0, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
    intro x _ hx _
    change |(abs x) / x - 1| < ε
    rw [abs_of_pos hx, div_self (ne_of_gt hx), sub_self, abs_zero]
    exact hε

theorem absolute_div_self_no_domainLimit :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ |x| / x) 0 := by
  rintro ⟨L, hL⟩
  obtain ⟨hl, hr⟩ := (domainLimit_iff_left_right (leftAccumulation_univ_diff 0)
    (rightAccumulation_univ_diff 0)).mp hL
  have heL := domainLeftLimit_unique absolute_div_self_limits.1 hl
  have heR := domainRightLimit_unique absolute_div_self_limits.2 hr
  linarith


theorem leftAccumulation_open_interval {a b c : ℝ} (hc : c ∈ Ioo a b) :
    LeftAccumulationPointOf (Ioo a b) c := by
  intro δ hδ
  have hm : 0 < min δ (c - a) := lt_min hδ (by linarith [hc.1])
  refine ⟨c - min δ (c - a) / 2, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [hc.1, hc.2, min_le_left δ (c - a), min_le_right δ (c - a)]

theorem rightAccumulation_open_interval {a b c : ℝ} (hc : c ∈ Ioo a b) :
    RightAccumulationPointOf (Ioo a b) c := by
  intro δ hδ
  have hm : 0 < min δ (b - c) := lt_min hδ (by linarith [hc.2])
  refine ⟨c + min δ (b - c) / 2, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [hc.1, hc.2, min_le_left δ (b - c), min_le_right δ (b - c)]

/-- Định lí 3.2.26: giới hạn một phía của hàm đơn điệu tại nội điểm. -/
theorem monotone_open_interval_side_limits {a b c : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    DomainLeftLimit (Ioo a b) f c (sSup (f '' Ioo a c)) ∧
      DomainRightLimit (Ioo a b) f c (sInf (f '' Ioo c b)) ∧
      sSup (f '' Ioo a c) ≤ f c ∧ f c ≤ sInf (f '' Ioo c b) := by
  have hleftsub : Ioo a c ⊆ Ioo a b := fun x hx ↦ ⟨hx.1, hx.2.trans hc.2⟩
  have hrightsub : Ioo c b ⊆ Ioo a b := fun x hx ↦ ⟨hc.1.trans hx.1, hx.2⟩
  have hleftne : (f '' Ioo a c).Nonempty :=
    (nonempty_Ioo.mpr hc.1).image f
  have hrightne : (f '' Ioo c b).Nonempty :=
    (nonempty_Ioo.mpr hc.2).image f
  have hleftbdd : BddAbove (f '' Ioo a c) := by
    refine ⟨f c, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hf (hleftsub hx) hc hx.2.le
  have hrightbdd : BddBelow (f '' Ioo c b) := by
    refine ⟨f c, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hf hc (hrightsub hx) hx.1.le
  have hleftle : sSup (f '' Ioo a c) ≤ f c := csSup_le hleftne (by
    rintro y ⟨x, hx, rfl⟩
    exact hf (hleftsub hx) hc hx.2.le)
  have hrightle : f c ≤ sInf (f '' Ioo c b) := le_csInf hrightne (by
    rintro y ⟨x, hx, rfl⟩
    exact hf hc (hrightsub hx) hx.1.le)
  refine ⟨⟨leftAccumulation_open_interval hc, ?_⟩,
    ⟨rightAccumulation_open_interval hc, ?_⟩, hleftle, hrightle⟩
  · intro ε hε
    obtain ⟨y, ⟨x₁, hx₁, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hleftne (by linarith :
      sSup (f '' Ioo a c) - ε < sSup (f '' Ioo a c))
    refine ⟨c - x₁, by linarith [hx₁.2], fun x hx hx₁x hxc ↦ ?_⟩
    have hxleft : x ∈ Ioo a c := ⟨hx.1, hxc⟩
    have hfx : f x₁ ≤ f x := hf (hleftsub hx₁) hx (by linarith)
    have hfxsup : f x ≤ sSup (f '' Ioo a c) := le_csSup hleftbdd ⟨x, hxleft, rfl⟩
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · intro ε hε
    obtain ⟨y, ⟨x₁, hx₁, rfl⟩, hy⟩ := exists_lt_of_csInf_lt hrightne (by linarith :
      sInf (f '' Ioo c b) < sInf (f '' Ioo c b) + ε)
    refine ⟨x₁ - c, by linarith [hx₁.1], fun x hx hcx hxx₁ ↦ ?_⟩
    have hxright : x ∈ Ioo c b := ⟨hcx, hx.2⟩
    have hfx : f x ≤ f x₁ := hf hx (hrightsub hx₁) (by linarith)
    have hinffx : sInf (f '' Ioo c b) ≤ f x := csInf_le hrightbdd ⟨x, hxright, rfl⟩
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

end calculus.Chapter03.Section02OneSided
