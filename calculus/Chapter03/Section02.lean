import calculus.Chapter02.Section03
import Mathlib.Topology.Sequences
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.Push

/-!
# 3.2. Giới hạn hàm số

Nguồn: dòng 1303–1668.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section02
open calculus.Chapter02.Section03

/-- Định nghĩa 3.2.1: điểm tụ của tập. -/
def AccumulationPointOf (D : Set ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, ∃ x ∈ D, x ≠ a ∧ a - δ < x ∧ x < a + δ

/-- Định nghĩa 3.2.2: điểm cô lập thuộc tập đang xét. -/
def IsolatedPointOf (D : Set ℝ) (a : ℝ) : Prop := a ∈ D ∧ ¬ AccumulationPointOf D a

/-- Định nghĩa 3.2.4: điểm tụ trái. -/
def LeftAccumulationPointOf (D : Set ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, ∃ x ∈ D, a - δ < x ∧ x < a

/-- Định nghĩa 3.2.4: điểm tụ phải. -/
def RightAccumulationPointOf (D : Set ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, ∃ x ∈ D, a < x ∧ x < a + δ


theorem accumulationPointOf_iff_abs {D : Set ℝ} {a : ℝ} :
    AccumulationPointOf D a ↔ ∀ δ > 0, ∃ x ∈ D, 0 < |x - a| ∧ |x - a| < δ := by
  simp only [AccumulationPointOf, abs_pos, sub_ne_zero, abs_lt]
  constructor <;> intro h δ hδ <;> obtain ⟨x, hx, hn, h₁, h₂⟩ := h δ hδ
  · exact ⟨x, hx, hn, by linarith, by linarith⟩
  · exact ⟨x, hx, hn, by linarith, by linarith⟩


theorem accumulationPointOf_iff_accPt {D : Set ℝ} {a : ℝ} :
    AccumulationPointOf D a ↔ AccPt a (𝓟 D) := by
  rw [accumulationPointOf_iff_abs, accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨x, hx, hn, hdist⟩ := h δ hδ
    exact ⟨x, ⟨hsub (by simpa [Metric.mem_ball, Real.dist_eq] using hdist), hx⟩,
      sub_ne_zero.mp (abs_pos.mp hn)⟩
  · intro h δ hδ
    obtain ⟨x, ⟨hxball, hx⟩, hn⟩ := h (Metric.ball a δ) (Metric.ball_mem_nhds a hδ)
    exact ⟨x, hx, abs_pos.mpr (sub_ne_zero.mpr hn),
      by simpa [Metric.mem_ball, Real.dist_eq] using hxball⟩


theorem accumulationPointOf_iff_neBot {D : Set ℝ} {a : ℝ} :
    AccumulationPointOf D a ↔ (𝓝[D \ {a}] a).NeBot :=
  accumulationPointOf_iff_accPt.trans accPt_principal_iff_nhdsWithin

/-- dòng 1330: điểm tụ của tập là điểm tụ trái hoặc điểm tụ phải của tập đó. -/
theorem accumulationPointOf_iff_left_or_right {D : Set ℝ} {a : ℝ} :
    AccumulationPointOf D a ↔ LeftAccumulationPointOf D a ∨ RightAccumulationPointOf D a := by
  constructor
  · intro h
    by_cases hl : LeftAccumulationPointOf D a
    · exact Or.inl hl
    · right
      unfold LeftAccumulationPointOf at hl
      push Not at hl
      obtain ⟨δ₀, hδ₀, hl⟩ := hl
      intro δ hδ
      obtain ⟨x, hx, hn, hleft, hright⟩ := h (min δ δ₀) (lt_min hδ hδ₀)
      have hxleft : a - δ₀ < x := by linarith [min_le_right δ δ₀]
      have hnot : ¬x < a := by
        intro hh
        linarith [hl x hx hxleft]
      exact ⟨x, hx, lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hn),
        lt_of_lt_of_le hright (by linarith [min_le_left δ δ₀])⟩
  · rintro (hl | hr) δ hδ
    · obtain ⟨x, hx, hleft, hright⟩ := hl δ hδ
      exact ⟨x, hx, ne_of_lt hright, hleft, by linarith⟩
    · obtain ⟨x, hx, hleft, hright⟩ := hr δ hδ
      exact ⟨x, hx, ne_of_gt hleft, by linarith, hright⟩

/-- Mệnh đề 3.2.5: đặc trưng điểm tụ bằng dãy. -/
theorem accumulationPointOf_iff_sequence {D : Set ℝ} {a : ℝ} :
    AccumulationPointOf D a ↔ ∃ u : ℕ → ℝ,
      (∀ n, 1 ≤ n → u n ∈ D ∧ u n ≠ a) ∧ ConvergesTo u a := by
  rw [accumulationPointOf_iff_accPt, accPt_principal_iff_clusterPt,
    ← mem_closure_iff_clusterPt, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨u, hu, ht⟩
    refine ⟨u, fun n _ ↦ ?_, convergesTo_iff_tendsto.mpr ht⟩
    simpa only [Set.mem_sdiff, mem_singleton_iff] using hu n
  · rintro ⟨u, hu, ht⟩
    refine ⟨fun n ↦ u (n + 1), fun n ↦ ?_, ?_⟩
    · simpa only [Set.mem_sdiff, mem_singleton_iff] using hu (n + 1) (by omega)
    · exact (convergesTo_iff_tendsto.mp ht).comp (tendsto_add_atTop_nat 1)

/-- Điều kiện ε–δ trên miền bỏ điểm của Định nghĩa 3.2.6. -/
def PuncturedLimitCondition (D : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, 0 < |x - a| → |x - a| < δ → |f x - L| < ε

/-- Giới hạn theo Định nghĩa 3.2.6: điểm tụ và điều kiện ε–δ trên miền bỏ điểm. -/
def DomainLimit (D : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  AccumulationPointOf D a ∧ PuncturedLimitCondition D f a L

def HasDomainLimit (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop := ∃ L, DomainLimit D f a L


theorem puncturedLimitCondition_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ} :
    PuncturedLimitCondition D f a L ↔ Tendsto f (𝓝[D \ {a}] a) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hxs hdist ↦ ?_⟩
    simpa only [Real.dist_eq] using hx x hxs.1
      (abs_pos.mpr (sub_ne_zero.mpr (by simpa using hxs.2)))
      (by simpa only [Real.dist_eq] using hdist)
  · intro h ε hε
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hxs hn hdist ↦ ?_⟩
    simpa only [Real.dist_eq] using hx ⟨hxs,
      by simpa only [mem_singleton_iff] using sub_ne_zero.mp (abs_pos.mp hn)⟩
      (by simpa only [Real.dist_eq] using hdist)

theorem domainLimit_iff_tendsto {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (ha : AccumulationPointOf D a) :
    DomainLimit D f a L ↔ Tendsto f (𝓝[D \ {a}] a) (𝓝 L) := by
  simp only [DomainLimit, ha, true_and, puncturedLimitCondition_iff_tendsto]

/-- Mệnh đề 3.2.8: giới hạn là duy nhất tại điểm tụ. -/
theorem domainLimit_unique {D : Set ℝ} {f : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (h₁ : DomainLimit D f a L₁) (h₂ : DomainLimit D f a L₂) : L₁ = L₂ := by
  have : (𝓝[D \ {a}] a).NeBot := accumulationPointOf_iff_neBot.mp h₁.1
  exact tendsto_nhds_unique (puncturedLimitCondition_iff_tendsto.mp h₁.2)
    (puncturedLimitCondition_iff_tendsto.mp h₂.2)

/-- Nhận xét 3.2.7: điều kiện lượng từ của giới hạn tại điểm tụ. -/
theorem hasDomainLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) :
    HasDomainLimit D f a ↔ ∃ L, ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ D, 0 < |x - a| → |x - a| < δ → |f x - L| < ε := by
  simp only [HasDomainLimit, DomainLimit, ha, true_and, PuncturedLimitCondition]


theorem not_hasDomainLimit_iff {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) :
    ¬ HasDomainLimit D f a ↔ ∀ L, ∃ ε > 0, ∀ δ > 0,
      ∃ x ∈ D, 0 < |x - a| ∧ |x - a| < δ ∧ ε ≤ |f x - L| := by
  rw [hasDomainLimit_iff ha]
  push Not
  rfl


theorem punctured_interval_iff (x a δ : ℝ) :
    x ∈ Ioo (a - δ) (a + δ) \ {a} ↔ 0 < |x - a| ∧ |x - a| < δ := by
  simp only [Set.mem_sdiff, mem_Ioo, mem_singleton_iff, abs_pos, sub_ne_zero, abs_lt]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩
  · exact ⟨h₂, by linarith [h₁.1], by linarith [h₁.2]⟩
  · exact ⟨⟨by linarith [h₂.1], by linarith [h₂.2]⟩, h₁⟩


theorem univ_diff_accumulation (a : ℝ) : AccumulationPointOf (univ \ {a}) a := by
  intro δ hδ
  refine ⟨a + δ / 2, ?_, ?_, ?_, ?_⟩
  · simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
    linarith
  · linarith
  · linarith
  · linarith

theorem univ_accumulation (a : ℝ) : AccumulationPointOf univ a := by
  intro δ hδ
  obtain ⟨x, _, hn, hl, hr⟩ := univ_diff_accumulation a δ hδ
  exact ⟨x, mem_univ x, hn, hl, hr⟩

/-- Ví dụ 3.2.3(a): mọi điểm trong [0,1] là điểm tụ của [0,1). -/
theorem unit_half_open_accumulation {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    AccumulationPointOf (Ico (0 : ℝ) 1) a := by
  intro δ hδ
  by_cases h1 : a = 1
  · subst a
    have hm : 0 < min δ 1 := lt_min hδ zero_lt_one
    refine ⟨1 - min δ 1 / 2, ?_, ?_, ?_, ?_⟩
    · constructor <;> linarith [min_le_right δ 1]
    · linarith
    · linarith [min_le_left δ 1]
    · linarith
  · have har : a < 1 := lt_of_le_of_ne ha.2 h1
    have hm : 0 < min δ (1 - a) := lt_min hδ (by linarith)
    refine ⟨a + min δ (1 - a) / 2, ?_, ?_, ?_, ?_⟩
    · constructor <;> linarith [ha.1, min_le_right δ (1 - a)]
    · linarith
    · linarith
    · linarith [min_le_left δ (1 - a)]

theorem unit_half_open_no_isolated : ∀ a ∈ Ico (0 : ℝ) 1,
    ¬ IsolatedPointOf (Ico (0 : ℝ) 1) a := by
  intro a ha h
  exact h.2 (unit_half_open_accumulation ⟨ha.1, ha.2.le⟩)


def positiveNaturalReals : Set ℝ := (fun n : ℕ ↦ (n : ℝ)) '' Ici 1

/-- Ví dụ 3.2.3(b): ℕ+ không có điểm tụ trong ℝ. -/
theorem positiveNaturalReals_no_accumulation (a : ℝ) : ¬ AccumulationPointOf positiveNaturalReals a := by
  intro h
  have hh := accumulationPointOf_iff_abs.mp h
  obtain ⟨x, ⟨n, hn, hnx⟩, hxa, hxδ⟩ := hh (1 / 4) (by norm_num)
  obtain ⟨y, ⟨m, hm, hmy⟩, _, hyδ⟩ := hh (min (1 / 4) (|x - a| / 2))
    (lt_min (by norm_num) (by positivity))
  have hy4 : |y - a| < 1 / 4 := hyδ.trans_le (min_le_left _ _)
  have hxy : |x - y| < 1 := by
    calc |x - y| ≤ |x - a| + |a - y| := abs_sub_le x a y
         _ < 1 := by rw [abs_sub_comm a y]; linarith
  have heq : n = m := by
    by_contra hnm
    have hsep : 1 ≤ dist (n : ℝ) (m : ℝ) := by
      rw [Nat.dist_cast_real]
      exact Nat.pairwise_one_le_dist hnm
    change (n : ℝ) = x at hnx
    change (m : ℝ) = y at hmy
    rw [Real.dist_eq, hnx, hmy] at hsep
    linarith
  have hxy_eq : x = y := by rw [← hnx, ← hmy, heq]
  rw [← hxy_eq] at hyδ
  have hyhalf := hyδ.trans_le (min_le_right _ _)
  linarith

theorem positiveNaturalReals_all_isolated : ∀ a ∈ positiveNaturalReals, IsolatedPointOf positiveNaturalReals a :=
  fun a ha ↦ ⟨ha, positiveNaturalReals_no_accumulation a⟩

/-- Ví dụ 3.2.3(c): khoảng mở bỏ một điểm. -/
theorem punctured_interval_accumulation {δ : ℝ} (hδ : 0 < δ) :
    AccumulationPointOf (Ioo (1 - δ) (1 + δ) \ {(1 : ℝ)}) 1 := by
  intro ε hε
  have hm : 0 < min ε δ := lt_min hε hδ
  refine ⟨1 + min ε δ / 2, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by linarith, by linarith [min_le_right ε δ]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith
  · linarith
  · linarith
  · linarith [min_le_left ε δ]

/-- Ví dụ 3.2.3(d): mọi số thực là điểm tụ của ℚ. -/
theorem rational_accumulation (a : ℝ) : AccumulationPointOf (range ((↑) : ℚ → ℝ)) a := by
  intro δ hδ
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show a < a + δ by linarith)
  exact ⟨q, ⟨q, rfl⟩, ne_of_gt hq₁, by linarith, hq₂⟩


theorem constant_domainLimit (C a : ℝ) : DomainLimit univ (fun _ ↦ C) a C := by
  refine ⟨univ_accumulation a, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
  intro x _ _ _
  simpa only [sub_self, abs_zero] using hε

theorem identity_domainLimit (a : ℝ) : DomainLimit univ id a a := by
  refine ⟨univ_accumulation a, fun ε hε ↦ ⟨ε, hε, ?_⟩⟩
  exact fun x _ _ hx ↦ hx


noncomputable def cubicDifferenceQuotient (x : ℝ) : ℝ := (x ^ 3 - 1) / (x - 1)

theorem cubicDifferenceQuotient_eq {x : ℝ} (hx : x ≠ 1) :
    cubicDifferenceQuotient x = x ^ 2 + x + 1 := by
  unfold cubicDifferenceQuotient
  apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
  ring


theorem cubicDifferenceQuotient_error {x : ℝ} (hx : x ≠ 1) :
    |cubicDifferenceQuotient x - 3| = |x + 2| * |x - 1| := by
  rw [cubicDifferenceQuotient_eq hx, ← abs_mul]
  congr 1
  ring


theorem cubicDifferenceQuotient_strict_estimate {x : ℝ}
    (hx0 : 0 < |x - 1|) (hx1 : |x - 1| < 1) :
    |cubicDifferenceQuotient x - 3| < 4 * |x - 1| := by
  rw [cubicDifferenceQuotient_error (sub_ne_zero.mp (abs_pos.mp hx0))]
  have hbound : |x + 2| < 4 := by
    calc |x + 2| = |(x - 1) + 3| := by congr 1; ring
         _ ≤ |x - 1| + |(3 : ℝ)| := abs_add_le _ _
         _ < 4 := by norm_num; linarith
  exact mul_lt_mul_of_pos_right hbound hx0


theorem cubicDifferenceQuotient_limit : DomainLimit (univ \ {(1 : ℝ)}) cubicDifferenceQuotient 1 3 := by
  refine ⟨univ_diff_accumulation 1, fun ε hε ↦ ?_⟩
  refine ⟨min 1 (ε / 4), lt_min zero_lt_one (by positivity), fun x _ hx0 hxδ ↦ ?_⟩
  have hx1 := hxδ.trans_le (min_le_left _ _)
  have hxe := hxδ.trans_le (min_le_right _ _)
  have hb := cubicDifferenceQuotient_strict_estimate hx0 hx1
  linarith

/-- Đẳng thức in tại dòng 1499 sai khi x=2; kết luận về giới hạn của ví dụ vẫn đúng. -/
theorem printed_cubic_absolute_equality_false :
    ¬ (∀ x : ℝ, x ≠ 1 → |cubicDifferenceQuotient x - 3| = |cubicDifferenceQuotient x|) := by
  intro h
  have hh := h 2 (by norm_num)
  norm_num [cubicDifferenceQuotient] at hh

/-- Nhận xét 3.2.12(i): thay đổi giá trị tại điểm bị bỏ không ảnh hưởng giới hạn. -/
theorem domainLimit_congr_punctured {D : Set ℝ} {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : ∀ x ∈ D, x ≠ a → f x = g x) :
    DomainLimit D f a L ↔ DomainLimit D g a L := by
  constructor <;> rintro ⟨ha, hf⟩ <;> refine ⟨ha, ?_⟩ <;> intro ε hε
  · obtain ⟨δ, hδ, hd⟩ := hf ε hε
    refine ⟨δ, hδ, fun x hx hn hdist ↦ ?_⟩
    rw [← hfg x hx (sub_ne_zero.mp (abs_pos.mp hn))]
    exact hd x hx hn hdist
  · obtain ⟨δ, hδ, hd⟩ := hf ε hε
    refine ⟨δ, hδ, fun x hx hn hdist ↦ ?_⟩
    rw [hfg x hx (sub_ne_zero.mp (abs_pos.mp hn))]
    exact hd x hx hn hdist


theorem limit_value_at_hole_example (a : ℝ) :
    DomainLimit univ (fun x ↦ if x = a then 7 else 0) a 0 ∧
      (if a = a then (7 : ℝ) else 0) ≠ 0 := by
  constructor
  · apply (domainLimit_congr_punctured (f := fun _ ↦ 0) ?_).mp (constant_domainLimit 0 a)
    intro x _ hn
    simp [hn]
  · norm_num


theorem domainLimit_congr_domain {D : Set ℝ} {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : ∀ x ∈ D, f x = g x) : DomainLimit D f a L ↔ DomainLimit D g a L :=
  domainLimit_congr_punctured fun x hx _ ↦ hfg x hx

/-- Định lí 3.2.14: đặc trưng giới hạn bằng dãy. -/
theorem domainLimit_iff_sequences {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (ha : AccumulationPointOf D a) :
    DomainLimit D f a L ↔ ∀ u : ℕ → ℝ,
      (∀ n, 1 ≤ n → u n ∈ D ∧ u n ≠ a) → ConvergesTo u a →
      ConvergesTo (fun n ↦ f (u n)) L := by
  classical
  rw [domainLimit_iff_tendsto ha]
  constructor
  · intro hf u hu ht
    apply convergesTo_iff_tendsto.mpr
    have humem : ∀ᶠ n in atTop, u n ∈ D \ {a} := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simpa only [Set.mem_sdiff, mem_singleton_iff] using hu n hn
    have hub : Tendsto u atTop (𝓝[D \ {a}] a) :=
      tendsto_nhdsWithin_iff.mpr ⟨convergesTo_iff_tendsto.mp ht, humem⟩
    exact hf.comp hub
  · intro h
    apply tendsto_iff_seq_tendsto.mpr
    intro u hu
    obtain ⟨c, hc, hn, _, _⟩ := ha 1 zero_lt_one
    have hc' : c ∈ D \ {a} := by simpa using And.intro hc hn
    have humem : ∀ᶠ n in atTop, u n ∈ D \ {a} :=
      (tendsto_nhdsWithin_iff.mp hu).2
    let v : ℕ → ℝ := fun n ↦ if u n ∈ D \ {a} then u n else c
    have huv : u =ᶠ[atTop] v := humem.mono fun n hn ↦ by
      simp only [v, if_pos hn]
    have hv : ConvergesTo v a := convergesTo_iff_tendsto.mpr
      ((hu.mono_right nhdsWithin_le_nhds).congr' huv)
    have hfv := convergesTo_iff_tendsto.mp (h v (fun n _ ↦ by
      by_cases hn : u n ∈ D \ {a}
      · simpa only [v, if_pos hn] using (show u n ∈ D ∧ u n ≠ a from
          ⟨hn.1, by simpa only [mem_singleton_iff] using hn.2⟩)
      · simpa only [v, if_neg hn] using (show c ∈ D ∧ c ≠ a from
          ⟨hc'.1, by simpa only [mem_singleton_iff] using hc'.2⟩)) hv)
    exact hfv.congr' (huv.symm.mono fun n hn ↦ congrArg f hn)

/-- Hệ quả 3.2.17: hai dãy ảnh có giới hạn khác nhau bác bỏ giới hạn hàm số. -/
theorem no_domainLimit_of_two_sequences {D : Set ℝ} {f : ℝ → ℝ} {a A B : ℝ}
    (ha : AccumulationPointOf D a) (u v : ℕ → ℝ)
    (hu : ∀ n, 1 ≤ n → u n ∈ D ∧ u n ≠ a)
    (hv : ∀ n, 1 ≤ n → v n ∈ D ∧ v n ≠ a)
    (hua : ConvergesTo u a) (hva : ConvergesTo v a)
    (hfu : ConvergesTo (fun n ↦ f (u n)) A) (hfv : ConvergesTo (fun n ↦ f (v n)) B)
    (hne : A ≠ B) : ¬ HasDomainLimit D f a := by
  rintro ⟨L, hL⟩
  have hh := (domainLimit_iff_sequences ha).mp hL
  have hA : A = L := tendsto_nhds_unique (convergesTo_iff_tendsto.mp hfu)
    (convergesTo_iff_tendsto.mp (hh u hu hua))
  have hB : B = L := tendsto_nhds_unique (convergesTo_iff_tendsto.mp hfv)
    (convergesTo_iff_tendsto.mp (hh v hv hva))
  exact hne (hA.trans hB.symm)


def positiveIndexedInterleave (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then u (n / 2 + 1) else v (n / 2 + 1)

theorem positiveIndexedInterleave_even (u v : ℕ → ℝ) (n : ℕ) :
    positiveIndexedInterleave u v (2 * n) = u (n + 1) := by
  simp [positiveIndexedInterleave]

theorem positiveIndexedInterleave_odd (u v : ℕ → ℝ) (n : ℕ) :
    positiveIndexedInterleave u v (2 * n + 1) = v (n + 1) := by
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [positiveIndexedInterleave, hmod, hdiv]

theorem positiveIndexedInterleave_converges {u v : ℕ → ℝ} {a : ℝ}
    (hu : ConvergesTo u a) (hv : ConvergesTo v a) :
    ConvergesTo (positiveIndexedInterleave u v) a := by
  intro ε hε
  obtain ⟨N, hN, huN⟩ := hu ε hε
  obtain ⟨M, hM, hvM⟩ := hv ε hε
  refine ⟨2 * max N M, by omega, fun n hn ↦ ?_⟩
  have hnN : N ≤ n / 2 + 1 := by omega
  have hnM : M ≤ n / 2 + 1 := by omega
  by_cases he : n % 2 = 0
  · simpa [positiveIndexedInterleave, he] using huN (n / 2 + 1) hnN
  · simpa [positiveIndexedInterleave, he] using hvM (n / 2 + 1) hnM

theorem positiveIndexedInterleave_image_limits {u v : ℕ → ℝ} {f : ℝ → ℝ} {L : ℝ}
    (h : ConvergesTo (fun n ↦ f (positiveIndexedInterleave u v n)) L) :
    ConvergesTo (fun n ↦ f (u n)) L ∧ ConvergesTo (fun n ↦ f (v n)) L := by
  have he : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    (strictMono_nat_of_lt_succ fun n ↦ by omega).tendsto_atTop
  have ho : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
    (strictMono_nat_of_lt_succ fun n ↦ by omega).tendsto_atTop
  have hu : Tendsto (fun n ↦ f (u (n + 1))) atTop (𝓝 L) := by
    simpa only [Function.comp_def, positiveIndexedInterleave_even] using
      (convergesTo_iff_tendsto.mp h).comp he
  have hv : Tendsto (fun n ↦ f (v (n + 1))) atTop (𝓝 L) := by
    simpa only [Function.comp_def, positiveIndexedInterleave_odd] using
      (convergesTo_iff_tendsto.mp h).comp ho
  exact ⟨convergesTo_iff_tendsto.mpr ((tendsto_add_atTop_iff_nat 1).mp hu),
    convergesTo_iff_tendsto.mpr ((tendsto_add_atTop_iff_nat 1).mp hv)⟩

/-- Hệ quả 3.2.15: giới hạn hàm số không tồn tại khi và chỉ khi có dãy ảnh phân kì. -/
theorem no_domainLimit_iff_divergent_sequence {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) :
    ¬ HasDomainLimit D f a ↔ ∃ u : ℕ → ℝ,
      (∀ n, 1 ≤ n → u n ∈ D ∧ u n ≠ a) ∧ ConvergesTo u a ∧
      IsDivergent (fun n ↦ f (u n)) := by
  classical
  constructor
  · intro hno
    obtain ⟨u, hu, hua⟩ := accumulationPointOf_iff_sequence.mp ha
    by_cases hfu : IsConvergent (fun n ↦ f (u n))
    · obtain ⟨L, hL⟩ := hfu
      obtain ⟨ε, hε, hfail⟩ := (not_hasDomainLimit_iff ha).mp hno L
      have hb : ∀ n : ℕ, ∃ x ∈ D, 0 < |x - a| ∧
          |x - a| < 1 / ((n : ℝ) + 1) ∧ ε ≤ |f x - L| :=
        fun n ↦ hfail (1 / ((n : ℝ) + 1)) (by positivity)
      choose v hvmem hvpos hvsmall hvfar using hb
      have hva : ConvergesTo v a := by
        intro η hη
        obtain ⟨N, hN, hn⟩ := convergesTo_iff_tendsto.mpr
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) η hη
        refine ⟨N, hN, fun n hnN ↦ ?_⟩
        have hh := hn n hnN
        rw [sub_zero, abs_of_pos (by positivity)] at hh
        exact (hvsmall n).trans hh
      have hvnot : ¬ ConvergesTo (fun n ↦ f (v n)) L := by
        intro h
        obtain ⟨N, hN, hn⟩ := h ε hε
        exact (not_lt_of_ge (hvfar N)) (hn N le_rfl)
      refine ⟨positiveIndexedInterleave u v, fun n _ ↦ ?_, positiveIndexedInterleave_converges hua hva, ?_⟩
      · by_cases he : n % 2 = 0
        · simpa [positiveIndexedInterleave, he] using hu (n / 2 + 1) (by omega)
        · exact by
            simp only [positiveIndexedInterleave, he, ↓reduceIte]
            exact ⟨hvmem _, sub_ne_zero.mp (abs_pos.mp (hvpos _))⟩
      · rintro ⟨B, hB⟩
        obtain ⟨huB, hvB⟩ := positiveIndexedInterleave_image_limits hB
        have hLB : L = B := tendsto_nhds_unique (convergesTo_iff_tendsto.mp hL)
          (convergesTo_iff_tendsto.mp huB)
        exact hvnot (by simpa only [hLB] using hvB)
    · exact ⟨u, hu, hua, hfu⟩
  · rintro ⟨u, hu, hua, hfu⟩ ⟨L, hL⟩
    exact hfu ⟨L, (domainLimit_iff_sequences ha).mp hL u hu hua⟩


noncomputable def reciprocalPi (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.pi)


noncomputable def reciprocalSinPeak (n : ℕ) : ℝ :=
  1 / (Real.pi / 2 + 2 * (n : ℝ) * Real.pi)

theorem reciprocalPi_converges : ConvergesTo reciprocalPi 0 := by
  apply convergesTo_iff_tendsto.mpr
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const Real.pi
  change Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) * Real.pi)) atTop (𝓝 0)
  simpa only [div_mul_eq_div_div, zero_div] using h

theorem reciprocalSinPeak_converges : ConvergesTo reciprocalSinPeak 0 := by
  apply convergesTo_iff_tendsto.mpr
  have hmul : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) * Real.pi) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : 0 < (2 : ℝ))).atTop_mul_const
      Real.pi_pos
  have hden : Tendsto (fun n : ℕ ↦ Real.pi / 2 + 2 * (n : ℝ) * Real.pi) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hmul
  change Tendsto (fun n : ℕ ↦ 1 / (Real.pi / 2 + 2 * (n : ℝ) * Real.pi)) atTop (𝓝 0)
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden

theorem reciprocalPi_positive {n : ℕ} (hn : 1 ≤ n) : 0 < reciprocalPi n := by
  unfold reciprocalPi
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  positivity

theorem reciprocalSinPeak_positive (n : ℕ) : 0 < reciprocalSinPeak n := by
  unfold reciprocalSinPeak
  positivity

theorem sine_reciprocalPi (n : ℕ) : Real.sin (1 / reciprocalPi n) = 0 := by
  simp only [reciprocalPi, one_div_one_div, Real.sin_nat_mul_pi]

theorem sine_reciprocalSinPeak (n : ℕ) : Real.sin (1 / reciprocalSinPeak n) = 1 := by
  rw [reciprocalSinPeak, one_div_one_div]
  have he : Real.pi / 2 + 2 * (n : ℝ) * Real.pi = Real.pi / 2 + n * (2 * Real.pi) := by ring
  rw [he, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

/-- Ví dụ 3.2.13: sin(1/x) không có giới hạn hữu hạn tại 0. -/
theorem sine_reciprocal_no_domainLimit :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ Real.sin (1 / x)) 0 := by
  apply no_domainLimit_of_two_sequences (univ_diff_accumulation 0)
    reciprocalPi reciprocalSinPeak
    (fun n hn ↦ ⟨⟨mem_univ _, by simpa using (reciprocalPi_positive hn).ne'⟩,
      (reciprocalPi_positive hn).ne'⟩)
    (fun n _ ↦ ⟨⟨mem_univ _, by simpa using (reciprocalSinPeak_positive n).ne'⟩,
      (reciprocalSinPeak_positive n).ne'⟩)
    reciprocalPi_converges reciprocalSinPeak_converges
    (by simpa only [sine_reciprocalPi] using constant_converges 0)
    (by simpa only [sine_reciprocalSinPeak] using constant_converges 1)
    (by norm_num)


theorem cosine_reciprocalPi (n : ℕ) : Real.cos (1 / reciprocalPi n) = (-1 : ℝ) ^ n := by
  simp only [reciprocalPi, one_div_one_div, Real.cos_nat_mul_pi]

theorem alternating_sequence_divergent : IsDivergent (fun n : ℕ ↦ (-1 : ℝ) ^ n) := by
  rintro ⟨L, hL⟩
  obtain ⟨N, hN, hn⟩ := hL 1 zero_lt_one
  have he := hn (2 * N) (by omega)
  have ho := hn (2 * N + 1) (by omega)
  have hpe : (-1 : ℝ) ^ (2 * N) = 1 := by simp [pow_mul]
  have hpo : (-1 : ℝ) ^ (2 * N + 1) = -1 := by rw [pow_add, hpe]; norm_num
  change |(-1 : ℝ) ^ (2 * N) - L| < 1 at he
  change |(-1 : ℝ) ^ (2 * N + 1) - L| < 1 at ho
  rw [hpe, abs_lt] at he
  rw [hpo, abs_lt] at ho
  linarith [he.2, ho.1]

/-- Ví dụ 3.2.16: dãy ảnh phân kì bác bỏ giới hạn hàm số. -/
theorem cosine_reciprocal_no_domainLimit :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ Real.cos (1 / x)) 0 := by
  apply (no_domainLimit_iff_divergent_sequence (univ_diff_accumulation 0)).mpr
  refine ⟨reciprocalPi, fun n hn ↦ ?_, reciprocalPi_converges, ?_⟩
  · exact ⟨⟨mem_univ _, by simpa using (reciprocalPi_positive hn).ne'⟩,
      (reciprocalPi_positive hn).ne'⟩
  · simpa only [cosine_reciprocalPi] using alternating_sequence_divergent


noncomputable def dirichletFunction (x : ℝ) : ℝ := by
  classical
  exact if x ∈ range ((↑) : ℚ → ℝ) then 1 else 0

/-- Ví dụ 3.2.18: hàm Dirichlet không có giới hạn hữu hạn tại bất kì điểm nào. -/
theorem dirichletFunction_no_domainLimit (a : ℝ) : ¬ HasDomainLimit univ dirichletFunction a := by
  classical
  rw [not_hasDomainLimit_iff (univ_accumulation a)]
  intro L
  refine ⟨1 / 2, by norm_num, fun δ hδ ↦ ?_⟩
  obtain ⟨q, hqa, hqδ⟩ := exists_rat_btwn (show a < a + δ by linarith)
  obtain ⟨r, hri, hra, hrδ⟩ := exists_irrational_btwn (show a < a + δ by linarith)
  have hq : dirichletFunction q = 1 := by
    unfold dirichletFunction
    exact if_pos ⟨q, rfl⟩
  have hr : dirichletFunction r = 0 := by
    unfold dirichletFunction
    exact if_neg hri
  by_cases hL : 1 / 2 ≤ |1 - L|
  · refine ⟨q, mem_univ _, ?_, ?_, ?_⟩
    · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hqa))
    · rw [abs_of_pos (by linarith : 0 < (q : ℝ) - a)]; linarith
    · simpa only [hq] using hL
  · refine ⟨r, mem_univ _, ?_, ?_, ?_⟩
    · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hra))
    · rw [abs_of_pos (by linarith : 0 < r - a)]; linarith
    · rw [hr]
      have hh : |1 - L| < 1 / 2 := lt_of_not_ge hL
      rw [abs_lt] at hh
      have hpos : 0 ≤ L := by linarith [hh.2]
      rw [zero_sub, abs_neg, abs_of_nonneg hpos]
      linarith [hh.2]


theorem output_interval_iff_abs (y L ε : ℝ) :
    y ∈ Ioo (L - ε) (L + ε) ↔ |y - L| < ε := by
  simp only [mem_Ioo, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- dòng 1363: đồ thị bậc hai bỏ điểm (1,3). -/
theorem cubicDifferenceQuotient_graph :
    {p : ℝ × ℝ | p.1 ≠ 1 ∧ p.2 = cubicDifferenceQuotient p.1} =
      {p : ℝ × ℝ | p.1 ≠ 1 ∧ p.2 = p.1 ^ 2 + p.1 + 1} := by
  ext p
  constructor <;> rintro ⟨hp, hq⟩ <;> refine ⟨hp, ?_⟩
  · simpa only [cubicDifferenceQuotient_eq hp] using hq
  · simpa only [cubicDifferenceQuotient_eq hp] using hq

end calculus.Chapter03.Section02
