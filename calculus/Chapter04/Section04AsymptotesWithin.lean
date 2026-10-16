import calculus.Chapter04.Section04Asymptotes
import calculus.Chapter03.Section07

/-!
# Tiệm cận trên miền xác định bất kỳ

Nguồn: `source/Ch4_hamsokhavi.tex` dòng 1961–1989, Định nghĩa 4.4.22, Ví dụ 4.4.23 và Định lí 4.4.24. Giới hạn chỉ xét trong miền `D`, với bộ lọc không suy biến; miền không cần chứa cả một khoảng hay một nửa trục.
-/

set_option autoImplicit false

noncomputable section

namespace calculus.Chapter04.Section04AsymptotesWithin

open Filter Set
open scoped Topology
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter03.Section02
open calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section07

/-- Định nghĩa 4.4.22: tiệm cận đứng xét trong miền `D`, với phía tiếp cận không suy biến. -/
def HasVerticalAsymptoteWithinAt (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ) : Prop :=
  (DomainRightTopLimit D f a ∨ DomainRightBotLimit D f a) ∨
    (DomainLeftTopLimit D f a ∨ DomainLeftBotLimit D f a)

/-- Định nghĩa 4.4.22: `y = b` là tiệm cận ngang trên một đầu không bị chặn của `D`. -/
def HasHorizontalAsymptoteWithin (f : ℝ → ℝ) (D : Set ℝ) (b : ℝ) : Prop :=
  DomainAtTopLimit D f b ∨ DomainAtBotLimit D f b

/-- Định nghĩa 4.4.22: tiệm cận xiên có hệ số góc khác 0, xét trên một đầu không bị chặn của `D`. -/
def HasObliqueAsymptoteWithin (f : ℝ → ℝ) (D : Set ℝ) (m b : ℝ) : Prop :=
  m ≠ 0 ∧
    (DomainAtTopLimit D (fun x ↦ f x - (m * x + b)) 0 ∨
      DomainAtBotLimit D (fun x ↦ f x - (m * x + b)) 0)


theorem hasVerticalAsymptoteWithinAt_iff (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ) :
    HasVerticalAsymptoteWithinAt f D a ↔
      (NeBot (𝓝[D ∩ Ioi a] a) ∧
          (Tendsto f (𝓝[D ∩ Ioi a] a) atTop ∨
            Tendsto f (𝓝[D ∩ Ioi a] a) atBot)) ∨
        (NeBot (𝓝[D ∩ Iio a] a) ∧
          (Tendsto f (𝓝[D ∩ Iio a] a) atTop ∨
            Tendsto f (𝓝[D ∩ Iio a] a) atBot)) := by
  have hRight : RightAccumulationPointOf D a ↔ NeBot (𝓝[D ∩ Ioi a] a) := by
    have hs : (D ∩ Ioi a) \ {a} = D ∩ Ioi a := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioi, mem_singleton_iff]
      constructor
      · exact fun h ↦ h.1
      · exact fun h ↦ ⟨h, ne_of_gt h.2⟩
    simpa only [hs] using
      ((rightAccumulation_iff_restricted (D := D) (a := a)).trans
        accumulationPointOf_iff_neBot)
  have hLeft : LeftAccumulationPointOf D a ↔ NeBot (𝓝[D ∩ Iio a] a) := by
    have hs : (D ∩ Iio a) \ {a} = D ∩ Iio a := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff, mem_Iio, mem_singleton_iff]
      constructor
      · exact fun h ↦ h.1
      · exact fun h ↦ ⟨h, ne_of_lt h.2⟩
    simpa only [hs] using
      ((leftAccumulation_iff_restricted (D := D) (a := a)).trans
        accumulationPointOf_iff_neBot)
  simp only [HasVerticalAsymptoteWithinAt, DomainRightTopLimit, DomainRightBotLimit,
    DomainLeftTopLimit, DomainLeftBotLimit, hRight, hLeft, and_or_left]


theorem hasHorizontalAsymptoteWithin_iff (f : ℝ → ℝ) (D : Set ℝ) (b : ℝ) :
    HasHorizontalAsymptoteWithin f D b ↔
      (NeBot (atTop ⊓ 𝓟 D) ∧ Tendsto f (atTop ⊓ 𝓟 D) (𝓝 b)) ∨
        (NeBot (atBot ⊓ 𝓟 D) ∧ Tendsto f (atBot ⊓ 𝓟 D) (𝓝 b)) := by
  have hTop : DomainAtTopLimit D f b ↔
      NeBot (atTop ⊓ 𝓟 D) ∧ Tendsto f (atTop ⊓ 𝓟 D) (𝓝 b) := by
    constructor
    · intro h
      exact ⟨(properLimitApproach_positiveInfinity_iff D).mpr h.1,
        (domainAtTopLimit_iff_tendsto h.1).mp h⟩
    · intro h
      exact (domainAtTopLimit_iff_tendsto
        ((properLimitApproach_positiveInfinity_iff D).mp h.1)).mpr h.2
  have hBot : DomainAtBotLimit D f b ↔
      NeBot (atBot ⊓ 𝓟 D) ∧ Tendsto f (atBot ⊓ 𝓟 D) (𝓝 b) := by
    constructor
    · intro h
      exact ⟨(properLimitApproach_negativeInfinity_iff D).mpr h.1,
        (domainAtBotLimit_iff_tendsto h.1).mp h⟩
    · intro h
      exact (domainAtBotLimit_iff_tendsto
        ((properLimitApproach_negativeInfinity_iff D).mp h.1)).mpr h.2
  exact or_congr hTop hBot


theorem hasObliqueAsymptoteWithin_filter_iff (f : ℝ → ℝ) (D : Set ℝ) (m b : ℝ) :
    HasObliqueAsymptoteWithin f D m b ↔ m ≠ 0 ∧
      ((NeBot (atTop ⊓ 𝓟 D) ∧
          Tendsto (fun x ↦ f x - (m * x + b)) (atTop ⊓ 𝓟 D) (𝓝 0)) ∨
        (NeBot (atBot ⊓ 𝓟 D) ∧
          Tendsto (fun x ↦ f x - (m * x + b)) (atBot ⊓ 𝓟 D) (𝓝 0))) := by
  change m ≠ 0 ∧ HasHorizontalAsymptoteWithin (fun x ↦ f x - (m * x + b)) D 0 ↔ _
  rw [hasHorizontalAsymptoteWithin_iff]

/-- Định lí 4.4.24: tiêu chuẩn tiệm cận tại `+∞` trên miền không bị chặn trên. -/
theorem affine_residual_limit_atTopWithin_iff (D : Set ℝ)
    (_hD : NeBot (atTop ⊓ 𝓟 D)) (f : ℝ → ℝ) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) (atTop ⊓ 𝓟 D) (𝓝 0) ↔
      Tendsto (fun x ↦ f x / x) (atTop ⊓ 𝓟 D) (𝓝 m) ∧
        Tendsto (fun x ↦ f x - m * x) (atTop ⊓ 𝓟 D) (𝓝 b) :=
  affine_residual_limit_iff
    (tendsto_inv_atTop_zero.mono_left inf_le_left)
    (((eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left).mono
      fun _ hx ↦ hx.ne') f m b

/-- Định lí 4.4.24: tiêu chuẩn tiệm cận tại `−∞` trên miền không bị chặn dưới. -/
theorem affine_residual_limit_atBotWithin_iff (D : Set ℝ)
    (_hD : NeBot (atBot ⊓ 𝓟 D)) (f : ℝ → ℝ) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) (atBot ⊓ 𝓟 D) (𝓝 0) ↔
      Tendsto (fun x ↦ f x / x) (atBot ⊓ 𝓟 D) (𝓝 m) ∧
        Tendsto (fun x ↦ f x - m * x) (atBot ⊓ 𝓟 D) (𝓝 b) :=
  affine_residual_limit_iff
    (tendsto_inv_atBot_zero.mono_left inf_le_left)
    (((eventually_lt_atBot (0 : ℝ)).filter_mono inf_le_left).mono
      fun _ hx ↦ hx.ne) f m b


theorem hasObliqueAsymptoteWithin_iff (f : ℝ → ℝ) (D : Set ℝ) (m b : ℝ) :
    HasObliqueAsymptoteWithin f D m b ↔ m ≠ 0 ∧
      ((NeBot (atTop ⊓ 𝓟 D) ∧
          (Tendsto (fun x ↦ f x / x) (atTop ⊓ 𝓟 D) (𝓝 m) ∧
            Tendsto (fun x ↦ f x - m * x) (atTop ⊓ 𝓟 D) (𝓝 b))) ∨
        (NeBot (atBot ⊓ 𝓟 D) ∧
          (Tendsto (fun x ↦ f x / x) (atBot ⊓ 𝓟 D) (𝓝 m) ∧
            Tendsto (fun x ↦ f x - m * x) (atBot ⊓ 𝓟 D) (𝓝 b)))) := by
  rw [hasObliqueAsymptoteWithin_filter_iff]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, (affine_residual_limit_atTopWithin_iff D h.1 f m b).mp h.2⟩
    · exact Or.inr ⟨h.1, (affine_residual_limit_atBotWithin_iff D h.1 f m b).mp h.2⟩
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, (affine_residual_limit_atTopWithin_iff D h.1 f m b).mpr h.2⟩
    · exact Or.inr ⟨h.1, (affine_residual_limit_atBotWithin_iff D h.1 f m b).mpr h.2⟩


theorem hasVerticalAsymptoteWithinAt_univ_iff (f : ℝ → ℝ) (a : ℝ) :
    HasVerticalAsymptoteWithinAt f univ a ↔ HasVerticalAsymptoteAt f a := by
  rw [hasVerticalAsymptoteWithinAt_iff]
  unfold HasVerticalAsymptoteAt
  simp only [univ_inter]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨inferInstance, h⟩
    · exact Or.inr ⟨inferInstance, h⟩


theorem hasHorizontalAsymptoteWithin_univ_iff (f : ℝ → ℝ) (b : ℝ) :
    HasHorizontalAsymptoteWithin f univ b ↔ HasHorizontalAsymptote f b := by
  rw [hasHorizontalAsymptoteWithin_iff]
  unfold HasHorizontalAsymptote
  simp only [principal_univ, inf_top_eq]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨inferInstance, h⟩
    · exact Or.inr ⟨inferInstance, h⟩


theorem hasObliqueAsymptoteWithin_univ_iff (f : ℝ → ℝ) (m b : ℝ) :
    HasObliqueAsymptoteWithin f univ m b ↔ HasObliqueAsymptote f m b := by
  rw [hasObliqueAsymptoteWithin_filter_iff]
  unfold HasObliqueAsymptote
  simp only [principal_univ, inf_top_eq]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rcases h with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨inferInstance, h⟩
    · exact Or.inr ⟨inferInstance, h⟩

/-- Ví dụ 4.4.23(a): miền của `ln x` là `(0, +∞)`, chỉ xét giới hạn phải tại `0`. -/
theorem logarithm_vertical_asymptote_zero_within :
    HasVerticalAsymptoteWithinAt Real.log (Ioi 0) 0 := by
  apply (hasVerticalAsymptoteWithinAt_iff Real.log (Ioi 0) 0).mpr
  refine Or.inl ⟨?_, Or.inr ?_⟩
  · simpa only [inter_self] using (inferInstance : NeBot (𝓝[>] (0 : ℝ)))
  · simpa only [inter_self] using Real.tendsto_log_nhdsGT_zero

/-- Ví dụ 4.4.23(b): miền của `e^x` là `ℝ`, giới hạn ở `-∞` bằng `0`. -/
theorem exponential_horizontal_asymptote_zero_within :
    HasHorizontalAsymptoteWithin Real.exp univ 0 :=
  (hasHorizontalAsymptoteWithin_univ_iff Real.exp 0).mpr
    exponential_horizontal_asymptote_zero

/-- Toàn bộ Ví dụ 4.4.23, với miền xác định của mỗi hàm. -/
theorem source_logarithm_exponential_asymptotes_within :
    HasVerticalAsymptoteWithinAt Real.log (Ioi 0) 0 ∧
      HasHorizontalAsymptoteWithin Real.exp univ 0 :=
  ⟨logarithm_vertical_asymptote_zero_within, exponential_horizontal_asymptote_zero_within⟩

end calculus.Chapter04.Section04AsymptotesWithin
