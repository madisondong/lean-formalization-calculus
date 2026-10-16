import calculus.Chapter03.Section07AlgebraSupplement
import calculus.Chapter03.Section01Powers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
§3.7 — bậc và phần chính

Nguồn: dòng 3370–3379.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07 calculus.Chapter03.Section07AlgebraSupplement
open calculus.Chapter03.Section01Powers


def EventuallyRealPowerDefinedAlong (D : Set ℝ) (p : LimitApproach) (φ : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ᶠ x in domainApproachFilter D p, φ x ∈ realPowerDomain α


def InfinitesimalPowerOrderAlong (D : Set ℝ) (p : LimitApproach)
    (f φ : ℝ → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ InfinitesimalAlong D p f ∧ InfinitesimalAlong D p φ ∧
    EventuallyRealPowerDefinedAlong D p φ α ∧ NonzeroRatioLimitAlong D p f (fun x ↦ φ x ^ α)


def InfiniteMagnitudePowerOrderAlong (D : Set ℝ) (p : LimitApproach)
    (f φ : ℝ → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ InfiniteMagnitudeAlong D p f ∧ InfiniteMagnitudeAlong D p φ ∧
    EventuallyRealPowerDefinedAlong D p φ α ∧ NonzeroRatioLimitAlong D p f (fun x ↦ φ x ^ α)

/-- Định nghĩa 3.7.18: bậc α>0; f và hàm so sánh cùng là vô cùng bé hoặc cùng là vô cùng lớn. -/
def AsymptoticPowerOrderAlong (D : Set ℝ) (p : LimitApproach) (f φ : ℝ → ℝ) (α : ℝ) : Prop :=
  InfinitesimalPowerOrderAlong D p f φ α ∨ InfiniteMagnitudePowerOrderAlong D p f φ α

/-- Định nghĩa 3.7.20: phần chính C·φ(x)^α, với C≠0. -/
noncomputable def powerPrincipalPart (C α : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ C * φ x ^ α


def HasPowerPrincipalPartAlong (D : Set ℝ) (p : LimitApproach)
    (f φ : ℝ → ℝ) (α C : ℝ) : Prop :=
  AsymptoticPowerOrderAlong D p f φ α ∧ C ≠ 0 ∧ NonvanishingAsymptoticEquivalenceAlong D p f (powerPrincipalPart C α φ)


theorem real_power_abs {x α : ℝ} (hx : x ∈ realPowerDomain α) :
    |x ^ α| = |x| ^ α := by
  by_cases hi : IntegerExponent α
  · obtain ⟨z, rfl⟩ := hi
    simpa only [Real.rpow_intCast] using abs_zpow x z
  · have hp : 0 < x := by simpa only [noninteger_power_domain hi, mem_Ioi] using hx
    exact Real.abs_rpow_of_nonneg hp.le


theorem real_power_ne_zero {x α : ℝ} (hx : x ∈ realPowerDomain α) (hx0 : x ≠ 0) :
    x ^ α ≠ 0 := by
  by_cases hi : IntegerExponent α
  · obtain ⟨z, rfl⟩ := hi
    rw [Real.rpow_intCast]
    exact zpow_ne_zero z hx0
  · have hp : 0 < x := by simpa only [noninteger_power_domain hi, mem_Ioi] using hx
    exact (Real.rpow_pos_of_pos hp α).ne'

variable {D : Set ℝ} {p : LimitApproach} {f φ : ℝ → ℝ} {α β : ℝ}


theorem power_order_eventually_base_ne {α : ℝ} (hα : 0 < α)
    (hs : NonzeroRatioLimitAlong D p f (fun x ↦ φ x ^ α)) :
    ∀ᶠ x in domainApproachFilter D p, φ x ≠ 0 := by
  filter_upwards [hs.2.1] with x hx
  intro hz
  apply hx
  rw [hz, Real.zero_rpow hα.ne']


theorem real_power_littleO_of_abs_ratio_zero (hp : NontrivialDomainApproach D p)
    (hα : EventuallyRealPowerDefinedAlong D p φ α)
    (hβ : EventuallyRealPowerDefinedAlong D p φ β)
    (hφ : ∀ᶠ x in domainApproachFilter D p, φ x ≠ 0)
    (ht : Tendsto (fun x ↦ |φ x| ^ (α - β)) (domainApproachFilter D p) (𝓝 0)) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ φ x ^ α) (fun x ↦ φ x ^ β) := by
  refine ⟨hp, ?_, ?_⟩
  · filter_upwards [hβ, hφ] with x hx hn
    exact real_power_ne_zero hx hn
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply ht.congr'
    filter_upwards [hα, hβ, hφ] with x ha hb hn
    rw [Real.norm_eq_abs, abs_div, real_power_abs ha, real_power_abs hb]
    exact Real.rpow_sub (abs_pos.mpr hn) α β


theorem infinitesimalAlong_powers_littleO (hφ : InfinitesimalAlong D p φ)
    (hα : EventuallyRealPowerDefinedAlong D p φ α)
    (hβ : EventuallyRealPowerDefinedAlong D p φ β)
    (hn : ∀ᶠ x in domainApproachFilter D p, φ x ≠ 0) (hβα : β < α) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ φ x ^ α) (fun x ↦ φ x ^ β) := by
  apply real_power_littleO_of_abs_ratio_zero hφ.1 hα hβ hn
  have habs : Tendsto (fun x ↦ |φ x|) (domainApproachFilter D p) (𝓝 0) := by
    simpa only [abs_zero] using hφ.2.abs
  exact habs.rpow_const_nhds_zero (sub_pos.mpr hβα)


theorem infinite_magnitude_powers_littleO (hφ : InfiniteMagnitudeAlong D p φ)
    (hα : EventuallyRealPowerDefinedAlong D p φ α)
    (hβ : EventuallyRealPowerDefinedAlong D p φ β)
    (hn : ∀ᶠ x in domainApproachFilter D p, φ x ≠ 0) (hαβ : α < β) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ φ x ^ α) (fun x ↦ φ x ^ β) := by
  apply real_power_littleO_of_abs_ratio_zero hφ.1 hα hβ hn
  rw [show α - β = -(β - α) by ring]
  exact (tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)).comp hφ.2


theorem nonvanishingDenominatorLittleOAlong_trans_equivalent_right {g h k : ℝ → ℝ}
    (hg : NonvanishingDenominatorLittleOAlong D p g h) (hh : NonvanishingAsymptoticEquivalenceAlong D p h k) :
    NonvanishingDenominatorLittleOAlong D p g k := by
  apply nonvanishingDenominatorLittleOAlong_iff_mathlib.mpr
  exact ⟨hg.1, hh.2.1,
    (nonvanishingDenominatorLittleOAlong_iff_mathlib.mp hg).2.2.trans_isEquivalent (nonvanishingAsymptoticEquivalenceAlong_mathlib hh)⟩


theorem infinitesimal_power_order_comparisons
    (ho : InfinitesimalPowerOrderAlong D p f φ α)
    (hβ : EventuallyRealPowerDefinedAlong D p φ β) :
    (β < α → NonvanishingDenominatorLittleOAlong D p f (fun x ↦ φ x ^ β)) ∧
      (α < β → NonvanishingDenominatorLittleOAlong D p (fun x ↦ φ x ^ β) f) := by
  have hn := power_order_eventually_base_ne ho.1 ho.2.2.2.2
  obtain ⟨C, hC, he, _⟩ := nonzeroRatioLimitAlong_leading_part ho.2.2.2.2
  constructor
  · intro hβα
    have hp := infinitesimalAlong_powers_littleO ho.2.2.1 ho.2.2.2.1 hβ hn hβα
    exact nonvanishingAsymptoticEquivalenceAlong_trans_littleO he (nonvanishingDenominatorLittleOAlong_const_mul hp C)
  · intro hαβ
    have hp := infinitesimalAlong_powers_littleO ho.2.2.1 hβ ho.2.2.2.1 hn hαβ
    exact nonvanishingDenominatorLittleOAlong_trans_equivalent_right (nonvanishingDenominatorLittleOAlong_const_mul_right hC hp)
      (nonvanishingAsymptoticEquivalenceAlong_symm he)


theorem infinite_power_order_comparisons
    (ho : InfiniteMagnitudePowerOrderAlong D p f φ α)
    (hβ : EventuallyRealPowerDefinedAlong D p φ β) :
    (β < α → NonvanishingDenominatorLittleOAlong D p (fun x ↦ φ x ^ β) f) ∧
      (α < β → NonvanishingDenominatorLittleOAlong D p f (fun x ↦ φ x ^ β)) := by
  have hn := power_order_eventually_base_ne ho.1 ho.2.2.2.2
  obtain ⟨C, hC, he, _⟩ := nonzeroRatioLimitAlong_leading_part ho.2.2.2.2
  constructor
  · intro hβα
    have hp := infinite_magnitude_powers_littleO ho.2.2.1 hβ ho.2.2.2.1 hn hβα
    exact nonvanishingDenominatorLittleOAlong_trans_equivalent_right (nonvanishingDenominatorLittleOAlong_const_mul_right hC hp)
      (nonvanishingAsymptoticEquivalenceAlong_symm he)
  · intro hαβ
    have hp := infinite_magnitude_powers_littleO ho.2.2.1 ho.2.2.2.1 hβ hn hαβ
    exact nonvanishingAsymptoticEquivalenceAlong_trans_littleO he (nonvanishingDenominatorLittleOAlong_const_mul hp C)


theorem nonzeroRatioLimitAlong_comparisons_sameOrder {g h : ℝ → ℝ}
    (hg : NonzeroRatioLimitAlong D p f g) (hh : NonzeroRatioLimitAlong D p f h) :
    NonzeroRatioLimitAlong D p g h := by
  obtain ⟨C, hC, htC⟩ := hg.2.2
  obtain ⟨B, hB, htB⟩ := hh.2.2
  have hfn : ∀ᶠ x in domainApproachFilter D p, f x ≠ 0 := by
    filter_upwards [htC.eventually_ne hC] with x hx
    exact (div_ne_zero_iff.mp hx).1
  refine ⟨hg.1, hh.2.1, B / C, div_ne_zero hB hC, ?_⟩
  apply (htB.div htC hC).congr'
  filter_upwards [hfn, hg.2.1, hh.2.1] with x hf hgx hhx
  change (f x / h x) / (f x / g x) = g x / h x
  field_simp [hf, hgx, hhx]


theorem nonzeroRatioLimitAlong_not_littleO {g h : ℝ → ℝ}
    (hs : NonzeroRatioLimitAlong D p g h) : ¬ NonvanishingDenominatorLittleOAlong D p g h := by
  intro hl
  let : (domainApproachFilter D p).NeBot := hs.1
  obtain ⟨C, hC, ht⟩ := hs.2.2
  exact hC (tendsto_nhds_unique ht hl.2.2)


theorem infinitesimal_power_order_unique
    (ha : InfinitesimalPowerOrderAlong D p f φ α)
    (hb : InfinitesimalPowerOrderAlong D p f φ β) : α = β := by
  have hn := power_order_eventually_base_ne ha.1 ha.2.2.2.2
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have hp := infinitesimalAlong_powers_littleO ha.2.2.1 hb.2.2.2.1 ha.2.2.2.1 hn hlt
    exact (nonzeroRatioLimitAlong_not_littleO
      (nonzeroRatioLimitAlong_comparisons_sameOrder hb.2.2.2.2 ha.2.2.2.2) hp).elim
  · exact heq
  · have hp := infinitesimalAlong_powers_littleO ha.2.2.1 ha.2.2.2.1 hb.2.2.2.1 hn hgt
    exact (nonzeroRatioLimitAlong_not_littleO
      (nonzeroRatioLimitAlong_comparisons_sameOrder ha.2.2.2.2 hb.2.2.2.2) hp).elim


theorem infinite_power_order_unique
    (ha : InfiniteMagnitudePowerOrderAlong D p f φ α)
    (hb : InfiniteMagnitudePowerOrderAlong D p f φ β) : α = β := by
  have hn := power_order_eventually_base_ne ha.1 ha.2.2.2.2
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have hp := infinite_magnitude_powers_littleO ha.2.2.1 ha.2.2.2.1 hb.2.2.2.1 hn hlt
    exact (nonzeroRatioLimitAlong_not_littleO
      (nonzeroRatioLimitAlong_comparisons_sameOrder ha.2.2.2.2 hb.2.2.2.2) hp).elim
  · exact heq
  · have hp := infinite_magnitude_powers_littleO ha.2.2.1 hb.2.2.2.1 ha.2.2.2.1 hn hgt
    exact (nonzeroRatioLimitAlong_not_littleO
      (nonzeroRatioLimitAlong_comparisons_sameOrder hb.2.2.2.2 ha.2.2.2.2) hp).elim


theorem asymptotic_power_order_along_unique (ha : AsymptoticPowerOrderAlong D p f φ α)
    (hb : AsymptoticPowerOrderAlong D p f φ β) : α = β := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact infinitesimal_power_order_unique ha hb
    · let : (domainApproachFilter D p).NeBot := ha.2.2.1.1
      have hzero : Tendsto (fun x ↦ |φ x|) (domainApproachFilter D p) (𝓝 0) := by
        simpa only [abs_zero] using ha.2.2.1.2.abs
      exact (not_tendsto_nhds_of_tendsto_atTop hb.2.2.1.2 0 hzero).elim
  · rcases hb with hb | hb
    · let : (domainApproachFilter D p).NeBot := hb.2.2.1.1
      have hzero : Tendsto (fun x ↦ |φ x|) (domainApproachFilter D p) (𝓝 0) := by
        simpa only [abs_zero] using hb.2.2.1.2.abs
      exact (not_tendsto_nhds_of_tendsto_atTop ha.2.2.1.2 0 hzero).elim
    · exact infinite_power_order_unique ha hb

/-- Dòng 3377: hệ số phần chính và phần dư o. -/
theorem asymptotic_power_order_along_has_principal_part (ho : AsymptoticPowerOrderAlong D p f φ α) :
    ∃ C : ℝ, HasPowerPrincipalPartAlong D p f φ α C ∧
      NonvanishingDenominatorLittleOAlong D p (fun x ↦ f x - powerPrincipalPart C α φ x) (fun x ↦ φ x ^ α) := by
  have hs : NonzeroRatioLimitAlong D p f (fun x ↦ φ x ^ α) := by
    rcases ho with hi | hi
    · exact hi.2.2.2.2
    · exact hi.2.2.2.2
  obtain ⟨C, hC, he, hr⟩ := nonzeroRatioLimitAlong_leading_part hs
  exact ⟨C, ⟨ho, hC, he⟩, hr⟩

end calculus.Chapter03.Section07Orders
