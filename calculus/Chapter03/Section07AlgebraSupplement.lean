import calculus.Chapter03.Section07

/-! §3.7 — bỏ vô cùng bé bậc cao, phần chính và thay thế trong thương. -/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07AlgebraSupplement
open calculus.Chapter03.Section07

variable {D : Set ℝ} {p : LimitApproach} {f g h k : ℝ → ℝ}


theorem nonvanishingAsymptoticEquivalenceAlong_mathlib (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) :
    Asymptotics.IsEquivalent (domainApproachFilter D p) f g := by
  exact Asymptotics.isEquivalent_of_tendsto_one hf.2.2

/-- Dòng 3360–3363: bỏ số hạng vô cùng bé bậc cao trong tổng. -/
theorem infinitesimal_add_higher_equivalent (hf : InfinitesimalAlong D p f)
    (hg : InfinitesimalAlong D p g) (hgf : NonvanishingDenominatorLittleOAlong D p g f) :
    EquivalentInfinitesimalsAlong D p (fun x ↦ f x + g x) f := by
  have hs : InfinitesimalAlong D p (fun x ↦ f x + g x) :=
    ⟨hf.1, by simpa only [zero_add] using hf.2.add hg.2⟩
  refine ⟨hs, hf, (nonvanishingAsymptoticEquivalenceAlong_iff_sub_littleO hf.1 hgf.2.1).mpr ?_⟩
  simpa only [add_sub_cancel_left] using hgf


theorem nonvanishingDenominatorLittleOAlong_const_mul_right {C : ℝ} (hC : C ≠ 0)
    (hf : NonvanishingDenominatorLittleOAlong D p f g) :
    NonvanishingDenominatorLittleOAlong D p f (fun x ↦ C * g x) := by
  refine ⟨hf.1, hf.2.1.mono (fun x hx ↦ mul_ne_zero hC hx), ?_⟩
  have ht : Tendsto (fun x ↦ (f x / g x) / C) (domainApproachFilter D p) (𝓝 0) := by
    simpa only [zero_div] using hf.2.2.div_const C
  apply ht.congr'
  filter_upwards [hf.2.1] with x hx
  field_simp

/-- Dòng 3377–3378: hệ số của phần chính và phần dư o. -/
theorem nonzeroRatioLimitAlong_leading_part (hf : NonzeroRatioLimitAlong D p f g) :
    ∃ C : ℝ, C ≠ 0 ∧ NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ C * g x) ∧
      NonvanishingDenominatorLittleOAlong D p (fun x ↦ f x - C * g x) g := by
  obtain ⟨C, hC, ht⟩ := hf.2.2
  have he : NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ C * g x) := by
    refine ⟨hf.1, hf.2.1.mono (fun x hx ↦ mul_ne_zero hC hx), ?_⟩
    have hu : Tendsto (fun x ↦ (f x / g x) / C) (domainApproachFilter D p) (𝓝 1) := by
      simpa only [div_self hC] using ht.div_const C
    apply hu.congr'
    filter_upwards [hf.2.1] with x hx
    field_simp
  refine ⟨C, hC, he, hf.1, hf.2.1, ?_⟩
  have hu : Tendsto (fun x ↦ f x / g x - C) (domainApproachFilter D p) (𝓝 0) := by
    simpa only [sub_self] using ht.sub (tendsto_const_nhds (x := C))
  apply hu.congr'
  filter_upwards [hf.2.1] with x hx
  field_simp


theorem equivalent_quotients_limit_iff
    (_hf : InfinitesimalAlong D p f) (_hg : InfinitesimalAlong D p g)
    (_hh : InfinitesimalAlong D p h) (_hk : InfinitesimalAlong D p k)
    (hfh : NonvanishingAsymptoticEquivalenceAlong D p f h) (hgk : NonvanishingAsymptoticEquivalenceAlong D p g k) :
    (∀ L : ℝ, Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) (𝓝 L) ↔
      Tendsto (fun x ↦ h x / k x) (domainApproachFilter D p) (𝓝 L)) ∧
    (Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) atTop ↔
      Tendsto (fun x ↦ h x / k x) (domainApproachFilter D p) atTop) ∧
    (Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) atBot ↔
      Tendsto (fun x ↦ h x / k x) (domainApproachFilter D p) atBot) := by
  have he := (nonvanishingAsymptoticEquivalenceAlong_mathlib hfh).div (nonvanishingAsymptoticEquivalenceAlong_mathlib hgk)
  exact ⟨fun _ ↦ he.tendsto_nhds_iff, he.tendsto_atTop_iff, he.tendsto_atBot_iff⟩

end calculus.Chapter03.Section07AlgebraSupplement
