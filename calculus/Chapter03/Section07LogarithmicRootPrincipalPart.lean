import calculus.Chapter03.Section07Orders
import calculus.Chapter03.Section07Examples
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.7 — Bài tập 3.7.3(e): phần chính có số mũ không nguyên

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3491: ln(1+√x)−tan x.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07LogarithmicRootPrincipalPart

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07Orders


def logarithmicRootTangentDomain : Set ℝ := {x | 0 ≤ x ∧ Real.cos x ≠ 0}


theorem nonnegative_domain_accumulation : AccumulationPointOf (Ici 0) 0 := by
  intro δ hδ
  refine ⟨δ / 2, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ δ / 2
    positivity
  · exact ne_of_gt (by positivity)
  · linarith
  · linarith


theorem logarithmic_root_tangent_accumulation :
    AccumulationPointOf logarithmicRootTangentDomain 0 := by
  have hc : {x : ℝ | Real.cos x ≠ 0} ∈ 𝓝 (0 : ℝ) :=
    Real.continuous_cos.continuousAt.tendsto.eventually_ne (by simp : Real.cos 0 ≠ 0)
  change AccumulationPointOf (Ici 0 ∩ {x : ℝ | Real.cos x ≠ 0}) 0
  exact accumulationPointOf_inter_nhds nonnegative_domain_accumulation hc


theorem hasPowerPrincipalPartAlong_real_of_tendsto
    {D : Set ℝ} {p : LimitApproach} {f φ : ℝ → ℝ} {α C : ℝ}
    (hφ : InfinitesimalAlong D p φ) (hα : 0 < α)
    (had : EventuallyRealPowerDefinedAlong D p φ α)
    (hn : ∀ᶠ x in domainApproachFilter D p, φ x ≠ 0)
    (hC : C ≠ 0) (hf : Tendsto f (domainApproachFilter D p) (𝓝 0))
    (ht : Tendsto (fun x ↦ f x / φ x ^ α) (domainApproachFilter D p) (𝓝 C)) :
    HasPowerPrincipalPartAlong D p f φ α C := by
  have hp := hφ.1
  have hpow : ∀ᶠ x in domainApproachFilter D p, φ x ^ α ≠ 0 := by
    filter_upwards [had, hn] with x hx hx0
    exact real_power_ne_zero hx hx0
  have ho : InfinitesimalPowerOrderAlong D p f φ α :=
    ⟨hα, ⟨hp, hf⟩, hφ, had, hp, hpow, C, hC, ht⟩
  refine ⟨Or.inl ho, hC, hp, ?_, ?_⟩
  · simpa only [powerPrincipalPart] using hpow.mono fun x hx ↦ mul_ne_zero hC hx
  · have hs : Tendsto (fun x ↦ (f x / φ x ^ α) / C)
        (domainApproachFilter D p) (𝓝 (1 : ℝ)) := by
      simpa only [div_self hC] using ht.div_const C
    apply hs.congr
    intro x
    simp only [powerPrincipalPart]
    rw [div_div, mul_comm (φ x ^ α) C]


theorem logarithmic_root_eventually_positive :
    ∀ᶠ x in domainApproachFilter logarithmicRootTangentDomain (.point 0), 0 < x := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact lt_of_le_of_ne hx.1.1 (by simpa [ne_comm] using hx.2)

/-- Bài tập 3.7.3(e): phần chính √x, bậc 1/2, khi x→0⁺. -/
theorem logarithmic_root_sub_tangent_principal_part :
    HasPowerPrincipalPartAlong logarithmicRootTangentDomain (.point 0)
      (fun x ↦ Real.log (1 + Real.sqrt x) - Real.tan x) (fun x ↦ x) (1 / 2) 1 := by
  have hp := (properLimitApproach_point_iff _ 0).mpr logarithmic_root_tangent_accumulation
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hi.sqrt
  have hsne : ∀ᶠ x in domainApproachFilter logarithmicRootTangentDomain (.point 0),
      Real.sqrt x ≠ 0 := logarithmic_root_eventually_positive.mono fun x hx ↦ (Real.sqrt_pos.mpr hx).ne'
  have hsp : Tendsto (fun x : ℝ ↦ Real.sqrt x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0))
      (domainApproachFilter univ (.point 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hs, hsne.mono fun x hx ↦ ⟨mem_univ _, hx⟩⟩
  have hl : HasDerivAt (fun u : ℝ ↦ Real.log (1 + u)) 1 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
      using 1; norm_num
  have hlq : Tendsto (fun u : ℝ ↦ Real.log (1 + u) / u)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, add_zero, Real.log_one, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope hl)
  have hr : domainApproachFilter logarithmicRootTangentDomain (.point 0) ≤
      domainApproachFilter univ (.point 0) := nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ _))
  have htq : Tendsto (fun x : ℝ ↦ Real.tan x / Real.sqrt x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 0) := by
    apply (show Tendsto (fun x : ℝ ↦ (Real.tan x / x) * Real.sqrt x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 0) from by
        simpa only [mul_zero] using (tangent_equivalent_identity_zero.2.2.mono_left hr).mul hs).congr'
    filter_upwards [self_mem_nhdsWithin, hsne] with x hx hx0
    have hsq := Real.sq_sqrt hx.1.1
    have hn : x ≠ 0 := by simpa using hx.2
    field_simp [hn, hx0]
    nlinarith [congrArg (fun y : ℝ ↦ Real.tan x * y) hsq]
  have hf : Tendsto (fun x : ℝ ↦ Real.log (1 + Real.sqrt x) - Real.tan x)
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 0) := by
    have hlog : ContinuousAt (fun x : ℝ ↦ Real.log (1 + Real.sqrt x)) 0 :=
      (continuous_const.continuousAt.add Real.continuous_sqrt.continuousAt).log (by norm_num)
    have htan := (Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)).continuousAt
    simpa only [domainApproachFilter, Real.sqrt_zero, add_zero, Real.log_one, Pi.sub_apply, Real.tan_zero, sub_zero] using!
      (hlog.sub htan).tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun x : ℝ ↦ (Real.log (1 + Real.sqrt x) - Real.tan x) / x ^ (1 / 2 : ℝ))
      (domainApproachFilter logarithmicRootTangentDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, sub_zero, sub_div, ← Real.sqrt_eq_rpow] using
      (hlq.comp hsp).sub htq
  have had : EventuallyRealPowerDefinedAlong logarithmicRootTangentDomain (.point 0)
      (fun x ↦ x) (1 / 2) := by
    filter_upwards [logarithmic_root_eventually_positive] with x hx
    unfold realPowerDomain
    split_ifs
    · exact mem_univ _
    · exact hx.ne'
    · exact hx
  exact hasPowerPrincipalPartAlong_real_of_tendsto ⟨hp, hi⟩ (by norm_num) had
    (logarithmic_root_eventually_positive.mono fun x hx ↦ hx.ne') (by norm_num) hf hquot

end calculus.Chapter03.Section07LogarithmicRootPrincipalPart
