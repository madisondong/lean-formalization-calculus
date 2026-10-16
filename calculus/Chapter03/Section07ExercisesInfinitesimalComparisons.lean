import calculus.Chapter03.Section07Orders
import calculus.Chapter03.Section07Examples
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.7 — Bài tập 3.7.1: so sánh bốn vô cùng bé với x

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3467–3475; các câu (a,b,c,d) ở dòng 3470–3473.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesInfinitesimalComparisons

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Supplement calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section01Powers calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Orders


def tangentComparisonDomain : Set ℝ := {x | Real.cos x ≠ 0}


def shiftedRootComparisonDomain : Set ℝ := Ici (-9)


def arctangentRootComparisonDomain : Set ℝ := Ici 0


theorem tangent_comparison_domain_nhds : tangentComparisonDomain ∈ 𝓝 (0 : ℝ) := by
  exact (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.eventually_ne (by simp : Real.cos 0 ≠ 0)


theorem tangent_comparison_domain_accumulation :
    AccumulationPointOf tangentComparisonDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) tangent_comparison_domain_nhds


theorem shifted_root_comparison_domain_nhds : shiftedRootComparisonDomain ∈ 𝓝 (0 : ℝ) := by
  have hn : Ioi (-9 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Ioi.mem_nhds (by norm_num)
  exact mem_of_superset hn (fun x hx ↦ (show -9 ≤ x from hx.le))


theorem shifted_root_comparison_domain_accumulation :
    AccumulationPointOf shiftedRootComparisonDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) shifted_root_comparison_domain_nhds


theorem arctangent_root_comparison_domain_accumulation :
    AccumulationPointOf arctangentRootComparisonDomain 0 := by
  intro δ hδ
  refine ⟨δ / 2, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ δ / 2
    positivity
  · exact ne_of_gt (by positivity)
  · linarith
  · linarith


theorem positive_base_mem_real_power_domain {x α : ℝ} (hx : 0 < x) :
    x ∈ realPowerDomain α := by
  unfold realPowerDomain
  split_ifs
  · exact mem_univ _
  · exact hx.ne'
  · exact hx


theorem absolute_trial_power_admissible (α : ℝ) :
    EventuallyRealPowerDefinedAlong univ (.point 0) (fun x ↦ |x|) α := by
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact positive_base_mem_real_power_domain (abs_pos.mpr hx)


theorem sine_square_cube_root_abs_power (x : ℝ) :
    signedCubeRoot (Real.sin x ^ 2) = |Real.sin x| ^ (2 / 3 : ℝ) := by
  rw [signedCubeRoot, if_pos (sq_nonneg _), ← sq_abs (Real.sin x), ← Real.rpow_two]
  rw [← Real.rpow_mul (abs_nonneg (Real.sin x))]
  norm_num


theorem cube_root_sine_square_magnitude_power_order :
    InfinitesimalPowerOrderAlong univ (.point 0)
      (fun x ↦ signedCubeRoot (Real.sin x ^ 2)) (fun x ↦ |x|) (2 / 3) := by
  have hp : NontrivialDomainApproach univ (.point 0) :=
    (properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0)
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun x : ℝ ↦ |x|) (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [abs_zero] using hi.abs
  have hs : Tendsto (fun x : ℝ ↦ |Real.sin x|)
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [domainApproachFilter, Real.sin_zero, abs_zero] using
      (Real.continuous_sin.continuousAt (x := (0 : ℝ))).tendsto.abs.mono_left nhdsWithin_le_nhds
  have hf : Tendsto (fun x ↦ signedCubeRoot (Real.sin x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    apply (hs.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 2 / 3)).congr
    intro x
    exact (sine_square_cube_root_abs_power x).symm
  have hr : Tendsto (fun x : ℝ ↦ |Real.sin x / x|)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [abs_one] using sine_equivalent_identity_zero.2.2.abs
  have hq : Tendsto (fun x : ℝ ↦ |Real.sin x / x| ^ (2 / 3 : ℝ))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.one_rpow] using hr.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  refine ⟨by norm_num, ⟨hp, hf⟩, ⟨hp, ha⟩, absolute_trial_power_admissible (2 / 3),
    hp, ?_, 1, by norm_num, ?_⟩
  · filter_upwards [punctured_zero_eventually_ne] with x hx
    exact (Real.rpow_pos_of_pos (abs_pos.mpr hx) (2 / 3 : ℝ)).ne'
  · apply hq.congr
    intro x
    simp only
    rw [sine_square_cube_root_abs_power, abs_div,
      Real.div_rpow (abs_nonneg (Real.sin x)) (abs_nonneg x)]

/-- Bài tập 3.7.1(a): (tan x)³=o(x) khi x→0. -/
theorem tangent_cube_comparison_zero :
    InfinitesimalAlong tangentComparisonDomain (.point 0) (fun x ↦ Real.tan x ^ 3) ∧
      InfinitesimalAlong tangentComparisonDomain (.point 0) (fun x ↦ x) ∧
      NonvanishingDenominatorLittleOAlong tangentComparisonDomain (.point 0) (fun x ↦ Real.tan x ^ 3) (fun x ↦ x) := by
  have hp : NontrivialDomainApproach tangentComparisonDomain (.point 0) :=
    (properLimitApproach_point_iff _ 0).mpr tangent_comparison_domain_accumulation
  have hr : domainApproachFilter tangentComparisonDomain (.point 0) ≤
      domainApproachFilter univ (.point 0) :=
    nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ _))
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter tangentComparisonDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hd : HasDerivAt Real.tan 1 0 := by
    simpa using Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)
  have ht : Tendsto Real.tan (domainApproachFilter tangentComparisonDomain (.point 0)) (𝓝 0) := by
    simpa only [domainApproachFilter, Real.tan_zero] using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun x : ℝ ↦ Real.tan x / x)
      (domainApproachFilter tangentComparisonDomain (.point 0)) (𝓝 (1 : ℝ)) :=
    tangent_equivalent_identity_zero.2.2.mono_left hr
  refine ⟨⟨hp, by simpa using ht.pow 3⟩, ⟨hp, hi⟩, hp,
    punctured_zero_eventually_ne.filter_mono hr, ?_⟩
  apply (show Tendsto (fun x : ℝ ↦ (Real.tan x / x) * Real.tan x ^ 2)
      (domainApproachFilter tangentComparisonDomain (.point 0)) (𝓝 0) from by
        simpa using hquot.mul (ht.pow 2)).congr
  intro x
  ring

/-- Bài tập 3.7.1(b): x=o(∛(sin²x)) khi x→0 từ hai phía. -/
theorem identity_cube_root_sine_square_comparison_zero :
    InfinitesimalAlong univ (.point 0) (fun x ↦ signedCubeRoot (Real.sin x ^ 2)) ∧
      InfinitesimalAlong univ (.point 0) (fun x ↦ x) ∧
      NonvanishingDenominatorLittleOAlong univ (.point 0) (fun x ↦ x) (fun x ↦ signedCubeRoot (Real.sin x ^ 2)) := by
  have ho := cube_root_sine_square_magnitude_power_order
  have ha : NonvanishingDenominatorLittleOAlong univ (.point 0) (fun x ↦ |x|)
      (fun x ↦ signedCubeRoot (Real.sin x ^ 2)) := by
    simpa only [Real.rpow_one] using
      (infinitesimal_power_order_comparisons ho (absolute_trial_power_admissible 1)).2
        (by norm_num : (2 / 3 : ℝ) < 1)
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨ho.2.1, ⟨ha.1, hi⟩, ha.1, ha.2.1, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, abs_div, abs_abs] using
    (tendsto_zero_iff_norm_tendsto_zero.mp ha.2.2)

/-- Bài tập 3.7.1(c): √(9+x)−3 cùng bậc với x, với giới hạn thương 1/6. -/
theorem shifted_square_root_comparison_zero :
    InfinitesimalAlong shiftedRootComparisonDomain (.point 0) (fun x ↦ Real.sqrt (9 + x) - 3) ∧
      InfinitesimalAlong shiftedRootComparisonDomain (.point 0) (fun x ↦ x) ∧
      NonzeroRatioLimitAlong shiftedRootComparisonDomain (.point 0) (fun x ↦ Real.sqrt (9 + x) - 3) (fun x ↦ x) ∧
      Tendsto (fun x ↦ (Real.sqrt (9 + x) - 3) / x)
        (domainApproachFilter shiftedRootComparisonDomain (.point 0)) (𝓝 (1 / 6 : ℝ)) := by
  have hs9 : Real.sqrt (9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp : NontrivialDomainApproach shiftedRootComparisonDomain (.point 0) :=
    (properLimitApproach_point_iff _ 0).mpr shifted_root_comparison_domain_accumulation
  have hr : domainApproachFilter shiftedRootComparisonDomain (.point 0) ≤
      domainApproachFilter univ (.point 0) :=
    nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ _))
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter shiftedRootComparisonDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hd : HasDerivAt (fun x : ℝ ↦ Real.sqrt (9 + x) - 3) (1 / 6) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_add 9).sqrt
      (by norm_num : (9 : ℝ) + 0 ≠ 0)).sub_const 3 using 1; norm_num [hs9]
  have hf : Tendsto (fun x : ℝ ↦ Real.sqrt (9 + x) - 3)
      (domainApproachFilter shiftedRootComparisonDomain (.point 0)) (𝓝 0) := by
    convert! hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num [domainApproachFilter, hs9]
  have hq : Tendsto (fun x : ℝ ↦ (Real.sqrt (9 + x) - 3) / x)
      (domainApproachFilter shiftedRootComparisonDomain (.point 0)) (𝓝 (1 / 6 : ℝ)) := by
    have hs := (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope hd)
    have hs' : Tendsto (fun x : ℝ ↦ (Real.sqrt (9 + x) - 3) / x)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 / 6 : ℝ)) := by
      simpa only [domainApproachFilter, slope_fun_def_field, add_zero, hs9,
        sub_self, sub_zero] using hs
    exact hs'.mono_left hr
  exact ⟨⟨hp, hf⟩, ⟨hp, hi⟩, ⟨hp, punctured_zero_eventually_ne.filter_mono hr,
    1 / 6, by norm_num, hq⟩, hq⟩

/-- Bài tập 3.7.1(d): x=o(arctan √x) khi x→0⁺. -/
theorem identity_arctangent_square_root_comparison_zero :
    InfinitesimalAlong arctangentRootComparisonDomain (.point 0) (fun x ↦ Real.arctan (Real.sqrt x)) ∧
      InfinitesimalAlong arctangentRootComparisonDomain (.point 0) (fun x ↦ x) ∧
      NonvanishingDenominatorLittleOAlong arctangentRootComparisonDomain (.point 0) (fun x ↦ x)
        (fun x ↦ Real.arctan (Real.sqrt x)) := by
  have hp : NontrivialDomainApproach arctangentRootComparisonDomain (.point 0) :=
    (properLimitApproach_point_iff _ 0).mpr arctangent_root_comparison_domain_accumulation
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter arctangentRootComparisonDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt x)
      (domainApproachFilter arctangentRootComparisonDomain (.point 0)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hi.sqrt
  have hn : ∀ᶠ x in domainApproachFilter arctangentRootComparisonDomain (.point 0),
      Real.sqrt x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sqrt_ne_zero (show 0 ≤ x from hx.1)).mpr (by simpa using hx.2)
  have hsp : Tendsto (fun x : ℝ ↦ Real.sqrt x)
      (domainApproachFilter arctangentRootComparisonDomain (.point 0))
      (domainApproachFilter univ (.point 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hs, ?_⟩
    exact hn.mono fun x hx ↦ ⟨mem_univ _, hx⟩
  have hd : HasDerivAt Real.arctan 1 0 := by simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have hq : Tendsto (fun x : ℝ ↦ Real.arctan x / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, Real.arctan_zero, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope hd)
  have har : Tendsto (fun x : ℝ ↦ Real.arctan (Real.sqrt x) / Real.sqrt x)
      (domainApproachFilter arctangentRootComparisonDomain (.point 0)) (𝓝 (1 : ℝ)) :=
    hq.comp hsp
  have hf : Tendsto (fun x : ℝ ↦ Real.arctan (Real.sqrt x))
      (domainApproachFilter arctangentRootComparisonDomain (.point 0)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.arctan_zero] using (Real.continuous_arctan.tendsto 0).comp hs
  have han : ∀ᶠ x in domainApproachFilter arctangentRootComparisonDomain (.point 0),
      Real.arctan (Real.sqrt x) ≠ 0 :=
    hn.mono fun x hx hz ↦ hx (Real.arctan_eq_zero_iff.mp hz)
  refine ⟨⟨hp, hf⟩, ⟨hp, hi⟩, hp, han, ?_⟩
  apply (show Tendsto (fun x : ℝ ↦ Real.sqrt x / (Real.arctan (Real.sqrt x) / Real.sqrt x))
      (domainApproachFilter arctangentRootComparisonDomain (.point 0)) (𝓝 0) from by
        simpa [Pi.div_apply] using! hs.div har (by norm_num : (1 : ℝ) ≠ 0)).congr'
  filter_upwards [self_mem_nhdsWithin, hn, han] with x hx hsn hanx
  have hx0 : 0 ≤ x := hx.1
  field_simp [hsn, hanx]
  nlinarith [Real.sq_sqrt hx0]

end calculus.Chapter03.Section07ExercisesInfinitesimalComparisons
