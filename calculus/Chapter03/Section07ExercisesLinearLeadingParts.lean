import calculus.Chapter03.Section07ExercisesDerivativeRatios
import calculus.Chapter03.Section07Orders
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# §3.7 — hai phần chính tuyến tính

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3499–3500, Bài tập 3.7.3(m,n).
-/

set_option autoImplicit false

open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesLinearLeadingParts

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07ExercisesDerivativeRatios


def logSineLeadingPartDomain : Set ℝ := {x | 0 < 1 + Real.sin x}


theorem hasPowerPrincipalPartAlong_one_of_hasDerivAt
    {D : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (ha : AccumulationPointOf D 0) (hf : HasDerivAt f C 0)
    (hf0 : f 0 = 0) (hC : C ≠ 0) :
    HasPowerPrincipalPartAlong D (.point 0) f (fun x ↦ x) 1 C := by
  have hp := (properLimitApproach_point_iff D 0).mpr ha
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter D (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfs : InfinitesimalAlong D (.point 0) f :=
    ⟨hp, by simpa only [domainApproachFilter, hf0] using hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  have hn : ∀ᶠ x in domainApproachFilter D (.point 0), x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx.2
  have hs := domainLimit_restrict (hasDerivAt_domainLimit_slope hf) ha
    (fun _ _ ↦ mem_univ _)
  have ht : Tendsto (fun x ↦ f x / x) (domainApproachFilter D (.point 0)) (𝓝 C) := by
    simpa only [domainApproachFilter, slope_fun_def_field, hf0, sub_zero] using (domainLimit_iff_tendsto ha).mp hs
  have had : EventuallyRealPowerDefinedAlong D (.point 0) (fun x ↦ x) 1 := by
    have hdomain : realPowerDomain 1 = (univ : Set ℝ) := by
      simpa using positive_integer_power_domain 1 (by norm_num)
    exact Filter.Eventually.of_forall fun x ↦ by simp [hdomain]
  have ho : InfinitesimalPowerOrderAlong D (.point 0) f (fun x ↦ x) 1 := by
    refine ⟨by norm_num, hfs, ⟨hp, hi⟩, had, hp, ?_, C, hC, ?_⟩
    · simpa only [Real.rpow_one] using hn
    · simpa only [Real.rpow_one] using ht
  refine ⟨Or.inl ho, hC, ?_⟩
  simpa only [NonvanishingAsymptoticEquivalenceAlong, powerPrincipalPart, Real.rpow_one, sub_zero] using
    nonvanishingAsymptoticEquivalenceAlong_linear_of_hasDerivAt ha hf hf0 hC

/-- Bài tập 3.7.3(m): ln(1+sin x)−x² có phần chính x, bậc 1. -/
theorem log_sine_sub_square_principal_part :
    HasPowerPrincipalPartAlong logSineLeadingPartDomain (.point 0)
      (fun x ↦ Real.log (1 + Real.sin x) - x ^ 2) (fun x ↦ x) 1 1 := by
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + Real.sin x) 1 0 := by
    simpa using (Real.hasDerivAt_sin (0 : ℝ)).const_add 1
  have hlog : HasDerivAt (fun x : ℝ ↦ Real.log (1 + Real.sin x)) 1 0 := by
    convert! harg.log (by norm_num : (1 : ℝ) + Real.sin 0 ≠ 0) using 1; norm_num
  have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 0 := by
    simpa [Pi.pow_apply, id_eq] using! (hasDerivAt_id (0 : ℝ)).pow 2
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (1 + Real.sin x) - x ^ 2) 1 0 := by
    simpa [Pi.sub_apply] using! hlog.sub hsq
  have hopen : IsOpen logSineLeadingPartDomain :=
    isOpen_lt continuous_const (continuous_const.add Real.continuous_sin)
  have ha : AccumulationPointOf logSineLeadingPartDomain 0 := by
    have hD : logSineLeadingPartDomain ∈ 𝓝 (0 : ℝ) :=
      hopen.mem_nhds (by norm_num [logSineLeadingPartDomain])
    simpa only [univ_inter] using accumulationPointOf_inter_nhds (univ_accumulation 0) hD
  exact hasPowerPrincipalPartAlong_one_of_hasDerivAt ha hf (by norm_num) (by norm_num)

/-- Bài tập 3.7.3(n): exp(x²+x)−exp(2x) có phần chính −x, bậc 1. -/
theorem exponential_difference_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.exp (x ^ 2 + x) - Real.exp (2 * x)) (fun x ↦ x) 1 (-1) := by
  have hleft : HasDerivAt (fun x : ℝ ↦ x ^ 2 + x) 1 0 := by
    simpa [Pi.pow_apply, id_eq, Pi.add_apply] using! ((hasDerivAt_id (0 : ℝ)).pow 2).add (hasDerivAt_id (0 : ℝ))
  have hright : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).const_mul 2
  have hf : HasDerivAt
      (fun x : ℝ ↦ Real.exp (x ^ 2 + x) - Real.exp (2 * x)) (-1) 0 := by
    convert! hleft.exp.sub hright.exp using 1; norm_num
  exact hasPowerPrincipalPartAlong_one_of_hasDerivAt
    (univ_accumulation 0) hf (by norm_num) (by norm_num)

end calculus.Chapter03.Section07ExercisesLinearLeadingParts
