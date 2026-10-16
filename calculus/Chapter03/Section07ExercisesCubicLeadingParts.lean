import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.7 — ba phần chính bậc ba

Nguồn: Bài tập 3.7.3(a,b,l), `Ch3_gioihanhamso.tex`, dòng 3487, dòng 3488, dòng 3498.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesCubicLeadingParts

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts


def arctangentLeadingPartDomain : Set ℝ := {x | x ^ 5 + x ^ 2 + 1 ≠ 0}


theorem arctangent_leading_part_domain_nhds :
    arctangentLeadingPartDomain ∈ 𝓝 (0 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ ↦ x ^ 5 + x ^ 2 + 1) 0 := by fun_prop
  exact hc.tendsto.eventually_ne (by norm_num : (0 : ℝ) ^ 5 + 0 ^ 2 + 1 ≠ 0)


theorem arctangent_leading_part_domain_accumulation :
    AccumulationPointOf arctangentLeadingPartDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) arctangent_leading_part_domain_nhds

/-- Bài tập 3.7.3(a): tích có phần chính 12x³. -/
theorem exponential_sine_square_product_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ (Real.exp (3 * x) - 1) * (Real.sin (2 * x) ^ 2 + 3 * x ^ 3))
      (fun x ↦ x) 3 12 := by
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (3 * x) - 1) 3 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 3).exp).sub_const 1
  have hs : HasDerivAt (fun x : ℝ ↦ Real.sin (2 * x)) 2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).sin
  have het : Tendsto (fun x : ℝ ↦ (Real.exp (3 * x) - 1) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (3 : ℝ)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, mul_zero, Real.exp_zero, sub_self, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope he)
  have hst : Tendsto (fun x : ℝ ↦ Real.sin (2 * x) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, mul_zero, Real.sin_zero, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope hs)
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦
      ((Real.exp (3 * x) - 1) / x) * ((Real.sin (2 * x) / x) ^ 2 + 3 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (12 : ℝ)) := by
    convert! het.mul ((hst.pow 2).add (hi.const_mul 3)) using 1; norm_num
  apply hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0)
    (by norm_num : 0 < (3 : ℕ)) (by norm_num : (12 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦
        (Real.exp (3 * x) - 1) * (Real.sin (2 * x) ^ 2 + 3 * x ^ 3)) 0 := by fun_prop
    simpa [domainApproachFilter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]

/-- Bài tập 3.7.3(b): phần chính x³. -/
theorem cosine_linear_cubic_cancellation_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ x * Real.cos (2 * x) - x + 3 * x ^ 3) (fun x ↦ x) 3 1 := by
  have ht : Tendsto (fun x : ℝ ↦ 3 - 2 * (Real.sin x / x) ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    convert! tendsto_const_nhds.sub ((sine_equivalent_identity_zero.2.2.pow 2).const_mul 2)
      using 1; norm_num
  apply hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0)
    (by norm_num : 0 < (3 : ℕ)) (by norm_num : (1 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦ x * Real.cos (2 * x) - x + 3 * x ^ 3) 0 := by
      fun_prop
    simpa [domainApproachFilter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    have hcos : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
      nlinarith [Real.cos_two_mul x, Real.sin_sq_add_cos_sq x]
    rw [hcos]
    field_simp [hx]; ring

/-- Bài tập 3.7.3(l): x² arctan x/(x⁵+x²+1) có phần chính x³. -/
theorem rational_arctangent_cubic_principal_part :
    HasPowerPrincipalPartAlong arctangentLeadingPartDomain (.point 0)
      (fun x ↦ x ^ 2 * Real.arctan x / (x ^ 5 + x ^ 2 + 1)) (fun x ↦ x) 3 1 := by
  have ha : HasDerivAt Real.arctan 1 0 := by
    simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have hat : Tendsto (fun x : ℝ ↦ Real.arctan x / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, Real.arctan_zero, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope ha)
  have hd : Tendsto (fun x : ℝ ↦ x ^ 5 + x ^ 2 + 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ 5 + x ^ 2 + 1) 0 := by fun_prop
    simpa [domainApproachFilter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ (Real.arctan x / x) / (x ^ 5 + x ^ 2 + 1))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, div_one] using! hat.div hd (by norm_num : (1 : ℝ) ≠ 0)
  apply hasPowerPrincipalPartAlong_nat_of_tendsto arctangent_leading_part_domain_accumulation
    (by norm_num : 0 < (3 : ℕ)) (by norm_num : (1 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦
        x ^ 2 * Real.arctan x / (x ^ 5 + x ^ 2 + 1)) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    simpa [domainApproachFilter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply (ht.mono_left (nhdsWithin_mono 0
      (sdiff_subset_sdiff_left (subset_univ arctangentLeadingPartDomain)))).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxn : x ≠ 0 := by simpa using hx.2
    have hden : x ^ 5 + x ^ 2 + 1 ≠ 0 := hx.1
    field_simp [hxn, hden]

end calculus.Chapter03.Section07ExercisesCubicLeadingParts
