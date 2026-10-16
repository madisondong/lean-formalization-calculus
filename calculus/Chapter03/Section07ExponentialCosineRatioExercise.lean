import calculus.Chapter03.Section07CosineRatioExercises
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
§3.7 — Bài tập 3.7.11(d)

Nguồn: dòng 3686.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07ExponentialCosineRatioExercise
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07CosineRatioExercises


def exponentialCosineRatioDomain : Set ℝ := {x | Real.sin x ^ 3 + 2 * x ^ 4 ≠ 0}


theorem normalized_exponential_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.exp x - 1) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
  have hd : HasDerivAt Real.exp 1 0 := by
    simpa only [Real.exp_zero] using Real.hasDerivAt_exp 0
  have ht := (domainLimit_iff_tendsto (univ_accumulation 0)).mp
    (hasDerivAt_domainLimit_slope hd)
  apply ht.congr'
  exact Eventually.of_forall fun x ↦ by rw [slope_def_field, Real.exp_zero, sub_zero]

/-- Bài tập 3.7.11(d): giới hạn bằng −1/2. -/
theorem exponential_cosine_ratio_at_zero :
    DomainLimit exponentialCosineRatioDomain
      (fun x ↦ ((Real.exp x - 1) * (Real.cos x - 1)) /
        (Real.sin x ^ 3 + 2 * x ^ 4)) 0 (-1 / 2) := by
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun x : ℝ ↦ (Real.cos x - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    convert! (normalized_scaled_cosine 1).neg using 1
    · ext x; simp only [one_mul]; ring
    · norm_num
  have hf : Tendsto (fun x : ℝ ↦ ((Real.exp x - 1) * (Real.cos x - 1)) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ ((Real.exp x - 1) / x) *
      ((Real.cos x - 1) / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) from by
        simpa only [one_mul] using normalized_exponential_at_zero.mul hc).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hg : Tendsto (fun x : ℝ ↦ (Real.sin x ^ 3 + 2 * x ^ 4) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ (Real.sin x / x) ^ 3 + 2 * x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) from by
        simpa only [one_pow, mul_zero, add_zero] using
          (sine_equivalent_identity_zero.2.2.pow 3).add (hi.const_mul 2)).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ exponentialCosineRatioDomain :=
    (hg.eventually_ne one_ne_zero).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have he := domainApproachFilter_eq_univ_of_eventually_mem hD
  have hp : NontrivialDomainApproach exponentialCosineRatioDomain (.point 0) := by
    change (domainApproachFilter exponentialCosineRatioDomain (.point 0)).NeBot
    rw [he]
    exact (properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0)
  apply (domainLimit_iff_tendsto
    ((properLimitApproach_point_iff exponentialCosineRatioDomain 0).mp hp)).mpr
  change Tendsto _ (domainApproachFilter exponentialCosineRatioDomain (.point 0)) _
  rw [he]
  apply (show Tendsto (fun x : ℝ ↦ (((Real.exp x - 1) * (Real.cos x - 1)) / x ^ 3) /
      ((Real.sin x ^ 3 + 2 * x ^ 4) / x ^ 3))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) from by
        simpa only [Pi.div_apply, div_one] using! hf.div hg one_ne_zero).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_div_div_cancel_right₀ (pow_ne_zero 3 hx) _ _

end calculus.Chapter03.Section07ExponentialCosineRatioExercise
