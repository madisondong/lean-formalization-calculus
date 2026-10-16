import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.7 — Bài tập 3.7.3(i): 2 sin x − tan(2x)

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3483–3501, mục (i) dòng 3495.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesDoubleAngleCubicPart

open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts


def doubleAngleTangentDomain : Set ℝ := {x | Real.cos (2 * x) ≠ 0}


theorem double_angle_tangent_domain_nhds : doubleAngleTangentDomain ∈ 𝓝 (0 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ ↦ Real.cos (2 * x)) 0 := by fun_prop
  exact hc.tendsto.eventually_ne (by norm_num : Real.cos (2 * (0 : ℝ)) ≠ 0)


theorem double_angle_tangent_domain_accumulation :
    AccumulationPointOf doubleAngleTangentDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) double_angle_tangent_domain_nhds


theorem twice_sine_sub_double_tangent_div_cube_tendsto :
    Tendsto (fun x : ℝ ↦ (2 * Real.sin x - Real.tan (2 * x)) / x ^ 3)
      (domainApproachFilter doubleAngleTangentDomain (.point 0)) (𝓝 (-3 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hphase : Tendsto (fun x : ℝ ↦ 2 * x)
      (domainApproachFilter univ (.point 0)) (domainApproachFilter univ (.point 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hi.const_mul 2, ?_⟩
    filter_upwards [punctured_zero_eventually_ne] with x hx
    exact ⟨mem_univ _, mul_ne_zero (by norm_num) hx⟩
  have hdouble : Tendsto (fun x : ℝ ↦
      (Real.sin (2 * x) - Real.tan (2 * x)) / (2 * x) ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) :=
    sine_sub_tangent_div_cube_tendsto.comp hphase
  have hfirst : Tendsto (fun x : ℝ ↦
      8 * ((Real.sin (2 * x) - Real.tan (2 * x)) / (2 * x) ^ 3))
      (domainApproachFilter univ (.point 0)) (𝓝 (-4 : ℝ)) := by
    convert! hdouble.const_mul 8 using 1; norm_num
  have hsecond : Tendsto (fun x : ℝ ↦
      2 * ((Real.sin x / x) * ((1 - Real.cos x) / x ^ 2)))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    convert! (sine_equivalent_identity_zero.2.2.mul one_sub_cos_div_square_tendsto).const_mul 2
      using 1; norm_num
  have ht : Tendsto (fun x : ℝ ↦
      8 * ((Real.sin (2 * x) - Real.tan (2 * x)) / (2 * x) ^ 3) +
        2 * ((Real.sin x / x) * ((1 - Real.cos x) / x ^ 2)))
      (domainApproachFilter univ (.point 0)) (𝓝 (-3 : ℝ)) := by
    convert! hfirst.add hsecond using 1; norm_num
  have hnormalized : Tendsto (fun x : ℝ ↦ (2 * Real.sin x - Real.tan (2 * x)) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-3 : ℝ)) := by
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    rw [Real.sin_two_mul]
    field_simp [hx]; ring
  exact hnormalized.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ doubleAngleTangentDomain)))


theorem twice_sine_sub_double_tangent_infinitesimal :
    Tendsto (fun x : ℝ ↦ 2 * Real.sin x - Real.tan (2 * x))
      (domainApproachFilter doubleAngleTangentDomain (.point 0)) (𝓝 0) := by
  have hphase : ContinuousAt (fun x : ℝ ↦ 2 * x) 0 := by fun_prop
  have ht : ContinuousAt (fun x : ℝ ↦ Real.tan (2 * x)) 0 :=
    (Real.continuousAt_tan.mpr (by norm_num : Real.cos (2 * (0 : ℝ)) ≠ 0)).comp hphase
  have hf : ContinuousAt (fun x : ℝ ↦ 2 * Real.sin x - Real.tan (2 * x)) 0 :=
    ((Real.continuous_sin.continuousAt (x := (0 : ℝ))).const_mul 2).sub ht
  simpa only [domainApproachFilter, Real.sin_zero, mul_zero, Real.tan_zero, sub_zero] using
    hf.tendsto.mono_left nhdsWithin_le_nhds

/-- Bài tập 3.7.3(i): phần chính −3x³, bậc 3, khi x→0 từ hai phía. -/
theorem twice_sine_sub_double_tangent_principal_part :
    HasPowerPrincipalPartAlong doubleAngleTangentDomain (.point 0)
      (fun x ↦ 2 * Real.sin x - Real.tan (2 * x)) (fun x ↦ x) 3 (-3) := by
  exact hasPowerPrincipalPartAlong_nat_of_tendsto double_angle_tangent_domain_accumulation
    (by norm_num : 0 < (3 : ℕ)) (by norm_num : (-3 : ℝ) ≠ 0)
    twice_sine_sub_double_tangent_infinitesimal twice_sine_sub_double_tangent_div_cube_tendsto

end calculus.Chapter03.Section07ExercisesDoubleAngleCubicPart
