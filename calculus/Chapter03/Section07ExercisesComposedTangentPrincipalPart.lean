import calculus.Chapter03.Section07ExercisesLinearLeadingParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.7 — phần chính của hàm tang hợp

Nguồn: Bài tập 3.7.3(d), `Ch3_gioihanhamso.tex`, dòng 3490.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesComposedTangentPrincipalPart

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07
open calculus.Chapter03.Section07Orders calculus.Chapter03.Section07ExercisesLinearLeadingParts


def composedTangentDomain : Set ℝ := {x | Real.cos ((x ^ 2 + 1) * Real.sin x) ≠ 0}


theorem composed_tangent_domain_nhds : composedTangentDomain ∈ 𝓝 (0 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ ↦ Real.cos ((x ^ 2 + 1) * Real.sin x)) 0 := by
    fun_prop
  exact hc.tendsto.eventually_ne
    (by norm_num : Real.cos (((0 : ℝ) ^ 2 + 1) * Real.sin 0) ≠ 0)


theorem composed_tangent_domain_accumulation : AccumulationPointOf composedTangentDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) composed_tangent_domain_nhds

/-- Bài tập 3.7.3(d): phần chính x, bậc 1. -/
theorem tangent_of_quadratic_sine_principal_part :
    HasPowerPrincipalPartAlong composedTangentDomain (.point 0)
      (fun x ↦ Real.tan ((x ^ 2 + 1) * Real.sin x)) (fun x ↦ x) 1 1 := by
  have harg : HasDerivAt (fun x : ℝ ↦ (x ^ 2 + 1) * Real.sin x) 1 0 := by
    simpa [Pi.pow_apply, id_eq, Pi.add_apply, Pi.mul_apply] using! (((hasDerivAt_id (0 : ℝ)).pow 2).add_const 1).mul
      (Real.hasDerivAt_sin (0 : ℝ))
  have hf : HasDerivAt (fun x : ℝ ↦ Real.tan ((x ^ 2 + 1) * Real.sin x)) 1 0 := by
    convert! (Real.hasDerivAt_tan
      (by norm_num : Real.cos (((0 : ℝ) ^ 2 + 1) * Real.sin 0) ≠ 0)).comp 0 harg using 1
    norm_num
  exact hasPowerPrincipalPartAlong_one_of_hasDerivAt
    composed_tangent_domain_accumulation hf (by norm_num) (by norm_num)

end calculus.Chapter03.Section07ExercisesComposedTangentPrincipalPart
