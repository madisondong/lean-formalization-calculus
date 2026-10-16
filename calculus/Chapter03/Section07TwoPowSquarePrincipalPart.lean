import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# §3.7 — phần chính của `2^(x²) − 1`

Nguồn: `Ch3_gioihanhamso.tex`, Bài tập 3.7.3(j), dòng 3496.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07TwoPowSquarePrincipalPart

open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts


theorem square_punctured_tendsto :
    Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0))
      (domainApproachFilter univ (.point 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [domainApproachFilter, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (continuous_pow 2).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : domainApproachFilter univ (.point 0) ≤ 𝓝 (0 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx ⊢
    exact pow_ne_zero 2 hx

/-- Bài tập 3.7.3(j): phần chính (ln 2)x², bậc 2. -/
theorem two_pow_square_sub_one_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ (2 : ℝ) ^ (x ^ 2) - 1) (fun x ↦ x) 2 (Real.log 2) := by
  have hF : HasDerivAt (fun u : ℝ ↦ (2 : ℝ) ^ u - 1) (Real.log 2) 0 := by
    simpa only [Real.rpow_zero, one_mul] using
      ((Real.hasStrictDerivAt_const_rpow (by norm_num : (0 : ℝ) < 2) 0).hasDerivAt.sub_const 1)
  have hq : Tendsto (fun u : ℝ ↦ ((2 : ℝ) ^ u - 1) / u)
      (domainApproachFilter univ (.point 0)) (𝓝 (Real.log 2)) := by
    simpa only [domainApproachFilter, slope_fun_def_field, Real.rpow_zero, sub_self, sub_zero] using
      (domainLimit_iff_tendsto (univ_accumulation 0)).mp (hasDerivAt_domainLimit_slope hF)
  have hf : Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ (x ^ 2) - 1)
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, sub_self] using
      hF.continuousAt.tendsto.comp (square_punctured_tendsto.mono_right nhdsWithin_le_nhds)
  have ht : Tendsto (fun x : ℝ ↦ ((2 : ℝ) ^ (x ^ 2) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (Real.log 2)) := by
    simpa only [Function.comp_def] using hq.comp square_punctured_tendsto
  exact hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0)
    (by norm_num : 0 < (2 : ℕ)) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' hf ht

end calculus.Chapter03.Section07TwoPowSquarePrincipalPart
