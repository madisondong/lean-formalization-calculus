import calculus.Chapter03.Section07ComposedQuadraticRatioExercises
import calculus.Chapter03.Section07LogarithmicRatioExercises
import Mathlib.Analysis.Calculus.LHopital

/-!
§3.7 — Bài tập 3.7.14(g)

Nguồn: dòng 3755.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07CubicArctangentRootLimitExercise
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07
open calculus.Chapter03.Section07CosineRatioExercises
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section07LogarithmicRatioExercises


def cubicArctangentRootDomain : Set ℝ :=
  {x | Real.cos x ≠ 0 ∧ x ^ 2 * Real.tan x + Real.cos (2 * x) ∈ nthRootDomain 3 ∧
    x - Real.tan x ≠ 0}


theorem identity_sub_tangent_div_cube_at_zero :
    Tendsto (fun x : ℝ ↦ (x - Real.tan x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 3 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using!
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hff : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ y - Real.tan y) (1 - 1 / Real.cos x ^ 2) x := by
    filter_upwards [tangent_eventually_defined_zero] with x hx
    simpa only [id_eq] using! (hasDerivAt_id x).sub (Real.hasDerivAt_tan hx)
  have hgg : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) x := by
    exact Eventually.of_forall fun x ↦ by simpa using! (hasDerivAt_id x).pow 3
  have hgne : ∀ᶠ x in domainApproachFilter univ (.point 0), 3 * x ^ 2 ≠ 0 :=
    punctured_zero_eventually_ne.mono fun _ hx ↦ mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 2 hx)
  have hf : Tendsto (fun x : ℝ ↦ x - Real.tan x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_zero] using! hi.sub ht
  have hg : Tendsto (fun x : ℝ ↦ x ^ 3) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! hi.pow 3
  have hratio : Tendsto (fun x : ℝ ↦ (1 - 1 / Real.cos x ^ 2) / (3 * x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 3 : ℝ)) := by
    have hs : Tendsto (fun x : ℝ ↦ -((Real.tan x / x) ^ 2) / 3)
        (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 3 : ℝ)) := by
      simpa only [Pi.neg_apply, one_pow] using! (tangent_equivalent_identity_zero.2.2.pow 2).neg.div_const 3
    apply hs.congr'
    filter_upwards [punctured_zero_eventually_ne, tangent_eventually_defined_zero] with x hx hc
    rw [Real.tan_eq_sin_div_cos]
    have he := congrArg (fun t : ℝ ↦ t * x ^ 2) (Real.sin_sq_add_cos_sq x)
    field_simp [hx, hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hfilter : domainApproachFilter univ (.point 0) = (𝓝[≠] (0 : ℝ)) := by
    simp only [domainApproachFilter, compl_eq_univ_sdiff]
  rw [hfilter] at hff hgg hgne hf hg hratio ⊢
  exact HasDerivAt.lhopital_zero_nhdsNE hff hgg hgne hf hg hratio


theorem normalized_cubic_arctangent_root_increment_at_zero :
    Tendsto (fun x : ℝ ↦ (realNthRoot 3 (x ^ 2 * Real.tan x + Real.cos (2 * x)) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-2 / 3 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using!
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun x : ℝ ↦ Real.cos (2 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.cos (2 * x)) 0 := by fun_prop
    simpa only [mul_zero, Real.cos_zero] using! hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ x ^ 2 * Real.tan x + Real.cos (2 * x) - 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add, sub_self] using!
      (((hi.pow 2).mul ht).add hc).sub_const 1
  have hcos : Tendsto (fun x : ℝ ↦ (1 - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [show (2 : ℝ) ^ 2 / 2 = 2 by norm_num] using! normalized_scaled_cosine 2
  have hn : Tendsto (fun x : ℝ ↦ (x ^ 2 * Real.tan x + Real.cos (2 * x) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-2 : ℝ)) := by
    have hs : Tendsto (fun x : ℝ ↦ Real.tan x - (1 - Real.cos (2 * x)) / x ^ 2)
        (domainApproachFilter univ (.point 0)) (𝓝 (-2 : ℝ)) := by
      simpa only [Pi.sub_apply, zero_sub] using! ht.sub hcos
    apply hs.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
    all_goals ring
  have ha : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_add 1
  have ho : HasDerivAt (realNthRoot 3) ((3 : ℝ)⁻¹) (1 + (0 : ℝ)) := by
    simpa only [add_zero, Nat.cast_ofNat] using realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)
  have hψ : HasDerivAt (fun t : ℝ ↦ realNthRoot 3 (1 + t) - 1) (1 / 3) 0 := by
    simpa only [Function.comp_def, mul_one, one_div] using! (ho.comp 0 ha).sub_const 1
  have hs : Tendsto (fun x : ℝ ↦ (realNthRoot 3 (1 + (x ^ 2 * Real.tan x + Real.cos (2 * x) - 1)) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-2 / 3 : ℝ)) := by
    simpa only [show (1 / 3 : ℝ) * (-2) = -2 / 3 by norm_num] using!
      normalized_composition_increment 2 hψ (by rw [add_zero, realNthRoot_one, sub_self]) hu hn
        (by norm_num : (-2 : ℝ) ≠ 0)
  apply hs.congr
  intro x
  rw [show 1 + (x ^ 2 * Real.tan x + Real.cos (2 * x) - 1) = x ^ 2 * Real.tan x + Real.cos (2 * x) by ring]

/-- Bài tập 3.7.14(g): giới hạn bằng 2. -/
theorem cubic_arctangent_root_ratio_at_zero :
    DomainLimit cubicArctangentRootDomain
      (fun x ↦ ((realNthRoot 3 (x ^ 2 * Real.tan x + Real.cos (2 * x)) - 1) * Real.arctan x) /
        (x - Real.tan x)) 0 2 := by
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ cubicArctangentRootDomain := by
    filter_upwards [tangent_eventually_defined_zero,
      identity_sub_tangent_div_cube_at_zero.eventually_ne (by norm_num : (-1 / 3 : ℝ) ≠ 0)] with x hc hn
    exact ⟨hc, Or.inl (by decide : Odd 3), (div_ne_zero_iff.mp hn).1⟩
  have hd : HasDerivAt Real.arctan 1 0 := by simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have ha : Tendsto (fun x : ℝ ↦ Real.arctan x / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.arctan_zero, sub_zero] using! derivative_quotient_zero hd
  have hn : Tendsto (fun x : ℝ ↦ ((realNthRoot 3 (x ^ 2 * Real.tan x + Real.cos (2 * x)) - 1) * Real.arctan x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-2 / 3 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ ((realNthRoot 3 (x ^ 2 * Real.tan x + Real.cos (2 * x)) - 1) / x ^ 2) *
        (Real.arctan x / x)) (domainApproachFilter univ (.point 0)) (𝓝 (-2 / 3 : ℝ)) := by
      simpa only [Pi.mul_apply, mul_one] using! normalized_cubic_arctangent_root_increment_at_zero.mul ha
    apply ht.congr
    intro x
    rw [div_mul_div_comm, ← pow_succ]
  apply domainLimit_of_eventually_domain hD
  have hq : Tendsto (fun x : ℝ ↦
      ((((realNthRoot 3 (x ^ 2 * Real.tan x + Real.cos (2 * x)) - 1) * Real.arctan x) / x ^ 3) /
        ((x - Real.tan x) / x ^ 3))) (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [Pi.div_apply, show (-2 / 3 : ℝ) / (-1 / 3) = 2 by norm_num] using!
      hn.div identity_sub_tangent_div_cube_at_zero (by norm_num : (-1 / 3 : ℝ) ≠ 0)
  apply hq.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_div_div_cancel_right₀ (pow_ne_zero 3 hx) _ _

end calculus.Chapter03.Section07CubicArctangentRootLimitExercise
