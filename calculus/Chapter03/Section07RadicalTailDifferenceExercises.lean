import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.Normed.Group.Continuity

/-!
§3.7 — Bài tập 3.7.13(e) và Bài tập 3.7.14(b)

Nguồn: dòng 3732, 3750.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07RadicalTailDifferenceExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07QuadraticRadicalInfinityExercises


def quadraticCubicRadicalDifferenceDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + 2 * x ∧ x ^ 3 + x ^ 2 ∈ nthRootDomain 3}


def oscillatoryRadicalRatioDomain : Set ℝ :=
  {x | 0 ≤ x ^ 3 + 1 ∧ Real.sqrt (x ^ 3 + 1) * Real.arctan x ≠ 0}


theorem normalized_cubic_root_atTop :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 3 + x ^ 2) / x) atTop (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ 1 + x⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using! tendsto_inv_atTop_zero.const_add (1 : ℝ)
  have hr : Tendsto (fun x : ℝ ↦ realNthRoot 3 (1 + x⁻¹)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, realNthRoot_one] using!
      (realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)).continuousAt.tendsto.comp hi
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply (by decide : Odd 3).pow_injective
  change realNthRoot 3 (1 + x⁻¹) ^ (3 : ℕ) =
    (realNthRoot 3 (x ^ 3 + x ^ 2) / x) ^ (3 : ℕ)
  rw [div_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)), add_div,
    div_self (pow_ne_zero 3 hx.ne')]
  rw [show x ^ 3 = x ^ 2 * x by ring, div_mul_cancel_left₀ (pow_ne_zero 2 hx.ne') x]


theorem cubic_root_sub_identity_atTop :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 3 + x ^ 2) - x) atTop (𝓝 (1 / 3 : ℝ)) := by
  have hd : Tendsto (fun x : ℝ ↦ (realNthRoot 3 (x ^ 3 + x ^ 2) / x) ^ 2 +
      realNthRoot 3 (x ^ 3 + x ^ 2) / x + 1) atTop (𝓝 (3 : ℝ)) := by
    simpa only [one_pow, show (1 : ℝ) + 1 + 1 = 3 by norm_num] using!
      ((normalized_cubic_root_atTop.pow 2).add normalized_cubic_root_atTop).add_const 1
  have ht : Tendsto (fun x : ℝ ↦ 1 / ((realNthRoot 3 (x ^ 3 + x ^ 2) / x) ^ 2 +
      realNthRoot 3 (x ^ 3 + x ^ 2) / x + 1)) atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa only [Pi.div_apply] using!
      (tendsto_const_nhds (x := (1 : ℝ))).div hd (by norm_num : (3 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne (by norm_num : (3 : ℝ) ≠ 0)] with x hx hden
  have hy := realNthRoot_pow (by decide : 1 ≤ 3)
    (show x ^ 3 + x ^ 2 ∈ nthRootDomain 3 from Or.inl (by decide : Odd 3))
  have hm : (realNthRoot 3 (x ^ 3 + x ^ 2) - x) *
      ((realNthRoot 3 (x ^ 3 + x ^ 2) / x) ^ 2 + realNthRoot 3 (x ^ 3 + x ^ 2) / x + 1) = 1 := by
    generalize realNthRoot 3 (x ^ 3 + x ^ 2) = y at hy ⊢
    field_simp [hx.ne']
    nlinarith [hy]
  exact ((eq_div_iff hden).mpr hm).symm


theorem quadratic_root_sub_identity_atTop :
    Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 2 * x) - x) atTop (𝓝 (1 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 2 * x) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, add_zero, Real.sqrt_one] using! normalized_quadratic_sqrt_atTop 1 2 0
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 2 * x) / x + 1) atTop (𝓝 (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using! hs.add_const 1
  have ht : Tendsto (fun x : ℝ ↦ 2 / (Real.sqrt (x ^ 2 + 2 * x) / x + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, div_self (by norm_num : (2 : ℝ) ≠ 0)] using!
      (tendsto_const_nhds (x := (2 : ℝ))).div hd (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)] with x hx hden
  have hrad : 0 ≤ x ^ 2 + 2 * x := by nlinarith [sq_nonneg x]
  have hsq := Real.sq_sqrt hrad
  have hm : (Real.sqrt (x ^ 2 + 2 * x) - x) * (Real.sqrt (x ^ 2 + 2 * x) / x + 1) = 2 := by
    generalize Real.sqrt (x ^ 2 + 2 * x) = y at hsq ⊢
    field_simp [hx.ne']
    nlinarith [hsq]
  exact ((eq_div_iff hden).mpr hm).symm

/-- Bài tập 3.7.13(e): giới hạn tại +∞ bằng 2/3. -/
theorem quadratic_cubic_radical_difference_at_infinity :
    DomainAtTopLimit quadraticCubicRadicalDifferenceDomain
      (fun x ↦ Real.sqrt (x ^ 2 + 2 * x) - realNthRoot 3 (x ^ 3 + x ^ 2)) (2 / 3) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ quadraticCubicRadicalDifferenceDomain := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ⟨by nlinarith [sq_nonneg x], Or.inl (by decide : Odd 3)⟩
  apply domainAtTopLimit_of_eventually_domain hD
  have ht : Tendsto (fun x : ℝ ↦ (Real.sqrt (x ^ 2 + 2 * x) - x) -
      (realNthRoot 3 (x ^ 3 + x ^ 2) - x)) atTop (𝓝 (2 / 3 : ℝ)) := by
    simpa only [Pi.sub_apply, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] using!
      quadratic_root_sub_identity_atTop.sub cubic_root_sub_identity_atTop
  apply ht.congr
  intro x
  ring


theorem linear_over_cubic_radical_atTop_zero :
    Tendsto (fun x : ℝ ↦ x / Real.sqrt (x ^ 3 + 1)) atTop (𝓝 (0 : ℝ)) := by
  have hsmall : Tendsto (fun x : ℝ ↦ 1 / Real.sqrt x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using! Real.tendsto_sqrt_atTop.inv_tendsto_atTop
  have hn : ∀ᶠ x : ℝ in atTop, 0 ≤ x / Real.sqrt (x ^ 3 + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg hx.le (Real.sqrt_nonneg _)
  have hb : ∀ᶠ x : ℝ in atTop, x / Real.sqrt (x ^ 3 + 1) ≤ 1 / Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hrad : 0 < x ^ 3 + 1 := by positivity
    have hden : 0 < Real.sqrt (x ^ 3 + 1) := Real.sqrt_pos.mpr hrad
    have he : Real.sqrt (x ^ 3) = x * Real.sqrt x := by
      rw [show x ^ 3 = x ^ 2 * x by ring, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
    have hm := Real.sqrt_le_sqrt (show x ^ 3 ≤ x ^ 3 + 1 by linarith)
    rw [he] at hm
    exact (div_le_div_iff₀ hden hroot).mpr (by simpa only [one_mul] using hm)
  exact squeeze_zero' hn hb hsmall

/-- Bài tập 3.7.14(b): giới hạn thương bằng 0. -/
theorem oscillatory_radical_ratio_at_infinity :
    DomainAtTopLimit oscillatoryRadicalRatioDomain
      (fun x ↦ x * Real.sin x / (Real.sqrt (x ^ 3 + 1) * Real.arctan x)) 0 := by
  have ha : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ oscillatoryRadicalRatioDomain := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hp : 0 < x ^ 3 + 1 := by positivity
    exact ⟨hp.le, mul_ne_zero (Real.sqrt_pos.mpr hp).ne' (Real.arctan_pos.mpr hx).ne'⟩
  apply domainAtTopLimit_of_eventually_domain hD
  have hb : ∀ᶠ x : ℝ in atTop, ‖(x / Real.sqrt (x ^ 3 + 1)) * Real.sin x‖ ≤
      x / Real.sqrt (x ^ 3 + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hn : 0 ≤ x / Real.sqrt (x ^ 3 + 1) := div_nonneg hx.le (Real.sqrt_nonneg _)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs]
    calc
      _ ≤ (x / Real.sqrt (x ^ 3 + 1)) * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) hn
      _ = _ := mul_one _
  have hs : Tendsto (fun x : ℝ ↦ (x / Real.sqrt (x ^ 3 + 1)) * Real.sin x) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero_norm' hb linear_over_cubic_radical_atTop_zero
  have hq : Tendsto (fun x : ℝ ↦ ((x / Real.sqrt (x ^ 3 + 1)) * Real.sin x) / Real.arctan x)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.div_apply, zero_div] using! hs.div ha (by positivity : Real.pi / 2 ≠ 0)
  apply hq.congr
  intro x
  rw [← div_div]
  ring

end calculus.Chapter03.Section07RadicalTailDifferenceExercises
