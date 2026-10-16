import calculus.Chapter03.Section07ComposedQuadraticRatioExercises
import calculus.Chapter03.Section06VariablePowerLimitExercises

/-! §3.7 — Bài tập 3.7.11(h), 3.7.12(a,b,f): giới hạn lũy thừa. -/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07QuadraticVariablePowerExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section01Powers calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07LogarithmicRatioExercises
open calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section06SourceIssues calculus.Chapter03.Section06VariablePowerLimitExercises


def tangentSquarePowerDomain : Set ℝ :=
  {x | Real.cos x ≠ 0 ∧ Real.sin (2 * x) ^ 2 ≠ 0 ∧
    1 - Real.tan x ^ 2 ∈ realPowerDomain (1 / Real.sin (2 * x) ^ 2)}


def cosineQuadraticPowerDomain : Set ℝ :=
  {x | x ^ 2 ≠ 0 ∧ Real.cos x ∈ realPowerDomain (1 / x ^ 2)}


def cosineSineCubicPowerDomain : Set ℝ :=
  {x | x ^ 3 ≠ 0 ∧ Real.cos x ∈ realPowerDomain (Real.sin x)}


theorem normalized_log_tangent_square_at_zero :
    Tendsto (fun x : ℝ ↦ Real.log (1 - Real.tan x ^ 2) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 : ℝ)) := by
  have ht : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using!
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ -(Real.tan x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.neg_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero] using! (ht.pow 2).neg
  have hn : Tendsto (fun x : ℝ ↦ -(Real.tan x ^ 2) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 : ℝ)) := by
    have hh : Tendsto (fun x : ℝ ↦ -((Real.tan x / x) ^ 2))
        (domainApproachFilter univ (.point 0)) (𝓝 (-1 : ℝ)) := by
      simpa only [Pi.neg_apply, one_pow] using! (tangent_equivalent_identity_zero.2.2.pow 2).neg
    apply hh.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  simpa only [← sub_eq_add_neg] using!
    normalized_log_of_quadratic hu hn (by norm_num : (-1 : ℝ) ≠ 0)


theorem normalized_sine_double_square_at_zero :
    Tendsto (fun x : ℝ ↦ Real.sin (2 * x) ^ 2 / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ ↦ (Real.sin (2 * x) / x) ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using! (scaled_sine_normalized_at_zero 2).pow 2
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  field_simp [hx]

/-- Bài tập 3.7.12(a): giới hạn bằng exp(−1/4). -/
theorem tangent_square_variable_power_at_zero :
    DomainLimit tangentSquarePowerDomain
      (fun x ↦ (1 - Real.tan x ^ 2) ^ (1 / Real.sin (2 * x) ^ 2)) 0 (Real.exp (-1 / 4)) := by
  have hf := normalized_log_tangent_square_at_zero
  have hg := normalized_sine_double_square_at_zero
  have hprod : Tendsto (fun x : ℝ ↦ (1 / Real.sin (2 * x) ^ 2) * Real.log (1 - Real.tan x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 4 : ℝ)) := by
    have hq : Tendsto (fun x : ℝ ↦ (Real.log (1 - Real.tan x ^ 2) / x ^ 2) /
        (Real.sin (2 * x) ^ 2 / x ^ 2))
        (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 4 : ℝ)) := by
      simpa only [Pi.div_apply] using! hf.div hg (by norm_num : (4 : ℝ) ≠ 0)
    apply hq.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hx)]
    ring
  have htan : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using!
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun x : ℝ ↦ 1 - Real.tan x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using! (htan.pow 2).const_sub 1
  have hpos := hb.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsne : ∀ᶠ x in domainApproachFilter univ (.point 0), Real.sin (2 * x) ^ 2 ≠ 0 :=
    (hg.eventually_ne (by norm_num : (4 : ℝ) ≠ 0)).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ tangentSquarePowerDomain := by
    filter_upwards [tangent_eventually_defined_zero, hsne, hpos] with x hc hs hp
    exact ⟨hc, hs, positive_base_mem_variable_power_domain hp⟩
  exact domainLimit_of_eventually_domain hD (power_limit_of_log_product hpos hprod)

/-- Bài tập 3.7.12(f): giới hạn bằng exp(−1/4). -/
theorem tangent_square_variable_power_at_zero_duplicate :
    DomainLimit tangentSquarePowerDomain
      (fun x ↦ (1 - Real.tan x ^ 2) ^ (1 / Real.sin (2 * x) ^ 2)) 0 (Real.exp (-1 / 4)) :=
  tangent_square_variable_power_at_zero

/-- Bài tập 3.7.12(b): cos(x)^(1/x²)→exp(−1/2). -/
theorem cosine_quadratic_variable_power_at_zero :
    DomainLimit cosineQuadraticPowerDomain
      (fun x ↦ Real.cos x ^ (1 / x ^ 2)) 0 (Real.exp (-1 / 2)) := by
  have hh : Tendsto (fun x : ℝ ↦ Real.log (Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [one_mul, one_pow, ← neg_div] using! normalized_log_cosine_at_zero (by norm_num : (1 : ℝ) ≠ 0)
  have hprod : Tendsto (fun x : ℝ ↦ (1 / x ^ 2) * Real.log (Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    apply hh.congr
    intro x
    ring
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using!
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hpos := hc.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ cosineQuadraticPowerDomain := by
    filter_upwards [punctured_zero_eventually_ne, hpos] with x hx hp
    exact ⟨pow_ne_zero 2 hx, positive_base_mem_variable_power_domain hp⟩
  exact domainLimit_of_eventually_domain hD (power_limit_of_log_product hpos hprod)

/-- Bài tập 3.7.11(h): (1−cos(x)^(sin x))/x³→1/2. -/
theorem cosine_sine_cubic_power_ratio_at_zero :
    DomainLimit cosineSineCubicPowerDomain
      (fun x ↦ (1 - Real.cos x ^ Real.sin x) / x ^ 3) 0 (1 / 2) := by
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using!
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto Real.sin (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.sin_zero] using!
      (Real.continuous_sin.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ ↦ Real.log (Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one] using! hc.log one_ne_zero
  have hu : Tendsto (fun x : ℝ ↦ Real.sin x * Real.log (Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! hs.mul hlog
  have hlq : Tendsto (fun x : ℝ ↦ Real.log (Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [one_mul, one_pow, ← neg_div] using! normalized_log_cosine_at_zero (by norm_num : (1 : ℝ) ≠ 0)
  have hun : Tendsto (fun x : ℝ ↦ (Real.sin x * Real.log (Real.cos x)) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ (Real.sin x / x) * (Real.log (Real.cos x) / x ^ 2))
        (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
      simpa only [Pi.mul_apply, one_mul] using! sine_equivalent_identity_zero.2.2.mul hlq
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hψ : HasDerivAt (fun t : ℝ ↦ 1 - Real.exp t) (-1) 0 := by
    simpa only [Real.exp_zero] using! (Real.hasDerivAt_exp 0).const_sub 1
  have hnorm : Tendsto (fun x : ℝ ↦ (1 - Real.exp (Real.sin x * Real.log (Real.cos x))) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [show (-1 : ℝ) * (-1 / 2) = 1 / 2 by norm_num] using!
      normalized_composition_increment 3 hψ (by simp only [Real.exp_zero, sub_self]) hu hun
        (by norm_num : (-1 / 2 : ℝ) ≠ 0)
  have hpos := hc.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ cosineSineCubicPowerDomain := by
    filter_upwards [punctured_zero_eventually_ne, hpos] with x hx hp
    exact ⟨pow_ne_zero 3 hx, positive_base_mem_variable_power_domain hp⟩
  apply domainLimit_of_eventually_domain hD
  apply hnorm.congr'
  filter_upwards [hpos] with x hp
  have he : Real.cos x ^ Real.sin x = Real.exp (Real.sin x * Real.log (Real.cos x)) := by
    rw [Real.rpow_def_of_pos hp, mul_comm]
  rw [he]

end calculus.Chapter03.Section07QuadraticVariablePowerExercises
