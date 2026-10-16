import calculus.Chapter03.Section07LogarithmicRootPrincipalPart
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §3.7 — Bài tập 3.7.3(h): sin(√(2x+√(x+x²)))−x⁵

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3483–3501; mục (h) dòng 3494.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesNestedRootPrincipalPart

open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section01Powers calculus.Chapter03.Section07
open calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07LogarithmicRootPrincipalPart

/-- Miền tự nhiên của hai căn là [0,+∞). -/
def nestedRootDomain : Set ℝ :=
  {x | 0 ≤ x + x ^ 2 ∧ 0 ≤ 2 * x + Real.sqrt (x + x ^ 2)}


noncomputable def nestedRootArgument (x : ℝ) : ℝ :=
  Real.sqrt (2 * x + Real.sqrt (x + x ^ 2))


theorem nested_root_domain_eq_Ici : nestedRootDomain = Ici 0 := by
  ext x
  constructor
  · intro hx
    change 0 ≤ x
    by_contra hn
    have hneg : x < 0 := lt_of_not_ge hn
    have hbound : -2 * x ≤ Real.sqrt (x + x ^ 2) := by linarith [hx.2]
    have hsq : (-2 * x) ^ 2 ≤ Real.sqrt (x + x ^ 2) ^ 2 :=
      (sq_le_sq₀ (by linarith) (Real.sqrt_nonneg _)).mpr hbound
    rw [Real.sq_sqrt hx.1] at hsq
    nlinarith [sq_nonneg x]
  · intro hx
    change 0 ≤ x at hx
    refine ⟨by nlinarith [sq_nonneg x], ?_⟩
    linarith [Real.sqrt_nonneg (x + x ^ 2)]


theorem nested_root_domain_accumulation : AccumulationPointOf nestedRootDomain 0 := by
  rw [nested_root_domain_eq_Ici]
  exact nonnegative_domain_accumulation


theorem nested_root_eventually_positive :
    ∀ᶠ x in domainApproachFilter nestedRootDomain (.point 0), 0 < x := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 ≤ x := by simpa only [nested_root_domain_eq_Ici, mem_Ici] using hx.1
  exact lt_of_le_of_ne hx0 (by simpa [ne_comm] using hx.2)


theorem nested_root_inner_factor {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x + x ^ 2) = Real.sqrt x * Real.sqrt (1 + x) := by
  rw [show x + x ^ 2 = x * (1 + x) by ring, Real.sqrt_mul hx]


theorem nested_root_outer_factor {x : ℝ} (hx : 0 ≤ x) :
    nestedRootArgument x = Real.sqrt (Real.sqrt x) *
      Real.sqrt (2 * Real.sqrt x + Real.sqrt (1 + x)) := by
  have hr : 2 * x + Real.sqrt (x + x ^ 2) =
      Real.sqrt x * (2 * Real.sqrt x + Real.sqrt (1 + x)) := by
    rw [nested_root_inner_factor hx]
    nlinarith [Real.sq_sqrt hx]
  rw [nestedRootArgument, hr, Real.sqrt_mul (Real.sqrt_nonneg x)]


theorem nested_root_quarter_power {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num


theorem nested_root_normalized_factor {x : ℝ} (hx : 0 < x) :
    nestedRootArgument x / x ^ (1 / 4 : ℝ) =
      Real.sqrt (2 * Real.sqrt x + Real.sqrt (1 + x)) := by
  rw [nested_root_outer_factor hx.le, nested_root_quarter_power hx.le]
  have hn := (Real.rpow_pos_of_pos hx (1 / 4 : ℝ)).ne'
  field_simp [hn]


theorem nested_root_argument_tendsto_zero :
    Tendsto nestedRootArgument (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hin : Tendsto (fun x : ℝ ↦ x + x ^ 2)
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    simpa using hi.add (hi.pow 2)
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x + x ^ 2))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hin.sqrt
  have hout : Tendsto (fun x : ℝ ↦ 2 * x + Real.sqrt (x + x ^ 2))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    simpa using (hi.const_mul 2).add hs
  change Tendsto (fun x : ℝ ↦ Real.sqrt (2 * x + Real.sqrt (x + x ^ 2)))
    (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0)
  simpa only [Real.sqrt_zero] using hout.sqrt


theorem nested_root_sine_sub_fifth_normalized_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.sin (nestedRootArgument x) - x ^ 5) / x ^ (1 / 4 : ℝ))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt x)
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hi.sqrt
  have hone : Tendsto (fun x : ℝ ↦ Real.sqrt (1 + x))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero, Real.sqrt_one] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).sqrt
  have hfactor : Tendsto (fun x : ℝ ↦ Real.sqrt (2 * Real.sqrt x + Real.sqrt (1 + x)))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, zero_add, Real.sqrt_one] using ((hs.const_mul 2).add hone).sqrt
  have hrootratio : Tendsto (fun x : ℝ ↦ nestedRootArgument x / x ^ (1 / 4 : ℝ))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    apply hfactor.congr'
    filter_upwards [nested_root_eventually_positive] with x hx
    exact (nested_root_normalized_factor hx).symm
  have hsinc : Tendsto (fun x : ℝ ↦ Real.sinc (nestedRootArgument x))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      (Real.continuous_sinc.tendsto (0 : ℝ)).comp nested_root_argument_tendsto_zero
  have hsinratio : Tendsto (fun x : ℝ ↦ Real.sin (nestedRootArgument x) / x ^ (1 / 4 : ℝ))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ Real.sinc (nestedRootArgument x) *
        (nestedRootArgument x / x ^ (1 / 4 : ℝ)))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 (1 : ℝ)) from by
        simpa only [one_mul] using hsinc.mul hrootratio).congr'
    filter_upwards [nested_root_eventually_positive] with x hx
    have harg : nestedRootArgument x ≠ 0 := by
      apply (Real.sqrt_pos.mpr ?_).ne'
      linarith [Real.sqrt_nonneg (x + x ^ 2)]
    have hquarter := (Real.rpow_pos_of_pos hx (1 / 4 : ℝ)).ne'
    rw [Real.sinc_of_ne_zero harg]
    field_simp [harg, hquarter]
  have hfifth : Tendsto (fun x : ℝ ↦ x ^ 5 / x ^ (1 / 4 : ℝ))
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    apply (hi.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 19 / 4)).congr'
    filter_upwards [nested_root_eventually_positive] with x hx
    rw [show (19 / 4 : ℝ) = 5 - 1 / 4 by norm_num, Real.rpow_sub hx,
      show x ^ (5 : ℝ) = x ^ 5 from Real.rpow_natCast x 5]
  simpa only [sub_zero, sub_div] using hsinratio.sub hfifth

/-- Bài tập 3.7.3(h): phần chính x^(1/4), bậc 1/4, khi x→0⁺. -/
theorem nested_root_sine_sub_fifth_principal_part :
    HasPowerPrincipalPartAlong nestedRootDomain (.point 0)
      (fun x ↦ Real.sin (Real.sqrt (2 * x + Real.sqrt (x + x ^ 2))) - x ^ 5)
      (fun x ↦ x) (1 / 4) 1 := by
  have hp := (properLimitApproach_point_iff _ 0).mpr nested_root_domain_accumulation
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hf : Tendsto (fun x : ℝ ↦ Real.sin (nestedRootArgument x) - x ^ 5)
      (domainApproachFilter nestedRootDomain (.point 0)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by decide : (5 : ℕ) ≠ 0), sub_zero] using
      ((Real.continuous_sin.tendsto (0 : ℝ)).comp nested_root_argument_tendsto_zero).sub (hi.pow 5)
  have had : EventuallyRealPowerDefinedAlong nestedRootDomain (.point 0) (fun x ↦ x) (1 / 4) := by
    filter_upwards [nested_root_eventually_positive] with x hx
    unfold realPowerDomain
    split_ifs
    · exact mem_univ _
    · exact hx.ne'
    · exact hx
  exact hasPowerPrincipalPartAlong_real_of_tendsto ⟨hp, hi⟩
    (by norm_num : (0 : ℝ) < 1 / 4) had
    (nested_root_eventually_positive.mono fun _ hx ↦ hx.ne') (by norm_num : (1 : ℝ) ≠ 0)
    hf nested_root_sine_sub_fifth_normalized_tendsto

end calculus.Chapter03.Section07ExercisesNestedRootPrincipalPart
