import calculus.Chapter03.Section07InfinityComparisonExercises
import calculus.Chapter03.Section07FractionalRootRatioExercise
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
§3.7 — Bài tập 3.7.10(a–e)

Nguồn: dòng 3566–3572.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07GrowthRankingExercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07InfinityComparisonExercises
open calculus.Chapter03.Section07FractionalRootRatioExercise


def positiveLogRankingDomain : Set ℝ := Ioi 0


theorem positive_log_ranking_domain_tail : ∀ᶠ x : ℝ in atTop, x ∈ positiveLogRankingDomain :=
  eventually_gt_atTop 0


theorem tendsto_atTop_of_positive_ratio {f g : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hq : Tendsto (fun x ↦ f x / g x) atTop (𝓝 C))
    (hg : Tendsto g atTop atTop) : Tendsto f atTop atTop := by
  apply (hq.pos_mul_atTop hC hg).congr'
  filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  rw [div_mul_cancel₀ _ hx.ne']


theorem lower_order_infinite_magnitude_along_of_atTop_ratio {D : Set ℝ} {f g : ℝ → ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hf : Tendsto f atTop atTop)
    (hg : Tendsto g atTop atTop) (hq : Tendsto (fun x ↦ f x / g x) atTop (𝓝 0)) :
    LowerOrderInfiniteMagnitudeAlong D .positiveInfinity f g := by
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  refine ⟨infinite_magnitude_along_of_atTop hD hf, infinite_magnitude_along_of_atTop hD hg,
    hp, ?_, ?_⟩
  · rw [he]
    exact (hg.eventually (eventually_gt_atTop (0 : ℝ))).mono (fun _ hx ↦ hx.ne')
  · rw [he]
    exact hq


theorem ratio_zero_of_common_scale {f g u : ℝ → ℝ} {B : ℝ}
    (hf : Tendsto (fun x ↦ f x / u x) atTop (𝓝 0))
    (hg : Tendsto (fun x ↦ g x / u x) atTop (𝓝 B)) (hB : B ≠ 0)
    (hu : ∀ᶠ x : ℝ in atTop, u x ≠ 0) :
    Tendsto (fun x ↦ f x / g x) atTop (𝓝 0) := by
  have ht : Tendsto (fun x ↦ (f x / u x) / (g x / u x)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.div_apply, zero_div] using! hf.div hg hB
  apply ht.congr'
  filter_upwards [hu] with x hx
  exact div_div_div_cancel_right₀ hx _ _


theorem ratio_zero_of_two_scales {f g a b : ℝ → ℝ} {A B : ℝ}
    (hf : Tendsto (fun x ↦ f x / a x) atTop (𝓝 A))
    (hg : Tendsto (fun x ↦ g x / b x) atTop (𝓝 B)) (hB : B ≠ 0)
    (hab : Tendsto (fun x ↦ a x / b x) atTop (𝓝 0))
    (ha : ∀ᶠ x : ℝ in atTop, a x ≠ 0) (hb : ∀ᶠ x : ℝ in atTop, b x ≠ 0) :
    Tendsto (fun x ↦ f x / g x) atTop (𝓝 0) := by
  have ht : Tendsto (fun x ↦ ((f x / a x) * (a x / b x)) / (g x / b x)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, Pi.div_apply, mul_zero, zero_div] using! (hf.mul hab).div hg hB
  apply ht.congr'
  filter_upwards [ha, hb, hg.eventually_ne hB] with x hax hbx hgn
  have hgx : g x ≠ 0 := (div_ne_zero_iff.mp hgn).1
  field_simp [hax, hbx, hgx]


theorem real_power_ratio_atTop_zero {α β : ℝ} (hαβ : α < β) :
    Tendsto (fun x : ℝ ↦ x ^ α / x ^ β) atTop (𝓝 (0 : ℝ)) := by
  have ht := tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [show -(β - α) = α - β by ring, Real.rpow_sub hx]


theorem logarithm_power_over_real_power_atTop_zero (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ n / x ^ s) atTop (𝓝 (0 : ℝ)) := by
  simpa only [Real.rpow_natCast] using!
    (isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).tendsto_div_nhds_zero


theorem sine_over_real_power_atTop_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ Real.sin x / x ^ s) atTop (𝓝 (0 : ℝ)) := by
  have hu : Tendsto (fun x : ℝ ↦ 1 / x ^ s) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using! (tendsto_rpow_atTop hs).inv_tendsto_atTop
  apply squeeze_zero_norm' ?_ hu
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hx s)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (Real.rpow_pos_of_pos hx s).le


theorem real_power_over_exponential_base_atTop_zero (s : ℝ) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun x : ℝ ↦ x ^ s / b ^ x) atTop (𝓝 (0 : ℝ)) := by
  simpa only [Real.rpow_def_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hb)] using!
    (isLittleO_rpow_exp_pos_mul_atTop s (Real.log_pos hb)).tendsto_div_nhds_zero


theorem signed_cubic_root_normalized_atTop {R : ℝ → ℝ} {α A : ℝ}
    (hR : Tendsto (fun x ↦ R x / x ^ (3 * α)) atTop (𝓝 A))
    (hc : ContinuousAt (realNthRoot 3) A) :
    Tendsto (fun x ↦ realNthRoot 3 (R x) / x ^ α) atTop (𝓝 (realNthRoot 3 A)) := by
  have ht : Tendsto (fun x ↦ realNthRoot 3 (R x / x ^ (3 * α))) atTop (𝓝 (realNthRoot 3 A)) := by
    simpa only [Function.comp_def] using! hc.tendsto.comp hR
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply (by decide : Odd 3).pow_injective
  change realNthRoot 3 (R x / x ^ (3 * α)) ^ (3 : ℕ) =
    (realNthRoot 3 (R x) / x ^ α) ^ (3 : ℕ)
  have hp : (x ^ α) ^ (3 : ℕ) = x ^ (3 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    norm_num [mul_comm]
  rw [div_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)), hp]


theorem quadratic_log_over_identity_atTop_zero :
    Tendsto (fun x : ℝ ↦ Real.log (1 + x ^ 2) / x) atTop (𝓝 (0 : ℝ)) := by
  have hl : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one, pow_one] using! logarithm_power_over_real_power_atTop_zero 1 (by norm_num : (0 : ℝ) < 1)
  have hu : Tendsto (fun x : ℝ ↦ Real.log 2 / x + 2 * (Real.log x / x)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using!
      (tendsto_inv_atTop_zero.const_mul (Real.log 2)).add (hl.const_mul 2)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg x] : 1 ≤ 1 + x ^ 2)) (by linarith)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have he : Real.log (2 * x ^ 2) = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hx0.ne'), Real.log_pow]
      norm_num
    have hle : Real.log (1 + x ^ 2) ≤ Real.log (2 * x ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (x - 1)])
    rw [he] at hle
    rw [← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right hle hx0.le


theorem square_sub_sine_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (x ^ 2 - x * Real.sin x) / x ^ 2) atTop (𝓝 (1 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ Real.sin x / x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one] using! sine_over_real_power_atTop_zero (by norm_num : (0 : ℝ) < 1)
  apply (show Tendsto (fun x : ℝ ↦ 1 - Real.sin x / x) atTop (𝓝 (1 : ℝ)) from by
    simpa only [sub_zero] using! hs.const_sub 1).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [hx.ne']


theorem first_group_tendsto_atTop :
    Tendsto (fun x : ℝ ↦ x * Real.log (1 + x ^ 2)) atTop atTop ∧
    Tendsto (fun x : ℝ ↦ x ^ 2 - x * Real.sin x) atTop atTop ∧
    Tendsto (fun x : ℝ ↦ Real.exp x - 1) atTop atTop := by
  have hl : Tendsto (fun x : ℝ ↦ Real.log (1 + x ^ 2)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa only [add_comm] using! tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  refine ⟨tendsto_id.atTop_mul_atTop₀ hl,
    tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1) square_sub_sine_normalized_atTop
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)), ?_⟩
  simpa only [← sub_eq_add_neg] using! tendsto_atTop_add_const_right _ (-1 : ℝ) Real.tendsto_exp_atTop

/-- Bài tập 10(a): f=o(g), g=o(h). -/
theorem first_growth_ranking :
    LowerOrderInfiniteMagnitudeAlong univ .positiveInfinity
      (fun x ↦ x * Real.log (1 + x ^ 2)) (fun x ↦ x ^ 2 - x * Real.sin x) ∧
    LowerOrderInfiniteMagnitudeAlong univ .positiveInfinity
      (fun x ↦ x ^ 2 - x * Real.sin x) (fun x ↦ Real.exp x - 1) := by
  obtain ⟨hf, hg, hh⟩ := first_group_tendsto_atTop
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ (univ : Set ℝ) := Eventually.of_forall (fun _ ↦ mem_univ _)
  have hfg : Tendsto (fun x : ℝ ↦ (x * Real.log (1 + x ^ 2)) / (x ^ 2 - x * Real.sin x)) atTop (𝓝 (0 : ℝ)) := by
    apply ratio_zero_of_common_scale (u := fun x ↦ x ^ 2) ?_ square_sub_sine_normalized_atTop one_ne_zero
      ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 2 hx.ne'))
    apply quadratic_log_over_identity_atTop_zero.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  have hhn : Tendsto (fun x : ℝ ↦ (Real.exp x - 1) / Real.exp x) atTop (𝓝 (1 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ 1 - (Real.exp x)⁻¹) atTop (𝓝 (1 : ℝ)) from by
      simpa only [sub_zero] using! Real.tendsto_exp_atTop.inv_tendsto_atTop.const_sub 1).congr
    intro x
    rw [sub_div, div_self (Real.exp_ne_zero x), one_div]
  have hab : Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp x) atTop (𝓝 (0 : ℝ)) :=
    (Real.isLittleO_pow_exp_atTop (n := 2)).tendsto_div_nhds_zero
  refine ⟨lower_order_infinite_magnitude_along_of_atTop_ratio hD hf hg hfg,
    lower_order_infinite_magnitude_along_of_atTop_ratio hD hg hh ?_⟩
  exact ratio_zero_of_two_scales square_sub_sine_normalized_atTop hhn one_ne_zero hab
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 2 hx.ne')) (Eventually.of_forall Real.exp_ne_zero)


theorem logarithmic_sine_cube_root_over_cube_atTop_zero :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (Real.log x + Real.sin x) / x ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have hn : Tendsto (fun x : ℝ ↦ (Real.log x + Real.sin x) / x ^ (9 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.add_apply, add_div, pow_one, zero_add] using!
      (logarithm_power_over_real_power_atTop_zero 1 (by norm_num : (0 : ℝ) < 9)).add
        (sine_over_real_power_atTop_zero (by norm_num : (0 : ℝ) < 9))
  have hR : Tendsto (fun x : ℝ ↦ (Real.log x + Real.sin x) / x ^ (3 * (3 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [show (3 : ℝ) * 3 = 9 by norm_num] using! hn
  have hz : realNthRoot 3 (0 : ℝ) = 0 := by norm_num [realNthRoot]
  simpa only [Real.rpow_ofNat, hz] using!
    signed_cubic_root_normalized_atTop (α := 3) hR realNthRoot_three_continuousAt_zero


theorem cubic_arctangent_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (x ^ 3 * Real.arctan x) / x ^ 3) atTop (𝓝 (Real.pi / 2)) := by
  apply (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 3 hx.ne')]

/-- Bài tập 10(b): f=o(g), g=o(h). -/
theorem second_growth_ranking :
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ realNthRoot 3 (Real.log x + Real.sin x)) (fun x ↦ x ^ 3 * Real.arctan x) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x ^ 3 * Real.arctan x) (fun x ↦ x ^ 2 + Real.exp (2 * x)) := by
  have hR : Tendsto (fun x : ℝ ↦ Real.log x + Real.sin x) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-1 : ℝ) Real.tendsto_log_atTop)
    exact Eventually.of_forall (fun x ↦ by linarith [Real.neg_one_le_sin x])
  have hf := realNthRoot_three_tendsto_atTop.comp hR
  have hg := tendsto_atTop_of_positive_ratio (by positivity : 0 < Real.pi / 2)
    cubic_arctangent_normalized_atTop (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0))
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (2 * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hh : Tendsto (fun x : ℝ ↦ x ^ 2 + Real.exp (2 * x)) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ hexp
    exact Eventually.of_forall (fun x ↦ by nlinarith [sq_nonneg x])
  have hhn : Tendsto (fun x : ℝ ↦ (x ^ 2 + Real.exp (2 * x)) / Real.exp (2 * x)) atTop (𝓝 (1 : ℝ)) := by
    have hs : Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp (2 * x)) atTop (𝓝 (0 : ℝ)) :=
      (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
    apply (show Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp (2 * x) + 1) atTop (𝓝 (1 : ℝ)) from by
      simpa only [zero_add] using! hs.add_const 1).congr
    intro x
    rw [add_div, div_self (Real.exp_ne_zero _)]
  refine ⟨lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hf hg
    (ratio_zero_of_common_scale logarithmic_sine_cube_root_over_cube_atTop_zero cubic_arctangent_normalized_atTop
      (by positivity : Real.pi / 2 ≠ 0) ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 3 hx.ne'))),
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hg hh ?_⟩
  exact ratio_zero_of_two_scales cubic_arctangent_normalized_atTop hhn one_ne_zero
    (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 3 hx.ne'))
    (Eventually.of_forall (fun x ↦ Real.exp_ne_zero (2 * x)))


theorem cube_sub_log_cube_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (x ^ 3 - Real.log x ^ 3) / x ^ 3) atTop (𝓝 (1 : ℝ)) := by
  have hl : Tendsto (fun x : ℝ ↦ Real.log x ^ 3 / x ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_ofNat] using! logarithm_power_over_real_power_atTop_zero 3 (by norm_num : (0 : ℝ) < 3)
  apply (show Tendsto (fun x : ℝ ↦ 1 - Real.log x ^ 3 / x ^ 3) atTop (𝓝 (1 : ℝ)) from by
    simpa only [sub_zero] using! hl.const_sub 1).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sub_div, div_self (pow_ne_zero 3 hx.ne')]


theorem quintic_cubic_root_normalized_atTop :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 5 + 2 * x - 3) / x ^ (5 / 3 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hlin : Tendsto (fun x : ℝ ↦ x / x ^ 5) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one] using! tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (p := 1) (q := 5) (by decide)
  have hinv : Tendsto (fun x : ℝ ↦ 1 / x ^ 5) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using! (tendsto_pow_atTop (by decide : (5 : ℕ) ≠ 0)).inv_tendsto_atTop
  have hn : Tendsto (fun x : ℝ ↦ (x ^ 5 + 2 * x - 3) / x ^ (3 * (5 / 3 : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ 1 + 2 * (x / x ^ 5) - 3 * (1 / x ^ 5)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, add_zero, sub_zero] using! ((hlin.const_mul 2).const_add 1).sub (hinv.const_mul 3)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (3 : ℝ) * (5 / 3) = 5 by norm_num, Real.rpow_ofNat]
    field_simp [hx.ne']
  simpa only [realNthRoot_one] using!
    signed_cubic_root_normalized_atTop hn (realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)).continuousAt


theorem two_power_sub_square_normalized_atTop :
    Tendsto (fun x : ℝ ↦ ((2 : ℝ) ^ x - x ^ 2) / (2 : ℝ) ^ x) atTop (𝓝 (1 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ x ^ 2 / (2 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_ofNat] using! real_power_over_exponential_base_atTop_zero 2 (by norm_num : (1 : ℝ) < 2)
  apply (show Tendsto (fun x : ℝ ↦ 1 - x ^ 2 / (2 : ℝ) ^ x) atTop (𝓝 (1 : ℝ)) from by
    simpa only [sub_zero] using! hs.const_sub 1).congr
  intro x
  rw [sub_div, div_self (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x).ne']

/-- Bài tập 10(c): g=o(f), f=o(h). -/
theorem third_growth_ranking :
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ realNthRoot 3 (x ^ 5 + 2 * x - 3)) (fun x ↦ x ^ 3 - Real.log x ^ 3) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x ^ 3 - Real.log x ^ 3) (fun x ↦ (2 : ℝ) ^ x - x ^ 2) := by
  have hf := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1)
    cube_sub_log_cube_normalized_atTop (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0))
  have hg := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1)
    quintic_cubic_root_normalized_atTop (tendsto_rpow_atTop (by norm_num : 0 < (5 / 3 : ℝ)))
  have hh := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1)
    two_power_sub_square_normalized_atTop (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num))
  have hgf : Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 5 + 2 * x - 3) / (x ^ 3 - Real.log x ^ 3)) atTop (𝓝 (0 : ℝ)) := by
    apply ratio_zero_of_two_scales quintic_cubic_root_normalized_atTop cube_sub_log_cube_normalized_atTop one_ne_zero
    · simpa only [Real.rpow_ofNat] using! real_power_ratio_atTop_zero (by norm_num : (5 / 3 : ℝ) < 3)
    · exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ (Real.rpow_pos_of_pos hx (5 / 3 : ℝ)).ne')
    · exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 3 hx.ne')
  refine ⟨lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hg hf hgf,
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hf hh ?_⟩
  exact ratio_zero_of_two_scales cube_sub_log_cube_normalized_atTop two_power_sub_square_normalized_atTop one_ne_zero
    (by simpa only [Real.rpow_ofNat] using! real_power_over_exponential_base_atTop_zero 3 (by norm_num : (1 : ℝ) < 2))
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 3 hx.ne'))
    (Eventually.of_forall (fun x ↦ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x).ne'))


theorem identity_add_two_power_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (x + (2 : ℝ) ^ x) / (2 : ℝ) ^ x) atTop (𝓝 (1 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ x / (2 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one] using! real_power_over_exponential_base_atTop_zero 1 (by norm_num : (1 : ℝ) < 2)
  apply (show Tendsto (fun x : ℝ ↦ x / (2 : ℝ) ^ x + 1) atTop (𝓝 (1 : ℝ)) from by
    simpa only [zero_add] using! hs.add_const 1).congr
  intro x
  rw [add_div, div_self (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x).ne']


theorem two_power_over_exp_atTop_zero :
    Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ x / Real.exp x) atTop (𝓝 (0 : ℝ)) := by
  have he : (2 : ℝ) < Real.exp 1 := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using! Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  have hbase0 : -1 < (2 : ℝ) / Real.exp 1 := by
    have hp := div_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos 1)
    linarith
  have hbase1 : (2 : ℝ) / Real.exp 1 < 1 := (div_lt_one (Real.exp_pos 1)).mpr he
  have ht := tendsto_rpow_atTop_of_base_lt_one ((2 : ℝ) / Real.exp 1) hbase0 hbase1
  simpa only [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le,
    Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul] using! ht


theorem exp_sub_two_power_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (Real.exp x - (2 : ℝ) ^ x) / Real.exp x) atTop (𝓝 (1 : ℝ)) := by
  apply (show Tendsto (fun x : ℝ ↦ 1 - (2 : ℝ) ^ x / Real.exp x) atTop (𝓝 (1 : ℝ)) from by
    simpa only [sub_zero] using! two_power_over_exp_atTop_zero.const_sub 1).congr
  intro x
  rw [sub_div, div_self (Real.exp_ne_zero x)]

/-- Bài tập 10(d): g=o(k), k=o(f), f=o(h). -/
theorem fourth_growth_ranking :
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x ^ 2 * Real.log x) (fun x ↦ x ^ 3) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x ^ 3) (fun x ↦ x + (2 : ℝ) ^ x) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x + (2 : ℝ) ^ x) (fun x ↦ Real.exp x - (2 : ℝ) ^ x) := by
  have hg : Tendsto (fun x : ℝ ↦ x ^ 2 * Real.log x) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hk : Tendsto (fun x : ℝ ↦ x ^ 3) atTop atTop := tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)
  have hf := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1)
    identity_add_two_power_normalized_atTop (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num))
  have hh := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 1) exp_sub_two_power_normalized_atTop Real.tendsto_exp_atTop
  have hgk : Tendsto (fun x : ℝ ↦ (x ^ 2 * Real.log x) / x ^ 3) atTop (𝓝 (0 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 (0 : ℝ)) from by
      simpa only [pow_one, Real.rpow_one] using! logarithm_power_over_real_power_atTop_zero 1 (by norm_num : (0 : ℝ) < 1)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  have hkf : Tendsto (fun x : ℝ ↦ x ^ 3 / (x + (2 : ℝ) ^ x)) atTop (𝓝 (0 : ℝ)) := by
    exact ratio_zero_of_common_scale
      (by simpa only [Real.rpow_ofNat] using! real_power_over_exponential_base_atTop_zero 3 (by norm_num : (1 : ℝ) < 2))
      identity_add_two_power_normalized_atTop one_ne_zero
      (Eventually.of_forall (fun x ↦ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x).ne'))
  refine ⟨lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hg hk hgk,
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hk hf hkf,
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hf hh ?_⟩
  exact ratio_zero_of_two_scales identity_add_two_power_normalized_atTop exp_sub_two_power_normalized_atTop one_ne_zero
    two_power_over_exp_atTop_zero (Eventually.of_forall (fun x ↦ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x).ne'))
    (Eventually.of_forall Real.exp_ne_zero)


theorem linear_add_log_cube_normalized_atTop :
    Tendsto (fun x : ℝ ↦ (3 * x + Real.log x ^ 3) / x) atTop (𝓝 (3 : ℝ)) := by
  have hl : Tendsto (fun x : ℝ ↦ Real.log x ^ 3 / x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one] using! logarithm_power_over_real_power_atTop_zero 3 (by norm_num : (0 : ℝ) < 1)
  apply (show Tendsto (fun x : ℝ ↦ 3 + Real.log x ^ 3 / x) atTop (𝓝 (3 : ℝ)) from by
    simpa only [add_zero] using! hl.const_add 3).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [add_div, mul_div_cancel_right₀ _ hx.ne']


theorem linear_log_over_oscillating_square_atTop_zero :
    Tendsto (fun x : ℝ ↦ (x * Real.log x) / (x ^ 2 * (2 + Real.sin x ^ 4))) atTop (𝓝 (0 : ℝ)) := by
  have hu : Tendsto (fun x : ℝ ↦ Real.log x / x / 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div, pow_one, Real.rpow_one] using!
      (logarithm_power_over_real_power_atTop_zero 1 (by norm_num : (0 : ℝ) < 1)).div_const 2
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (mul_nonneg (by linarith) (Real.log_pos hx).le) (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hh : 0 < 2 + Real.sin x ^ 4 := by positivity
    have hid : (x * Real.log x) / (x ^ 2 * (2 + Real.sin x ^ 4)) =
        (Real.log x / x) / (2 + Real.sin x ^ 4) := by field_simp [hx0.ne', hh.ne']
    rw [hid]
    exact div_le_div_of_nonneg_left (div_nonneg (Real.log_pos hx).le hx0.le)
      (by norm_num : (0 : ℝ) < 2) (by nlinarith [sq_nonneg (Real.sin x ^ 2)] : (2 : ℝ) ≤ 2 + Real.sin x ^ 4)

/-- Bài tập 10(e): f=o(g), g=o(k), k=o(h). -/
theorem fifth_growth_ranking :
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ 3 * realNthRoot 3 x) (fun x ↦ 3 * x + Real.log x ^ 3) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ 3 * x + Real.log x ^ 3) (fun x ↦ x * Real.log x) ∧
    LowerOrderInfiniteMagnitudeAlong positiveLogRankingDomain .positiveInfinity
      (fun x ↦ x * Real.log x) (fun x ↦ x ^ 2 * (2 + Real.sin x ^ 4)) := by
  have hf : Tendsto (fun x : ℝ ↦ 3 * realNthRoot 3 x) atTop atTop :=
    realNthRoot_three_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hg := tendsto_atTop_of_positive_ratio (by norm_num : (0 : ℝ) < 3) linear_add_log_cube_normalized_atTop tendsto_id
  have hk : Tendsto (fun x : ℝ ↦ x * Real.log x) atTop atTop := tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hh : Tendsto (fun x : ℝ ↦ x ^ 2 * (2 + Real.sin x ^ 4)) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact Eventually.of_forall (fun x ↦ by nlinarith [mul_nonneg (sq_nonneg x) (pow_nonneg (sq_nonneg (Real.sin x)) 2)])
  have hfn : Tendsto (fun x : ℝ ↦ (3 * realNthRoot 3 x) / x) atTop (𝓝 (0 : ℝ)) := by
    have hr : Tendsto (fun x : ℝ ↦ x ^ ((3 : ℝ)⁻¹) / x) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Real.rpow_one] using! real_power_ratio_atTop_zero (by norm_num : (3 : ℝ)⁻¹ < 1)
    apply (show Tendsto (fun x : ℝ ↦ 3 * (x ^ ((3 : ℝ)⁻¹) / x)) atTop (𝓝 (0 : ℝ)) from by
      simpa only [mul_zero] using! hr.const_mul 3).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [realNthRoot, if_neg (by rintro ⟨_, hn⟩; exact hx.not_gt hn), mul_div_assoc]
    norm_num only [Nat.cast_ofNat]
  have hgk : Tendsto (fun x : ℝ ↦ (3 * x + Real.log x ^ 3) / (x * Real.log x)) atTop (𝓝 (0 : ℝ)) := by
    apply (linear_add_log_cube_normalized_atTop.div_atTop Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_div]
  exact ⟨lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hf hg
      (ratio_zero_of_common_scale hfn linear_add_log_cube_normalized_atTop (by norm_num : (3 : ℝ) ≠ 0)
        ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ hx.ne'))),
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hg hk hgk,
    lower_order_infinite_magnitude_along_of_atTop_ratio positive_log_ranking_domain_tail hk hh linear_log_over_oscillating_square_atTop_zero⟩

end calculus.Chapter03.Section07GrowthRankingExercises
