import calculus.Chapter03.Section07AlgebraSupplement
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field

/-!
§3.7 — Bài tập 3.7.4(a–d), Bài tập 3.7.5(a,b)

Nguồn: dòng 3506–3520.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07InfinityComparisonExercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07AlgebraSupplement
open calculus.Chapter03.Section03Exercises


def shiftedLogComparisonDomain : Set ℝ := {x | 0 < x + 1 ∧ Real.log (x + 1) ≠ 0}


def logComparisonDomain : Set ℝ := {x | 0 < x ∧ Real.log x ≠ 0}


theorem domain_atTop_filter_of_tail {D : Set ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) :
    domainApproachFilter D .positiveInfinity = atTop ∧ NontrivialDomainApproach D .positiveInfinity := by
  have he : domainApproachFilter D .positiveInfinity = atTop := by
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using
      domainApproachFilter_eq_univ_of_eventually_mem (p := .positiveInfinity)
        (by simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hD)
  refine ⟨he, ?_⟩
  change (domainApproachFilter D .positiveInfinity).NeBot
  rw [he]
  infer_instance


theorem infinite_magnitude_along_of_atTop {D : Set ℝ} {f : ℝ → ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hf : Tendsto f atTop atTop) :
    InfiniteMagnitudeAlong D .positiveInfinity f := by
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  refine ⟨hp, ?_⟩
  rw [he]
  exact tendsto_abs_atTop_atTop.comp hf


theorem infinite_magnitude_along_of_ratio {D : Set ℝ} {p : LimitApproach}
    {f g : ℝ → ℝ} {C : ℝ} (hg : InfiniteMagnitudeAlong D p g) (hC : C ≠ 0)
    (hq : Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) (𝓝 C)) :
    InfiniteMagnitudeAlong D p f := by
  refine ⟨hg.1, ?_⟩
  have ht := hq.abs.pos_mul_atTop (abs_pos.mpr hC) hg.2
  apply ht.congr'
  filter_upwards [hg.2.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  rw [abs_div, div_mul_cancel₀ _ hx.ne']


theorem polynomial_comparison_ratio_atTop :
    Tendsto (fun x : ℝ ↦ (3 * x ^ 2 + 2 * x + 5) / (2 * x ^ 3 + 2 * x - 1))
      atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ ↦ 3 + 2 * x⁻¹ + 5 * x⁻¹ ^ 2) atTop (𝓝 (3 : ℝ)) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using!
      ((hi.const_mul 2).const_add 3).add ((hi.pow 2).const_mul 5)
  have hd : Tendsto (fun x : ℝ ↦ 2 + 2 * x⁻¹ ^ 2 - x⁻¹ ^ 3) atTop (𝓝 (2 : ℝ)) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero, sub_zero] using!
      (((hi.pow 2).const_mul 2).const_add 2).sub (hi.pow 3)
  have ht : Tendsto (fun x : ℝ ↦ ((3 + 2 * x⁻¹ + 5 * x⁻¹ ^ 2) /
      (2 + 2 * x⁻¹ ^ 2 - x⁻¹ ^ 3)) * x⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, mul_zero] using!
      (hn.div hd (by norm_num : (2 : ℝ) ≠ 0)).mul hi
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hg : 2 * x ^ 3 + 2 * x - 1 ≠ 0 := by
    have hx3 : 0 < x ^ 3 := pow_pos (by linarith : 0 < x) 3
    linarith
  field_simp [(by linarith : x ≠ 0), hg]

/-- Bài tập 4(a): f và g vô cùng lớn, với f=o(g). -/
theorem quadratic_lower_than_cubic_at_infinity :
    LowerOrderInfiniteMagnitudeAlong univ .positiveInfinity
      (fun x ↦ 3 * x ^ 2 + 2 * x + 5) (fun x ↦ 2 * x ^ 3 + 2 * x - 1) := by
  have hf : Tendsto (fun x : ℝ ↦ 3 * x ^ 2 + 2 * x + 5) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change x ≤ 3 * x ^ 2 + 2 * x + 5
    nlinarith [sq_nonneg x]
  have hg : Tendsto (fun x : ℝ ↦ 2 * x ^ 3 + 2 * x - 1) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change x ≤ 2 * x ^ 3 + 2 * x - 1
    have hp : 0 < x ^ 3 := pow_pos (by linarith : 0 < x) 3
    linarith
  have hiF := infinite_magnitude_along_of_atTop (D := univ) (Eventually.of_forall (fun _ ↦ mem_univ _)) hf
  have hiG := infinite_magnitude_along_of_atTop (D := univ) (Eventually.of_forall (fun _ ↦ mem_univ _)) hg
  refine ⟨hiF, hiG, hiG.1, ?_, ?_⟩
  · have hn := hg.eventually (eventually_gt_atTop (0 : ℝ))
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hn.mono (fun _ hx ↦ hx.ne')
  · simpa only [domainApproachFilter, principal_univ, inf_top_eq] using polynomial_comparison_ratio_atTop


theorem realNthRoot_three_tendsto_atTop : Tendsto (realNthRoot 3) atTop atTop := by
  apply (tendsto_rpow_atTop (by norm_num : 0 < (3 : ℝ)⁻¹)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [realNthRoot, not_lt.mpr hx.le, and_false, ↓reduceIte, Nat.cast_ofNat]


theorem shifted_cubic_roots_ratio_atTop :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x + 2) / realNthRoot 3 x) atTop (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ 1 + 2 * x⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using! (tendsto_inv_atTop_zero.const_mul (2 : ℝ)).const_add 1
  have hr : Tendsto (fun x : ℝ ↦ realNthRoot 3 (1 + 2 * x⁻¹)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, realNthRoot_one] using!
      (realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)).continuousAt.tendsto.comp hi
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply (by decide : Odd 3).pow_injective
  change realNthRoot 3 (1 + 2 * x⁻¹) ^ (3 : ℕ) =
    (realNthRoot 3 (x + 2) / realNthRoot 3 x) ^ (3 : ℕ)
  rw [div_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)), add_div, div_self hx.ne']
  rw [div_eq_mul_inv]

/-- Bài tập 4(b): hai căn bậc ba là các vô cùng lớn tương đương. -/
theorem shifted_cubic_roots_equivalent_at_infinity :
    EquivalentInfiniteMagnitudeFunctionsAlong univ .positiveInfinity
      (fun x ↦ realNthRoot 3 (x + 2)) (realNthRoot 3) := by
  have hg := infinite_magnitude_along_of_atTop (D := univ)
    (Eventually.of_forall (fun _ ↦ mem_univ _)) realNthRoot_three_tendsto_atTop
  have hq : Tendsto (fun x ↦ realNthRoot 3 (x + 2) / realNthRoot 3 x)
      (domainApproachFilter univ .positiveInfinity) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using shifted_cubic_roots_ratio_atTop
  refine ⟨infinite_magnitude_along_of_ratio hg one_ne_zero hq, hg, hg.1, ?_, hq⟩
  have hn := realNthRoot_three_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hn.mono (fun _ hx ↦ hx.ne')

/-- Bài tập 4(c): x⁴/log(x+1)=o(x⁴). -/
theorem logarithmic_quartic_lower_than_quartic_at_infinity :
    LowerOrderInfiniteMagnitudeAlong shiftedLogComparisonDomain .positiveInfinity
      (fun x ↦ x ^ 4 / Real.log (x + 1)) (fun x ↦ x ^ 4) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ shiftedLogComparisonDomain := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact ⟨by linarith, (Real.log_pos (by linarith : 1 < x + 1)).ne'⟩
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  have hf : Tendsto (fun x : ℝ ↦ x ^ 4 / Real.log (x + 1)) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
    have hle : Real.log (x + 1) ≤ x := by
      simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (by linarith : 0 < x + 1)
    apply (le_div_iff₀ hlog).mpr
    have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    calc
      x * Real.log (x + 1) ≤ x ^ 2 := by nlinarith
      _ ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hg : Tendsto (fun x : ℝ ↦ x ^ 4) atTop atTop := tendsto_pow_atTop (by decide : (4 : ℕ) ≠ 0)
  refine ⟨infinite_magnitude_along_of_atTop hD hf, infinite_magnitude_along_of_atTop hD hg,
    hp, ?_, ?_⟩
  · rw [he]
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ pow_ne_zero 4 hx.ne')
  · rw [he]
    have hl : Tendsto (fun x : ℝ ↦ Real.log (x + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    apply hl.inv_tendsto_atTop.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change (Real.log (x + 1))⁻¹ = (x ^ 4 / Real.log (x + 1)) / x ^ 4
    field_simp [pow_ne_zero 4 hx.ne']

/-- Bài tập 4(d): x log x=o(x²/log x). -/
theorem linear_log_lower_than_quadratic_over_log_at_infinity :
    LowerOrderInfiniteMagnitudeAlong logComparisonDomain .positiveInfinity
      (fun x ↦ x * Real.log x) (fun x ↦ x ^ 2 / Real.log x) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ logComparisonDomain := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact ⟨by linarith, (Real.log_pos hx).ne'⟩
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  have hf : Tendsto (fun x : ℝ ↦ x * Real.log x) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hg : Tendsto (fun x : ℝ ↦ x ^ 2 / Real.log x) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change x ≤ x ^ 2 / Real.log x
    apply (le_div_iff₀ (Real.log_pos hx)).mpr
    have hle := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
    nlinarith
  refine ⟨infinite_magnitude_along_of_atTop hD hf, infinite_magnitude_along_of_atTop hD hg,
    hp, ?_, ?_⟩
  · rw [he]
    filter_upwards [hD] with x hx
    exact div_ne_zero (pow_ne_zero 2 hx.1.ne') hx.2
  · rw [he]
    have ht : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_mul, add_zero] using! Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    apply ht.congr'
    filter_upwards [hD] with x hx
    field_simp [hx.1.ne', hx.2]


theorem negative_cubic_root_normalized_atBot :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / x)
      atBot (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 (0 : ℝ)) := tendsto_inv_atBot_zero
  have hn : Tendsto (fun x : ℝ ↦ 1 - 2 * x⁻¹ + x⁻¹ ^ 3) atBot (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero] using!
      ((hi.const_mul 2).const_sub 1).add (hi.pow 3)
  have hr : Tendsto (fun x : ℝ ↦ realNthRoot 3 (1 - 2 * x⁻¹ + x⁻¹ ^ 3)) atBot (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, realNthRoot_one] using!
      (realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)).continuousAt.tendsto.comp hn
  apply hr.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  apply (by decide : Odd 3).pow_injective
  change realNthRoot 3 (1 - 2 * x⁻¹ + x⁻¹ ^ 3) ^ (3 : ℕ) =
    (realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / x) ^ (3 : ℕ)
  rw [div_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3))]
  field_simp [hx.ne]


theorem negative_cubic_root_linear_ratio_atBot :
    Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / (2 * x + 1))
      atBot (𝓝 (1 / 2 : ℝ)) := by
  have hd : Tendsto (fun x : ℝ ↦ 2 + x⁻¹) atBot (𝓝 (2 : ℝ)) := by
    simpa only [add_zero] using! tendsto_inv_atBot_zero.const_add (2 : ℝ)
  have ht : Tendsto (fun x : ℝ ↦ (realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / x) /
      (2 + x⁻¹)) atBot (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply] using! negative_cubic_root_normalized_atBot.div hd (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
  have hg : 2 * x + 1 ≠ 0 := by linarith
  field_simp [(by linarith : x ≠ 0), hg]

/-- Bài tập 5(a): hai đại lượng vô cùng lớn cùng bậc tại −∞. -/
theorem negative_cubic_root_same_order_linear :
    InfiniteMagnitudesWithNonzeroRatioLimitAlong univ .negativeInfinity
      (fun x ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1)) (fun x ↦ 2 * x + 1) := by
  have hp : NontrivialDomainApproach univ .negativeInfinity :=
    (properLimitApproach_negativeInfinity_iff univ).mpr not_bddBelow_univ
  have hg0 : Tendsto (fun x : ℝ ↦ 2 * x + 1) atBot atBot := by
    exact tendsto_atBot_add_const_right _ 1 (tendsto_id.const_mul_atBot (by norm_num : (0 : ℝ) < 2))
  have hg : InfiniteMagnitudeAlong univ .negativeInfinity (fun x ↦ 2 * x + 1) := by
    refine ⟨hp, ?_⟩
    simpa only [domainApproachFilter, principal_univ, inf_top_eq, Function.comp_def] using!
      tendsto_abs_atBot_atTop.comp hg0
  have hq : Tendsto (fun x ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / (2 * x + 1))
      (domainApproachFilter univ .negativeInfinity) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using negative_cubic_root_linear_ratio_atBot
  refine ⟨infinite_magnitude_along_of_ratio hg (by norm_num : (1 / 2 : ℝ) ≠ 0) hq,
    hg, hp, ?_, 1 / 2, by norm_num, hq⟩
  have hn := hg0.eventually (eventually_lt_atBot (0 : ℝ))
  simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hn.mono (fun _ hx ↦ hx.ne)

/-- Bài tập 5(b): f tương đương g/2 tại −∞. -/
theorem negative_cubic_root_linear_principal_coefficient :
    NonvanishingAsymptoticEquivalenceAlong univ .negativeInfinity
      (fun x ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1)) (fun x ↦ (1 / 2) * (2 * x + 1)) := by
  have hs := negative_cubic_root_same_order_linear.2.2
  refine ⟨hs.1, hs.2.1.mono (fun _ hx ↦ mul_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0) hx), ?_⟩
  have ht : Tendsto (fun x : ℝ ↦
      (realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / (2 * x + 1)) / (1 / 2))
      (domainApproachFilter univ .negativeInfinity) (𝓝 (1 : ℝ)) := by
    simpa only [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] using!
      (show Tendsto (fun x ↦ realNthRoot 3 (x ^ 3 - 2 * x ^ 2 + 1) / (2 * x + 1))
        (domainApproachFilter univ .negativeInfinity) (𝓝 (1 / 2 : ℝ)) from by
          simpa only [domainApproachFilter, principal_univ, inf_top_eq] using negative_cubic_root_linear_ratio_atBot).div_const (1 / 2)
  apply ht.congr
  intro x
  rw [div_div, mul_comm (2 * x + 1) (1 / 2)]

end calculus.Chapter03.Section07InfinityComparisonExercises
