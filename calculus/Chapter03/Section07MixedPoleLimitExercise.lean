import calculus.Chapter03.Section07LogarithmicRatioExercises
import calculus.Chapter03.Section07ComposedQuadraticRatioExercises
import calculus.Chapter03.Section02Infinite

/-!
§3.7 — Bài tập 3.7.11(n)

Nguồn: dòng 3696.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07MixedPoleLimitExercise
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02OneSided calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07Fundamental calculus.Chapter03.Section07LogarithmicRatioExercises
open calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section07CosineRatioExercises


def mixedPoleDomain : Set ℝ :=
  {x | 0 < 1 + x ∧ Real.arctan (x ^ 3) + 1 - Real.cos (2 * x) ≠ 0}


theorem mixed_pole_numerator_normalized_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 : ℝ)) := by
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2) - 1) 0 0 := by
    simpa using! (((hasDerivAt_id (0 : ℝ)).pow 2).exp).sub_const 1
  have hl : HasDerivAt (fun x : ℝ ↦ Real.log (x + 1)) 1 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).add_const 1).log (by norm_num : (0 : ℝ) + 1 ≠ 0)
  have hn : HasDerivAt
      (fun x : ℝ ↦ Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) (-1) 0 := by
    simpa using! (he.sin.add (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 2)).sub hl
  simpa using! derivative_quotient_zero hn


theorem mixed_pole_denominator_normalized_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ x ^ 3) (domainApproachFilter univ (.point 0))
      (domainApproachFilter univ (.point 0)) := by
    change Tendsto (fun x : ℝ ↦ x ^ 3) (domainApproachFilter univ (.point 0)) (𝓝[univ \ {0}] 0)
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! hi.pow 3, ?_⟩
    filter_upwards [punctured_zero_eventually_ne] with x hx
    exact ⟨mem_univ _, by simpa using pow_ne_zero 3 hx⟩
  have hd : HasDerivAt Real.arctan 1 0 := by simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have ha : Tendsto (fun x : ℝ ↦ Real.arctan (x ^ 3) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.arctan_zero, sub_zero] using!
      (derivative_quotient_zero hd).comp hu
  have hat : Tendsto (fun x : ℝ ↦ Real.arctan (x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ (Real.arctan (x ^ 3) / x ^ 3) * x)
        (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
      simpa only [Pi.mul_apply, mul_zero] using! ha.mul hi
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    rw [pow_succ, ← div_div, div_mul_cancel₀ _ hx]
  have hc : Tendsto (fun x : ℝ ↦ (1 - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [show (2 : ℝ) ^ 2 / 2 = 2 by norm_num] using! normalized_scaled_cosine 2
  have ht : Tendsto (fun x : ℝ ↦ Real.arctan (x ^ 3) / x ^ 2 + (1 - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [Pi.add_apply, zero_add] using! hat.add hc
  apply ht.congr
  intro x
  rw [← add_div]
  congr 1
  ring


theorem mixedPoleDomain_eventually_at_zero :
    ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ mixedPoleDomain := by
  have hlog : ∀ᶠ x in domainApproachFilter univ (.point 0), 0 < 1 + x := log_one_add_eventually_defined
  have hden : ∀ᶠ x in domainApproachFilter univ (.point 0),
      Real.arctan (x ^ 3) + 1 - Real.cos (2 * x) ≠ 0 :=
    (mixed_pole_denominator_normalized_at_zero.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)).mono
      fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  exact hlog.and hden


theorem mixed_pole_weighted_quotient_at_zero :
    Tendsto (fun x : ℝ ↦ x *
      ((Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
        (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ ↦
      ((Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) / x) /
        ((Real.arctan (x ^ 3) + 1 - Real.cos (2 * x)) / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply] using!
      mixed_pole_numerator_normalized_at_zero.div mixed_pole_denominator_normalized_at_zero
        (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  have he : (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x)) / x ^ 2 =
      ((Real.arctan (x ^ 3) + 1 - Real.cos (2 * x)) / x) / x := by rw [div_div, pow_two]
  rw [he, div_div_div_cancel_right₀ hx, div_div_eq_mul_div]
  ring

/-- Bài tập 3.7.11(n): giới hạn phải −∞, giới hạn trái +∞; giới hạn hai phía không tồn tại. -/
theorem mixed_pole_has_opposite_one_sided_infinities :
    ¬ HasDomainLimit mixedPoleDomain
      (fun x ↦ (Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
        (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) 0 ∧
    DomainRightBotLimit mixedPoleDomain
      (fun x ↦ (Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
        (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) 0 ∧
    DomainLeftTopLimit mixedPoleDomain
      (fun x ↦ (Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
        (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) 0 := by
  have hD := mixedPoleDomain_eventually_at_zero
  have hweighted := domainLimit_of_eventually_domain hD mixed_pole_weighted_quotient_at_zero
  have hno : ¬ HasDomainLimit mixedPoleDomain
      (fun x ↦ (Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
        (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) 0 := by
    rintro ⟨L, hL⟩
    have hi : DomainLimit mixedPoleDomain (fun x : ℝ ↦ x) 0 0 :=
      domainLimit_of_continuousAt hL.1 continuous_id.continuousAt
    have hz := domainLimit_mul hi hL
    have he := domainLimit_unique hweighted hz
    norm_num at he
  have hRmono : (𝓝[>] (0 : ℝ)) ≤ domainApproachFilter univ (.point 0) := by
    change (𝓝[Ioi (0 : ℝ)] 0) ≤ (𝓝[univ \ {0}] 0)
    apply nhdsWithin_mono 0
    intro x hx
    exact ⟨mem_univ _, by simpa using hx.ne'⟩
  have hLmono : (𝓝[<] (0 : ℝ)) ≤ domainApproachFilter univ (.point 0) := by
    change (𝓝[Iio (0 : ℝ)] 0) ≤ (𝓝[univ \ {0}] 0)
    apply nhdsWithin_mono 0
    intro x hx
    exact ⟨mem_univ _, by simpa using hx.ne⟩
  have heR : (𝓝[mixedPoleDomain ∩ Ioi 0] (0 : ℝ)) = 𝓝[>] 0 := by
    rw [Set.inter_comm mixedPoleDomain (Ioi 0), nhdsWithin_inter']
    exact inf_eq_left.mpr (le_principal_iff.mpr (hD.filter_mono hRmono))
  have heL : (𝓝[mixedPoleDomain ∩ Iio 0] (0 : ℝ)) = 𝓝[<] 0 := by
    rw [Set.inter_comm mixedPoleDomain (Iio 0), nhdsWithin_inter']
    exact inf_eq_left.mpr (le_principal_iff.mpr (hD.filter_mono hLmono))
  have haccR : RightAccumulationPointOf mixedPoleDomain 0 := by
    apply rightAccumulation_iff_restricted.mpr
    apply accumulationPointOf_iff_neBot.mpr
    have he : (mixedPoleDomain ∩ Ioi 0) \ {0} = mixedPoleDomain ∩ Ioi 0 := by
      ext x
      constructor
      · exact fun hx ↦ hx.1
      · exact fun hx ↦ ⟨hx, by simpa using hx.2.ne'⟩
    rw [he, heR]
    infer_instance
  have haccL : LeftAccumulationPointOf mixedPoleDomain 0 := by
    apply leftAccumulation_iff_restricted.mpr
    apply accumulationPointOf_iff_neBot.mpr
    have he : (mixedPoleDomain ∩ Iio 0) \ {0} = mixedPoleDomain ∩ Iio 0 := by
      ext x
      constructor
      · exact fun hx ↦ hx.1
      · exact fun hx ↦ ⟨hx, by simpa using hx.2.ne⟩
    rw [he, heL]
    infer_instance
  refine ⟨hno, ⟨haccR, ?_⟩, ⟨haccL, ?_⟩⟩
  · rw [heR]
    have ht := (mixed_pole_weighted_quotient_at_zero.mono_left hRmono).neg_mul_atTop
      (by norm_num : (-1 / 2 : ℝ) < 0) tendsto_inv_nhdsGT_zero
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    calc
      _ = (x * x⁻¹) *
        ((Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
          (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hx.ne', one_mul]
  · rw [heL]
    have ht := (mixed_pole_weighted_quotient_at_zero.mono_left hLmono).neg_mul_atBot
      (by norm_num : (-1 / 2 : ℝ) < 0) tendsto_inv_nhdsLT_zero
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change x < 0 at hx
    calc
      _ = (x * x⁻¹) *
        ((Real.sin (Real.exp (x ^ 2) - 1) + 2 * x ^ 3 - Real.log (x + 1)) /
          (Real.arctan (x ^ 3) + 1 - Real.cos (2 * x))) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hx.ne, one_mul]

end calculus.Chapter03.Section07MixedPoleLimitExercise
