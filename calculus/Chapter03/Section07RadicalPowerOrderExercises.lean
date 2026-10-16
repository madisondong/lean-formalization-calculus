import calculus.Chapter03.Section07InfinityComparisonExercises
import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
import calculus.Chapter03.Section07LogarithmicRootPrincipalPart
import calculus.Chapter03.Section07ExercisesInfinitesimalComparisons
import calculus.Chapter03.Section07Fundamental

/-!
§3.7 — Ví dụ 3.7.16(b), 3.7.21(b), Bài tập 3.7.7(a,b), 3.7.8(a,b)

Nguồn: dòng 3355–3357, 3387, 3532–3540.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07RadicalPowerOrderExercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section01Powers calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07InfinityComparisonExercises
open calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
open calculus.Chapter03.Section07LogarithmicRootPrincipalPart
open calculus.Chapter03.Section07ExercisesInfinitesimalComparisons
open calculus.Chapter03.Section07Fundamental


def cubicLeadingRadicalDomain : Set ℝ :=
  {x | 0 ≤ 9 * x ^ 3 - 7 * x + 5 ∧ x ∈ realPowerDomain (3 / 2)}


def fifthRootInfinitesimalDomain : Set ℝ := {x | x ∈ nthRootDomain 5 ∧ x ^ 4 ≠ 0}


def sineRadicalInfinitesimalDomain : Set ℝ := {x | 0 ≤ x ^ 2 + 1}


def reciprocalRadicalDifferenceDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + 2 ∧ 0 ≤ x ^ 2 + 1 ∧ Real.sqrt (x ^ 2 + 2) - Real.sqrt (x ^ 2 + 1) ≠ 0}


def quarticRadicalDifferenceDomain : Set ℝ := {x | 0 ≤ x ^ 4 + x ^ 2}


theorem infinite_magnitude_power_order_along_atTop_of_ratio {D : Set ℝ} {f : ℝ → ℝ} {α C : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hα : 0 < α) (hC : C ≠ 0)
    (ht : Tendsto (fun x ↦ f x / x ^ α) atTop (𝓝 C)) :
    InfiniteMagnitudePowerOrderAlong D .positiveInfinity f (fun x ↦ x) α := by
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  have hg : InfiniteMagnitudeAlong D .positiveInfinity (fun x ↦ x ^ α) :=
    infinite_magnitude_along_of_atTop hD (tendsto_rpow_atTop hα)
  have hq : Tendsto (fun x ↦ f x / x ^ α) (domainApproachFilter D .positiveInfinity) (𝓝 C) := by
    rw [he]
    exact ht
  refine ⟨hα, infinite_magnitude_along_of_ratio hg hC hq,
    infinite_magnitude_along_of_atTop hD tendsto_id, ?_, hp, ?_, C, hC, hq⟩
  · unfold EventuallyRealPowerDefinedAlong
    rw [he]
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ positive_base_mem_real_power_domain hx)
  · rw [he]
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ (Real.rpow_pos_of_pos hx α).ne')


theorem infinite_magnitude_principal_atTop_of_ratio {D : Set ℝ} {f : ℝ → ℝ} {α C : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hα : 0 < α) (hC : C ≠ 0)
    (ht : Tendsto (fun x ↦ f x / x ^ α) atTop (𝓝 C)) :
    HasPowerPrincipalPartAlong D .positiveInfinity f (fun x ↦ x) α C := by
  have ho := infinite_magnitude_power_order_along_atTop_of_ratio hD hα hC ht
  refine ⟨Or.inr ho, hC, ho.2.2.2.2.1, ?_, ?_⟩
  · simpa only [powerPrincipalPart] using ho.2.2.2.2.2.1.mono (fun x hx ↦ mul_ne_zero hC hx)
  · 
    obtain ⟨he, _⟩ := domain_atTop_filter_of_tail hD
    have hqC : Tendsto (fun x ↦ (f x / x ^ α) / C)
        (domainApproachFilter D .positiveInfinity) (𝓝 (1 : ℝ)) := by
      rw [he]
      simpa only [div_self hC] using! ht.div_const C
    apply hqC.congr
    intro x
    simp only [powerPrincipalPart]
    rw [div_div, mul_comm (x ^ α) C]


theorem reciprocal_trial_principal_atTop {D : Set ℝ} {f : ℝ → ℝ} {n : ℕ} {C : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hn : n ≠ 0) (hC : C ≠ 0)
    (ht : Tendsto (fun x ↦ f x / (1 / x) ^ (n : ℝ)) atTop (𝓝 C)) :
    HasPowerPrincipalPartAlong D .positiveInfinity f (fun x ↦ 1 / x) (n : ℝ) C := by
  obtain ⟨he, hp⟩ := domain_atTop_filter_of_tail hD
  have hi : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using! tendsto_inv_atTop_zero
  have hpow : Tendsto (fun x : ℝ ↦ (1 / x) ^ (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_natCast, zero_pow hn] using! hi.pow n
  have hf : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    have hprod : Tendsto (fun x : ℝ ↦ (f x / (1 / x) ^ (n : ℝ)) * (1 / x) ^ (n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Pi.mul_apply, mul_zero] using! ht.mul hpow
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos (one_div_pos.mpr hx) (n : ℝ)).ne']
  apply hasPowerPrincipalPartAlong_real_of_tendsto
  · refine ⟨hp, ?_⟩
    rw [he]
    exact hi
  · exact_mod_cast Nat.pos_of_ne_zero hn
  · unfold EventuallyRealPowerDefinedAlong
    rw [he]
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦
      positive_base_mem_real_power_domain (one_div_pos.mpr hx))
  · rw [he]
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ (one_div_pos.mpr hx).ne')
  · exact hC
  · rw [he]
    exact hf
  · rw [he]
    exact ht


theorem cubic_leading_radical_ratio_atTop :
    Tendsto (fun x : ℝ ↦ Real.sqrt (9 * x ^ 3 - 7 * x + 5) / x ^ (3 / 2 : ℝ))
      atTop (𝓝 (3 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ ↦ 9 - 7 * x⁻¹ ^ 2 + 5 * x⁻¹ ^ 3) atTop (𝓝 (9 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0),
      mul_zero, sub_zero, add_zero] using! (((hi.pow 2).const_mul 7).const_sub 9).add ((hi.pow 3).const_mul 5)
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (9 - 7 * x⁻¹ ^ 2 + 5 * x⁻¹ ^ 3))
      atTop (𝓝 (3 : ℝ)) := by
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    simpa only [Function.comp_def, h9] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he : 9 * x ^ 3 - 7 * x + 5 = x ^ 3 * (9 - 7 * x⁻¹ ^ 2 + 5 * x⁻¹ ^ 3) := by
    field_simp [hx.ne']
  have hroot : Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  rw [he, Real.sqrt_mul (pow_nonneg hx.le 3), hroot,
    mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hx (3 / 2 : ℝ)).ne']


theorem cubic_leading_radical_domain_tail :
    ∀ᶠ x : ℝ in atTop, x ∈ cubicLeadingRadicalDomain := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx3 : x ≤ x ^ 3 := le_self_pow₀ hx.le (by decide : (3 : ℕ) ≠ 0)
  exact ⟨by nlinarith, positive_base_mem_real_power_domain (by linarith : 0 < x)⟩

/-- Ví dụ 3.7.16(b): hàm vô cùng lớn tương đương 3x^(3/2). -/
theorem cubic_leading_radical_same_infinite_order :
    InfiniteMagnitudesWithNonzeroRatioLimitAlong cubicLeadingRadicalDomain .positiveInfinity
      (fun x ↦ Real.sqrt (9 * x ^ 3 - 7 * x + 5)) (fun x ↦ x ^ (3 / 2 : ℝ)) ∧
    NonvanishingAsymptoticEquivalenceAlong cubicLeadingRadicalDomain .positiveInfinity
      (fun x ↦ Real.sqrt (9 * x ^ 3 - 7 * x + 5)) (fun x ↦ 3 * x ^ (3 / 2 : ℝ)) := by
  have ho := infinite_magnitude_power_order_along_atTop_of_ratio cubic_leading_radical_domain_tail
    (by norm_num : 0 < (3 / 2 : ℝ)) (by norm_num : (3 : ℝ) ≠ 0) cubic_leading_radical_ratio_atTop
  have hc := infinite_magnitude_principal_atTop_of_ratio cubic_leading_radical_domain_tail
    (by norm_num : 0 < (3 / 2 : ℝ)) (by norm_num : (3 : ℝ) ≠ 0) cubic_leading_radical_ratio_atTop
  refine ⟨⟨ho.2.1, infinite_magnitude_along_of_atTop cubic_leading_radical_domain_tail
    (tendsto_rpow_atTop (by norm_num : 0 < (3 / 2 : ℝ))), ho.2.2.2.2⟩, ?_⟩
  simpa only [powerPrincipalPart] using! hc.2.2

/-- Ví dụ 3.7.21(b): phần chính 3x^(3/2), bậc 3/2. -/
theorem cubic_leading_radical_principal_part :
    HasPowerPrincipalPartAlong cubicLeadingRadicalDomain .positiveInfinity
      (fun x ↦ Real.sqrt (9 * x ^ 3 - 7 * x + 5)) (fun x ↦ x) (3 / 2) 3 :=
  infinite_magnitude_principal_atTop_of_ratio cubic_leading_radical_domain_tail
    (by norm_num : 0 < (3 / 2 : ℝ)) (by norm_num : (3 : ℝ) ≠ 0) cubic_leading_radical_ratio_atTop

/-- Bài tập 7(a): phần chính 2/x², bậc 2 theo 1/x. -/
theorem fifth_root_rational_infinitesimal_principal_part :
    HasPowerPrincipalPartAlong fifthRootInfinitesimalDomain .positiveInfinity
      (fun x ↦ (2 * x ^ 2 + realNthRoot 5 x) / x ^ 4) (fun x ↦ 1 / x) 2 2 := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ fifthRootInfinitesimalDomain := by
    exact (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ ⟨Or.inl (by decide : Odd 5), pow_ne_zero 4 hx.ne'⟩)
  apply reciprocal_trial_principal_atTop (n := 2) hD (by decide) (by norm_num : (2 : ℝ) ≠ 0)
  have hr : Tendsto (fun x : ℝ ↦ realNthRoot 5 x / x ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ x ^ (-((9 : ℝ) / 5))) atTop (𝓝 (0 : ℝ)) :=
      tendsto_rpow_neg_atTop (by norm_num : 0 < (9 : ℝ) / 5)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [realNthRoot, if_neg (by rintro ⟨_, hh⟩; exact hx.not_gt hh), ← Real.rpow_natCast,
      ← Real.rpow_sub hx]
    norm_num
  have ht : Tendsto (fun x : ℝ ↦ 2 + realNthRoot 5 x / x ^ 2) atTop (𝓝 (2 : ℝ)) := by
    simpa only [add_zero] using! hr.const_add 2
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_natCast]
  field_simp [hx.ne']


theorem square_root_residual_times_identity_atTop :
    Tendsto (fun x : ℝ ↦ (Real.sqrt (x ^ 2 + 1) - x) * x) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 1) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, Real.sqrt_one] using! normalized_quadratic_sqrt_atTop 1 0 1
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 1) / x + 1) atTop (𝓝 (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using! hs.add_const 1
  have ht : Tendsto (fun x : ℝ ↦ 1 / (Real.sqrt (x ^ 2 + 1) / x + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply] using! (tendsto_const_nhds (x := (1 : ℝ))).div hd (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)] with x hx hden
  have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 1)
  have hm : ((Real.sqrt (x ^ 2 + 1) - x) * x) * (Real.sqrt (x ^ 2 + 1) / x + 1) = 1 := by
    field_simp [hx.ne']
    nlinarith [hsq]
  exact ((eq_div_iff hden).mpr hm).symm

/-- Bài tập 7(b): phần chính 1/(2x), bậc 1 theo 1/x. -/
theorem sine_radical_infinitesimal_principal_part :
    HasPowerPrincipalPartAlong sineRadicalInfinitesimalDomain .positiveInfinity
      (fun x ↦ Real.sin (Real.sqrt (x ^ 2 + 1) - x)) (fun x ↦ 1 / x) 1 (1 / 2) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ sineRadicalInfinitesimalDomain :=
    Eventually.of_forall (fun x ↦ by
      change 0 ≤ x ^ 2 + 1
      nlinarith [sq_nonneg x])
  have hu : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 1) - x) atTop (𝓝 (0 : ℝ)) := by
    have hp : Tendsto (fun x : ℝ ↦ ((Real.sqrt (x ^ 2 + 1) - x) * x) * x⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Pi.mul_apply, mul_zero] using! square_root_residual_times_identity_atTop.mul tendsto_inv_atTop_zero
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  have hune : ∀ᶠ x : ℝ in atTop, Real.sqrt (x ^ 2 + 1) - x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 1)
    intro hz
    have he : Real.sqrt (x ^ 2 + 1) = x := sub_eq_zero.mp hz
    rw [he] at hsq
    linarith
  have hup : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 1) - x) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, by simpa only [mem_compl_iff, mem_singleton_iff] using hune⟩
  have hs : Tendsto (fun x : ℝ ↦ Real.sin (Real.sqrt (x ^ 2 + 1) - x) /
      (Real.sqrt (x ^ 2 + 1) - x)) atTop (𝓝 (1 : ℝ)) := by
    have hsin : Tendsto (fun y : ℝ ↦ Real.sin y / y) (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa only [domainApproachFilter, sdiff_eq, univ_inter, Real.sin_zero, sub_zero,
        Real.cos_zero] using! derivative_quotient_zero (Real.hasDerivAt_sin 0)
    simpa only [Function.comp_def] using! hsin.comp hup
  have ht : Tendsto (fun x : ℝ ↦ (Real.sin (Real.sqrt (x ^ 2 + 1) - x) /
      (Real.sqrt (x ^ 2 + 1) - x)) * ((Real.sqrt (x ^ 2 + 1) - x) * x))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.mul_apply, one_mul] using! hs.mul square_root_residual_times_identity_atTop
  have hnorm : Tendsto (fun x : ℝ ↦ Real.sin (Real.sqrt (x ^ 2 + 1) - x) /
      (1 / x) ^ ((1 : ℕ) : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hune] with x hx hne
    rw [Real.rpow_natCast, pow_one]
    field_simp [hx.ne', hne]
  simpa only [Nat.cast_one] using!
    reciprocal_trial_principal_atTop (n := 1) hD (by decide) (by norm_num : (1 / 2 : ℝ) ≠ 0) hnorm

/-- Bài tập 8(a): phần chính 2x, bậc 1. -/
theorem reciprocal_radical_difference_principal_part :
    HasPowerPrincipalPartAlong reciprocalRadicalDifferenceDomain .positiveInfinity
      (fun x ↦ 1 / (Real.sqrt (x ^ 2 + 2) - Real.sqrt (x ^ 2 + 1))) (fun x ↦ x) 1 2 := by
  have hne : ∀ x : ℝ, Real.sqrt (x ^ 2 + 2) - Real.sqrt (x ^ 2 + 1) ≠ 0 := by
    intro x hz
    have h1 := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 1)
    have h2 := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 2)
    rw [sub_eq_zero.mp hz] at h2
    linarith
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ reciprocalRadicalDifferenceDomain :=
    Eventually.of_forall (fun x ↦ ⟨by nlinarith [sq_nonneg x], by nlinarith [sq_nonneg x], hne x⟩)
  apply infinite_magnitude_principal_atTop_of_ratio hD (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ) ≠ 0)
  have hs1 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 1) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, Real.sqrt_one] using! normalized_quadratic_sqrt_atTop 1 0 1
  have hs2 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 2) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, Real.sqrt_one] using! normalized_quadratic_sqrt_atTop 1 0 2
  have ht : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 2) / x + Real.sqrt (x ^ 2 + 1) / x)
      atTop (𝓝 (2 : ℝ)) := by
    simpa only [Pi.add_apply, show (1 : ℝ) + 1 = 2 by norm_num] using! hs2.add hs1
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h1 := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 1)
  have h2 := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 2)
  have hprod : (Real.sqrt (x ^ 2 + 2) - Real.sqrt (x ^ 2 + 1)) *
      (Real.sqrt (x ^ 2 + 2) + Real.sqrt (x ^ 2 + 1)) = 1 := by nlinarith
  have hid : 1 / (Real.sqrt (x ^ 2 + 2) - Real.sqrt (x ^ 2 + 1)) =
      Real.sqrt (x ^ 2 + 2) + Real.sqrt (x ^ 2 + 1) := by
    apply (div_eq_iff (hne x)).mpr
    nlinarith [hprod]
  rw [Real.rpow_one, hid, add_div]

/-- Bài tập 8(b): phần chính −x², bậc 2. -/
theorem quartic_radical_difference_principal_part :
    HasPowerPrincipalPartAlong quarticRadicalDifferenceDomain .positiveInfinity
      (fun x ↦ x - Real.sqrt (x ^ 4 + x ^ 2)) (fun x ↦ x) 2 (-1) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ quarticRadicalDifferenceDomain :=
    Eventually.of_forall (fun x ↦ by
      change 0 ≤ x ^ 4 + x ^ 2
      positivity)
  apply infinite_magnitude_principal_atTop_of_ratio hD (by norm_num : (0 : ℝ) < 2) (by norm_num : (-1 : ℝ) ≠ 0)
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 4 + x ^ 2) / x ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, one_mul, add_zero, ← pow_mul,
      show (2 : ℕ) * 2 = 4 by decide, Real.sqrt_one] using!
      (normalized_quadratic_sqrt_atTop 1 1 0).comp (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have ht : Tendsto (fun x : ℝ ↦ x⁻¹ - Real.sqrt (x ^ 4 + x ^ 2) / x ^ 2) atTop (𝓝 (-1 : ℝ)) := by
    simpa only [Pi.sub_apply, zero_sub] using! tendsto_inv_atTop_zero.sub hs
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_two]
  generalize Real.sqrt (x ^ 4 + x ^ 2) = y
  field_simp [hx.ne']

end calculus.Chapter03.Section07RadicalPowerOrderExercises
