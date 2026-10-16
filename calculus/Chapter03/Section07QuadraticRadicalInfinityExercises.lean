import calculus.Chapter03.Section07
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
§3.7 — Bài tập 3.7.13(a,b,c,d,f,g)

Nguồn: dòng 3728–3737.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section07 calculus.Chapter03.Section02Infinite


def threeRadicalRatioDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + 4 ∧ 0 ≤ x ∧ 0 ≤ x ^ 2 - 4 ∧ Real.sqrt (x ^ 2 - 4) + x ≠ 0}


def radicalDifferenceDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + 8 * x + 3 ∧ 0 ≤ x ^ 2 + 4 * x + 3}


def radicalRatioDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + 14 ∧ 0 ≤ x ^ 2 - 2 ∧ Real.sqrt (x ^ 2 - 2) + x ≠ 0}


def leadingRadicalDifferenceDomain : Set ℝ := {x | 0 ≤ 4 * x ^ 2 - 7 * x + 4}


theorem normalized_quadratic_sqrt_atTop (c a b : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.sqrt (c * x ^ 2 + a * x + b) / x) atTop (𝓝 (Real.sqrt c)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ ↦ c + a * x⁻¹ + b * x⁻¹ ^ 2) atTop (𝓝 c) := by
    simpa using ((hi.const_mul a).const_add c).add ((hi.pow 2).const_mul b)
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (c + a * x⁻¹ + b * x⁻¹ ^ 2)) atTop (𝓝 (Real.sqrt c)) := by
    simpa only [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 := hx.ne'
  have he : c * x ^ 2 + a * x + b = x ^ 2 * (c + a * x⁻¹ + b * x⁻¹ ^ 2) := by
    field_simp [hx0]
  rw [he, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  field_simp [hx0]


theorem normalized_quadratic_sqrt_atBot (c a b : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.sqrt (c * x ^ 2 + a * x + b) / x) atBot (𝓝 (-Real.sqrt c)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hn : Tendsto (fun x : ℝ ↦ c + a * x⁻¹ + b * x⁻¹ ^ 2) atBot (𝓝 c) := by
    simpa using ((hi.const_mul a).const_add c).add ((hi.pow 2).const_mul b)
  have hs : Tendsto (fun x : ℝ ↦ -Real.sqrt (c + a * x⁻¹ + b * x⁻¹ ^ 2)) atBot (𝓝 (-Real.sqrt c)) := by
    simpa only [Function.comp_def, Pi.neg_apply] using (Real.continuous_sqrt.continuousAt.tendsto.comp hn).neg
  apply hs.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  have hx0 := hx.ne
  have he : c * x ^ 2 + a * x + b = x ^ 2 * (c + a * x⁻¹ + b * x⁻¹ ^ 2) := by
    field_simp [hx0]
  rw [he, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  field_simp [hx0]


theorem quadratic_eventually_positive (l : Filter ℝ)
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) l (𝓝 0))
    (hx : ∀ᶠ x in l, x ≠ 0) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∀ᶠ x in l, 0 < c * x ^ 2 + a * x + b := by
  have hn : Tendsto (fun x : ℝ ↦ c + a * x⁻¹ + b * x⁻¹ ^ 2) l (𝓝 c) := by
    simpa using ((hi.const_mul a).const_add c).add ((hi.pow 2).const_mul b)
  filter_upwards [hx, hn.eventually (Ioi_mem_nhds hc)] with x hx0 hp
  have he : c * x ^ 2 + a * x + b = x ^ 2 * (c + a * x⁻¹ + b * x⁻¹ ^ 2) := by
    field_simp [hx0]
  rw [he]
  exact mul_pos (sq_pos_of_ne_zero hx0) hp


theorem domainAtTopLimit_of_eventually_domain {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hf : Tendsto f atTop (𝓝 L)) : DomainAtTopLimit D f L := by
  have he : domainApproachFilter D .positiveInfinity = atTop := by
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using
      domainApproachFilter_eq_univ_of_eventually_mem
        (p := .positiveInfinity) (by simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hD)
  have hp : NontrivialDomainApproach D .positiveInfinity := by
    change (domainApproachFilter D .positiveInfinity).NeBot
    rw [he]
    infer_instance
  apply (domainAtTopLimit_iff_tendsto ((properLimitApproach_positiveInfinity_iff D).mp hp)).mpr
  change Tendsto f (domainApproachFilter D .positiveInfinity) (𝓝 L)
  rwa [he]


theorem domainAtBotLimit_of_eventually_domain {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ∀ᶠ x : ℝ in atBot, x ∈ D) (hf : Tendsto f atBot (𝓝 L)) : DomainAtBotLimit D f L := by
  have he : domainApproachFilter D .negativeInfinity = atBot := by
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using
      domainApproachFilter_eq_univ_of_eventually_mem
        (p := .negativeInfinity) (by simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hD)
  have hp : NontrivialDomainApproach D .negativeInfinity := by
    change (domainApproachFilter D .negativeInfinity).NeBot
    rw [he]
    infer_instance
  apply (domainAtBotLimit_iff_tendsto ((properLimitApproach_negativeInfinity_iff D).mp hp)).mpr
  change Tendsto f (domainApproachFilter D .negativeInfinity) (𝓝 L)
  rwa [he]


theorem quadratic_sqrt_plus_identity_atBot (a b : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + a * x + b) + x) atBot (𝓝 (-a / 2)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + a * x + b) / x) atBot (𝓝 (-1 : ℝ)) := by
    simpa only [one_mul, Real.sqrt_one] using normalized_quadratic_sqrt_atBot 1 a b
  have hn : Tendsto (fun x : ℝ ↦ a + b * x⁻¹) atBot (𝓝 a) := by simpa using (hi.const_mul b).const_add a
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + a * x + b) / x - 1) atBot (𝓝 (-2 : ℝ)) := by
    convert! hs.sub_const 1 using 1; norm_num
  have ht : Tendsto (fun x : ℝ ↦ (a + b * x⁻¹) / (Real.sqrt (x ^ 2 + a * x + b) / x - 1))
      atBot (𝓝 (-a / 2)) := by convert! hn.div hd (by norm_num : (-2 : ℝ) ≠ 0) using 1; ring
  apply ht.congr'
  have hx : ∀ᶠ x : ℝ in atBot, x ≠ 0 := (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne
  have hp := quadratic_eventually_positive atBot hi hx (by norm_num : (0 : ℝ) < 1) a b
  filter_upwards [eventually_lt_atBot (0 : ℝ), hp] with x hx hpos
  have hx0 := hx.ne
  have hs0 := Real.sqrt_nonneg (x ^ 2 + a * x + b)
  have hsq := Real.sq_sqrt (show 0 ≤ x ^ 2 + a * x + b by simpa only [one_mul] using hpos.le)
  have hden : Real.sqrt (x ^ 2 + a * x + b) - x ≠ 0 := by linarith
  have hnum : a + b * x⁻¹ = (a * x + b) / x := by
    rw [add_div, mul_div_assoc, div_self hx0, mul_one, div_eq_mul_inv]
  have hnorm : Real.sqrt (x ^ 2 + a * x + b) / x - 1 =
      (Real.sqrt (x ^ 2 + a * x + b) - x) / x := by
    rw [sub_div, div_self hx0]
  rw [hnum, hnorm, div_div_div_cancel_right₀ hx0]
  apply (div_eq_iff hden).mpr
  nlinarith

/-- Bài tập 3.7.13(b): giới hạn tại −∞ bằng −2. -/
theorem radical_difference_at_negative_infinity :
    DomainAtBotLimit radicalDifferenceDomain
      (fun x ↦ Real.sqrt (x ^ 2 + 8 * x + 3) - Real.sqrt (x ^ 2 + 4 * x + 3)) (-2) := by
  have hx : ∀ᶠ x : ℝ in atBot, x ≠ 0 := (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne
  have hp8 := quadratic_eventually_positive atBot tendsto_inv_atBot_zero hx (by norm_num : (0 : ℝ) < 1) 8 3
  have hp4 := quadratic_eventually_positive atBot tendsto_inv_atBot_zero hx (by norm_num : (0 : ℝ) < 1) 4 3
  have hD : ∀ᶠ x : ℝ in atBot, x ∈ radicalDifferenceDomain := by
    filter_upwards [hp8,hp4] with x h8 h4
    exact ⟨by simpa only [one_mul] using h8.le, by simpa only [one_mul] using h4.le⟩
  apply domainAtBotLimit_of_eventually_domain hD
  convert! (quadratic_sqrt_plus_identity_atBot 8 3).sub (quadratic_sqrt_plus_identity_atBot 4 3) using 1
  · ext x; ring
  · norm_num


theorem radicalRatioDomain_eventually_atBot : ∀ᶠ x : ℝ in atBot, x ∈ radicalRatioDomain := by
  filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
  have hp : 0 ≤ x ^ 2 - 2 := by nlinarith
  refine ⟨by nlinarith [sq_nonneg x], hp, ?_⟩
  intro hz
  have hs := Real.sq_sqrt hp
  have he : Real.sqrt (x ^ 2 - 2) = -x := by linarith
  rw [he] at hs
  nlinarith

/-- Bài tập 3.7.13(c): giới hạn tại −∞ bằng −7. -/
theorem radical_ratio_at_negative_infinity :
    DomainAtBotLimit radicalRatioDomain
      (fun x ↦ (Real.sqrt (x ^ 2 + 14) + x) / (Real.sqrt (x ^ 2 - 2) + x)) (-7) := by
  apply domainAtBotLimit_of_eventually_domain radicalRatioDomain_eventually_atBot
  have h14 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 14) / x - 1) atBot (𝓝 (-2 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, ← sub_eq_add_neg, Real.sqrt_one,
      Pi.sub_apply, show (-1 : ℝ) - 1 = -2 by norm_num] using!
      (normalized_quadratic_sqrt_atBot 1 0 14).sub_const 1
  have h2 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 - 2) / x - 1) atBot (𝓝 (-2 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, ← sub_eq_add_neg, Real.sqrt_one,
      Pi.sub_apply, show (-1 : ℝ) - 1 = -2 by norm_num] using!
      (normalized_quadratic_sqrt_atBot 1 0 (-2)).sub_const 1
  have ht : Tendsto (fun x : ℝ ↦ -7 * ((Real.sqrt (x ^ 2 - 2) / x - 1) /
      (Real.sqrt (x ^ 2 + 14) / x - 1))) atBot (𝓝 (-7 : ℝ)) := by
    convert! (h2.div h14 (by norm_num : (-2 : ℝ) ≠ 0)).const_mul (-7) using 1; norm_num
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (-2 : ℝ),radicalRatioDomain_eventually_atBot] with x hx hD
  have hx0 : x ≠ 0 := by linarith
  have hsq14 := Real.sq_sqrt hD.1
  have hsq2 := Real.sq_sqrt hD.2.1
  have hm14 : Real.sqrt (x ^ 2 + 14) - x ≠ 0 := by linarith [Real.sqrt_nonneg (x ^ 2 + 14)]
  have hm2 : Real.sqrt (x ^ 2 - 2) - x ≠ 0 := by linarith [Real.sqrt_nonneg (x ^ 2 - 2)]
  have hn14 : Real.sqrt (x ^ 2 + 14) / x - 1 ≠ 0 := by
    intro hz
    have he : Real.sqrt (x ^ 2 + 14) = x := (div_eq_one_iff_eq hx0).mp (by linarith)
    linarith [Real.sqrt_nonneg (x ^ 2 + 14)]
  have he14 : Real.sqrt (x ^ 2 + 14) + x = 14 / (Real.sqrt (x ^ 2 + 14) - x) := by
    apply (eq_div_iff hm14).mpr
    nlinarith
  have he2 : Real.sqrt (x ^ 2 - 2) + x = -2 / (Real.sqrt (x ^ 2 - 2) - x) := by
    apply (eq_div_iff hm2).mpr
    nlinarith
  have hnorm2 : Real.sqrt (x ^ 2 - 2) / x - 1 = (Real.sqrt (x ^ 2 - 2) - x) / x := by
    rw [sub_div, div_self hx0]
  have hnorm14 : Real.sqrt (x ^ 2 + 14) / x - 1 = (Real.sqrt (x ^ 2 + 14) - x) / x := by
    rw [sub_div, div_self hx0]
  rw [hnorm2, hnorm14, div_div_div_cancel_right₀ hx0, he14, he2]
  field_simp [hm14, hm2]
  norm_num

/-- Bài tập 3.7.13(d): giới hạn tại −∞ bằng −7. -/
theorem radical_ratio_at_negative_infinity_duplicate :
    DomainAtBotLimit radicalRatioDomain
      (fun x ↦ (Real.sqrt (x ^ 2 + 14) + x) / (Real.sqrt (x ^ 2 - 2) + x)) (-7) :=
  radical_ratio_at_negative_infinity

/-- Bài tập 3.7.13(g): giới hạn tại +∞ bằng 1. -/
theorem radical_ratio_at_positive_infinity :
    DomainAtTopLimit radicalRatioDomain
      (fun x ↦ (Real.sqrt (x ^ 2 + 14) + x) / (Real.sqrt (x ^ 2 - 2) + x)) 1 := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ radicalRatioDomain := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    refine ⟨by nlinarith [sq_nonneg x], by nlinarith, ?_⟩
    linarith [Real.sqrt_nonneg (x ^ 2 - 2)]
  apply domainAtTopLimit_of_eventually_domain hD
  have h14 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 14) / x + 1) atTop (𝓝 (2 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, ← sub_eq_add_neg, Real.sqrt_one,
      Pi.add_apply, show (1 : ℝ) + 1 = 2 by norm_num] using!
      (normalized_quadratic_sqrt_atTop 1 0 14).add_const 1
  have h2 : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 - 2) / x + 1) atTop (𝓝 (2 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, ← sub_eq_add_neg, Real.sqrt_one,
      Pi.add_apply, show (1 : ℝ) + 1 = 2 by norm_num] using!
      (normalized_quadratic_sqrt_atTop 1 0 (-2)).add_const 1
  apply (show Tendsto (fun x : ℝ ↦ (Real.sqrt (x ^ 2 + 14) / x + 1) /
      (Real.sqrt (x ^ 2 - 2) / x + 1)) atTop (𝓝 (1 : ℝ)) from by
        simpa only [Pi.div_apply, show (2 : ℝ) / 2 = 1 by norm_num] using!
          h14.div h2 (by norm_num : (2 : ℝ) ≠ 0)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hnum : Real.sqrt (x ^ 2 + 14) / x + 1 = (Real.sqrt (x ^ 2 + 14) + x) / x := by
    rw [add_div, div_self hx.ne']
  have hden : Real.sqrt (x ^ 2 - 2) / x + 1 = (Real.sqrt (x ^ 2 - 2) + x) / x := by
    rw [add_div, div_self hx.ne']
  rw [hnum, hden, div_div_div_cancel_right₀ hx.ne']

/-- Bài tập 3.7.13(a): giới hạn tại +∞ bằng 3/2. -/
theorem three_radical_ratio_at_positive_infinity :
    DomainAtTopLimit threeRadicalRatioDomain
      (fun x ↦ (Real.sqrt (x ^ 2 + 4) + 2 * x + 3 * Real.sqrt x) /
        (Real.sqrt (x ^ 2 - 4) + x)) (3 / 2) := by
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ threeRadicalRatioDomain := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
    refine ⟨by nlinarith [sq_nonneg x], by linarith, by nlinarith, ?_⟩
    linarith [Real.sqrt_nonneg (x ^ 2 - 4)]
  apply domainAtTopLimit_of_eventually_domain hD
  have hsmall : Tendsto (fun x : ℝ ↦ Real.sqrt x / x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hplus : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 4) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa using normalized_quadratic_sqrt_atTop 1 0 4
  have hminus : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 - 4) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, zero_mul, add_zero, ← sub_eq_add_neg, Real.sqrt_one] using
      normalized_quadratic_sqrt_atTop 1 0 (-4)
  have hn : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + 4) / x + 2 + 3 * (Real.sqrt x / x))
      atTop (𝓝 (3 : ℝ)) := by
    simpa only [Pi.add_apply, mul_zero, add_zero, show (1 : ℝ) + 2 = 3 by norm_num] using
      (hplus.add_const 2).add (hsmall.const_mul 3)
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 - 4) / x + 1) atTop (𝓝 (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hminus.add_const 1
  apply (show Tendsto (fun x : ℝ ↦ (Real.sqrt (x ^ 2 + 4) / x + 2 + 3 * (Real.sqrt x / x)) /
      (Real.sqrt (x ^ 2 - 4) / x + 1)) atTop (𝓝 (3 / 2 : ℝ)) from by
        simpa only [Pi.div_apply] using! hn.div hd (by norm_num : (2 : ℝ) ≠ 0)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hnum : Real.sqrt (x ^ 2 + 4) / x + 2 + 3 * (Real.sqrt x / x) =
      (Real.sqrt (x ^ 2 + 4) + 2 * x + 3 * Real.sqrt x) / x := by
    simp only [add_div, mul_div_assoc, div_self hx.ne', mul_one]
  have hden : Real.sqrt (x ^ 2 - 4) / x + 1 = (Real.sqrt (x ^ 2 - 4) + x) / x := by
    rw [add_div, div_self hx.ne']
  rw [hnum, hden, div_div_div_cancel_right₀ hx.ne']

/-- Bài tập 3.7.13(f): 2x−√(4x²−7x+4)→7/4. -/
theorem leading_radical_difference_at_positive_infinity :
    DomainAtTopLimit leadingRadicalDifferenceDomain
      (fun x ↦ 2 * x - Real.sqrt (4 * x ^ 2 - 7 * x + 4)) (7 / 4) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hx : ∀ᶠ x : ℝ in atTop, x ≠ 0 := (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne'
  have hp := quadratic_eventually_positive atTop hi hx (by norm_num : (0 : ℝ) < 4) (-7) 4
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ leadingRadicalDifferenceDomain := by
    filter_upwards [hp] with x hp
    change 0 ≤ 4 * x ^ 2 - 7 * x + 4
    simpa only [neg_mul, ← sub_eq_add_neg] using hp.le
  apply domainAtTopLimit_of_eventually_domain hD
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x) atTop (𝓝 (2 : ℝ)) := by
    have h4 : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    simpa only [neg_mul, ← sub_eq_add_neg, h4] using normalized_quadratic_sqrt_atTop 4 (-7) 4
  have hn : Tendsto (fun x : ℝ ↦ 7 - 4 * x⁻¹) atTop (𝓝 (7 : ℝ)) := by
    simpa using (hi.const_mul 4).const_sub 7
  have hd : Tendsto (fun x : ℝ ↦ 2 + Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x) atTop (𝓝 (4 : ℝ)) := by
    simpa only [show (2 : ℝ) + 2 = 4 by norm_num] using hs.const_add 2
  apply (show Tendsto (fun x : ℝ ↦ (7 - 4 * x⁻¹) /
      (2 + Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x)) atTop (𝓝 (7 / 4 : ℝ)) from by
        simpa only [Pi.div_apply] using! hn.div hd (by norm_num : (4 : ℝ) ≠ 0)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),hD] with x hx hpoly
  have hx0 := hx.ne'
  have hs0 := Real.sqrt_nonneg (4 * x ^ 2 - 7 * x + 4)
  change 0 ≤ 4 * x ^ 2 - 7 * x + 4 at hpoly
  have hsq := Real.sq_sqrt hpoly
  have hden : 2 * x + Real.sqrt (4 * x ^ 2 - 7 * x + 4) ≠ 0 := by linarith
  have hnorm : 2 + Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x ≠ 0 := by
    have hn : 0 ≤ Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x := div_nonneg hs0 hx.le
    linarith
  have he : 2 * x - Real.sqrt (4 * x ^ 2 - 7 * x + 4) =
      (7 * x - 4) / (2 * x + Real.sqrt (4 * x ^ 2 - 7 * x + 4)) := by
    apply (eq_div_iff hden).mpr
    nlinarith
  have hnum : 7 - 4 * x⁻¹ = (7 * x - 4) / x := by
    rw [sub_div, mul_div_assoc, div_self hx0, mul_one, div_eq_mul_inv]
  have hnormeq : 2 + Real.sqrt (4 * x ^ 2 - 7 * x + 4) / x =
      (2 * x + Real.sqrt (4 * x ^ 2 - 7 * x + 4)) / x := by
    simp only [add_div, mul_div_assoc, div_self hx0, mul_one]
  rw [hnum, hnormeq, div_div_div_cancel_right₀ hx0, he]

end calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
