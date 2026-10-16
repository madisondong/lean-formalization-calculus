import calculus.Chapter04.Section04TaylorLimitCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# §4.4 Bài 4: mười hai giới hạn trên miền tự nhiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1700–1718.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04TaylorLimitExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02Infinite
open calculus.Chapter04.Section04TaylorLimitCoefficients

def powerQuotientDomain : Set ℝ := {x | x ≠ 0}
def cotangentCancellationDomain : Set ℝ := {x | x ≠ 0 ∧ Real.sin x ≠ 0}
def logarithmQuotientDomain : Set ℝ := {x | x ≠ 0 ∧ 0 < 1 + x}
def tangentQuotientDomain : Set ℝ := {x | x ≠ 0 ∧ Real.cos x ≠ 0}
def inverseTrigonometricQuotientDomain : Set ℝ := {x | x ≠ 0 ∧ -1 ≤ x ∧ x ≤ 1}
def tangentSineResidualRatioDomain : Set ℝ :=
  {x | Real.cos x ≠ 0 ∧ Real.sin x - x + x ^ 3 / 6 ≠ 0}
def squaredLogSineRatioDomain : Set ℝ :=
  {x | 0 < 1 + x ∧ 1 - Real.exp (-(x ^ 2)) ≠ 0}
def exponentialSineResidualRatioDomain : Set ℝ := {x | x - Real.sin x ≠ 0}
def infiniteLogarithmCancellationDomain : Set ℝ := {x | x ≠ 0 ∧ 0 < 1 + 1 / x}
def sixthRootDifferenceDomain : Set ℝ := {x | 0 ≤ x ^ 6 + x ^ 5 ∧ 0 ≤ x ^ 6 - x ^ 5}

theorem source_cotangent_first_cancellation_limit :
    DomainLimit cotangentCancellationDomain
      (fun x : ℝ ↦ (1 / x) * (1 / x - Real.cot x)) 0 (1 / 3) := by
  apply source_limit_of_eventual_natural_domain _ cotangent_first_cancellation_tendsto
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.1⟩

theorem source_logarithm_quadratic_limit :
    DomainLimit logarithmQuotientDomain
      (fun x : ℝ ↦ (Real.log (1 + x) - x) / x ^ 2) 0 (-1 / 2) := by
  apply source_limit_of_eventual_natural_domain _ logarithm_quadratic_quotient_tendsto
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.2.2.1⟩

theorem source_cosine_fourth_limit :
    DomainLimit powerQuotientDomain
      (fun x : ℝ ↦ (Real.cos x - 1 + x ^ 2 / 2) / x ^ 4) 0 (1 / 24) := by
  apply source_limit_of_eventual_natural_domain _ cosine_fourth_quotient_tendsto
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa [powerQuotientDomain] using hx

theorem source_tangent_sub_sine_cubic_limit :
    DomainLimit tangentQuotientDomain
      (fun x : ℝ ↦ (Real.tan x - Real.sin x) / x ^ 3) 0 (1 / 2) := by
  apply source_limit_of_eventual_natural_domain _ tangent_sub_sine_cubic_quotient_tendsto
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.2.1⟩

theorem source_arctangent_sub_arcsine_cubic_limit :
    DomainLimit inverseTrigonometricQuotientDomain
      (fun x : ℝ ↦ (Real.arctan x - Real.arcsin x) / x ^ 3) 0 (-1 / 2) := by
  have ht := arctangent_cubic_quotient_tendsto.sub arcsine_cubic_quotient_tendsto
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ (Real.arctan x - Real.arcsin x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
    norm_num
    apply ht.congr'
    filter_upwards with x
    ring
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.2.2.2.1.le, hx.2.2.2.2.2.le⟩

theorem source_tangent_sine_fifth_residual_ratio_limit :
    DomainLimit tangentSineResidualRatioDomain
      (fun x : ℝ ↦ (Real.tan x - x - x ^ 3 / 3) /
        (Real.sin x - x + x ^ 3 / 6)) 0 16 := by
  have ht := tangent_fifth_quotient_tendsto.div sine_fifth_quotient_tendsto
    (by norm_num : (1 / 120 : ℝ) ≠ 0)
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ (Real.tan x - x - x ^ 3 / 3) /
      (Real.sin x - x + x ^ 3 / 6)) (𝓝[≠] (0 : ℝ)) (𝓝 16) := by
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually, sine_fifth_residual_eventually_ne]
      with x hx hs
    dsimp only [Pi.div_apply]
    field_simp [hx.1, hs]
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [basic_natural_domains_eventually, sine_fifth_residual_eventually_ne]
    with x hx hs
  exact ⟨hx.2.2.1, hs⟩

theorem source_squared_logarithm_sub_sine_ratio_limit :
    DomainLimit squaredLogSineRatioDomain
      (fun x : ℝ ↦ (Real.log (1 + x) ^ 2 - Real.sin x ^ 2) /
        (1 - Real.exp (-(x ^ 2)))) 0 0 := by
  have hden : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 1 - Real.exp (-(x ^ 2)) ≠ 0 := by
    filter_upwards [exponential_square_denominator_tendsto.eventually_ne
      (by norm_num : (1 : ℝ) ≠ 0)] with x hx
    intro he
    exact hx (by simp only [he, zero_div])
  have ht := ((logarithm_linear_quotient_tendsto.pow 2).sub
    (sine_linear_quotient_tendsto.pow 2)).div exponential_square_denominator_tendsto
      (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ (Real.log (1 + x) ^ 2 - Real.sin x ^ 2) /
      (1 - Real.exp (-(x ^ 2)))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually, hden] with x hx he
    dsimp only [Pi.div_apply]
    field_simp [hx.1, he]
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [basic_natural_domains_eventually, hden] with x hx he
  exact ⟨hx.2.2.2.1, he⟩

theorem source_exponential_sine_cubic_residual_ratio_limit :
    DomainLimit exponentialSineResidualRatioDomain
      (fun x : ℝ ↦ (Real.exp x - 1 - x - x ^ 2 / 2) / (x - Real.sin x)) 0 1 := by
  have ht := exponential_cubic_quotient_tendsto.div sine_cubic_quotient_tendsto.neg
    (by norm_num : -(-1 / 6 : ℝ) ≠ 0)
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ (Real.exp x - 1 - x - x ^ 2 / 2) /
      (x - Real.sin x)) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually, sine_minus_identity_cubic_eventually_ne]
      with x hx hs
    have hneg : x - Real.sin x ≠ 0 := by exact sub_ne_zero.mpr (sub_ne_zero.mp hs).symm
    dsimp only [Pi.div_apply]
    field_simp [hx.1, hs, hneg]
    ring
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [sine_minus_identity_cubic_eventually_ne] with x hs
  exact sub_ne_zero.mpr (sub_ne_zero.mp hs).symm

theorem source_tangent_sine_fifth_cancellation_limit :
    DomainLimit tangentQuotientDomain
      (fun x : ℝ ↦ (2 * (Real.tan x - Real.sin x) - x ^ 3) / x ^ 5) 0 (1 / 4) := by
  have ht := (tangent_fifth_quotient_tendsto.sub sine_fifth_quotient_tendsto).const_mul 2
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ (2 * (Real.tan x - Real.sin x) - x ^ 3) / x ^ 5)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 4 : ℝ)) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp [hx0]
    ring
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.2.1⟩

theorem source_infinite_logarithm_cancellation_limit :
    DomainAtTopLimit infiniteLogarithmCancellationDomain
      (fun x : ℝ ↦ x - x ^ 2 * Real.log (1 + 1 / x)) (1 / 2) := by
  have harg : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝[≠] (0 : ℝ)) := by
    simpa only [one_div] using
      tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE (0 : ℝ))
  have ht := logarithm_quadratic_quotient_tendsto.neg.comp harg
  norm_num only [neg_div, neg_neg] at ht
  have hlim : Tendsto (fun x : ℝ ↦ x - x ^ 2 * Real.log (1 + 1 / x))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    dsimp only [Function.comp_def]
    field_simp [hx0]
    ring
  apply source_at_top_limit_of_eventual_natural_domain _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact ⟨by linarith, by positivity⟩

theorem source_cotangent_squared_cancellation_limit :
    DomainLimit cotangentCancellationDomain
      (fun x : ℝ ↦ 1 / x ^ 2 - Real.cot x ^ 2) 0 (2 / 3) := by
  have hlinear : Tendsto (fun x : ℝ ↦ x * Real.cot x)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have ht := cosine_tendsto_one.div sine_linear_quotient_tendsto
      (by norm_num : (1 : ℝ) ≠ 0)
    norm_num only [div_one] at ht
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually] with x hx
    dsimp only [Pi.div_apply]
    rw [Real.cot_eq_cos_div_sin]
    field_simp [hx.1, hx.2.1]
  have ht := cotangent_first_cancellation_tendsto.mul (hlinear.const_add 1)
  norm_num at ht
  have hlim : Tendsto (fun x : ℝ ↦ 1 / x ^ 2 - Real.cot x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 / 3 : ℝ)) := by
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually] with x hx
    field_simp [hx.1]
    ring
  apply source_limit_of_eventual_natural_domain _ hlim
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.1⟩

theorem source_sixth_root_difference_limit :
    DomainAtTopLimit sixthRootDifferenceDomain
      (fun x : ℝ ↦ (x ^ 6 + x ^ 5) ^ (1 / 6 : ℝ) -
        (x ^ 6 - x ^ 5) ^ (1 / 6 : ℝ)) (1 / 3) := by
  have harg : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝[≠] (0 : ℝ)) := by
    simpa only [one_div] using
      tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE (0 : ℝ))
  have ht := sixth_root_affine_difference_taylor_tendsto.comp harg
  have hfactor : ∀ x : ℝ, 1 < x →
      (x ^ 6 + x ^ 5) ^ (1 / 6 : ℝ) - (x ^ 6 - x ^ 5) ^ (1 / 6 : ℝ) =
        ((1 + 1 / x) ^ (1 / 6 : ℝ) - (1 - 1 / x) ^ (1 / 6 : ℝ)) / (1 / x) := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x < 1 := (div_lt_one hxpos).mpr hx
    have hp : 0 ≤ 1 + 1 / x := by positivity
    have hm : 0 ≤ 1 - 1 / x := by linarith
    have hplus : x ^ 6 + x ^ 5 = x ^ 6 * (1 + 1 / x) := by
      field_simp [hx0]
    have hminus : x ^ 6 - x ^ 5 = x ^ 6 * (1 - 1 / x) := by
      field_simp [hx0]
    have hroot : (x ^ 6) ^ (1 / 6 : ℝ) = x := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast hxpos.le (by decide : (6 : ℕ) ≠ 0)
    rw [hplus, hminus, Real.mul_rpow (pow_nonneg hxpos.le 6) hp,
      Real.mul_rpow (pow_nonneg hxpos.le 6) hm, hroot]
    field_simp [hx0]
  have hlim : Tendsto (fun x : ℝ ↦ (x ^ 6 + x ^ 5) ^ (1 / 6 : ℝ) -
      (x ^ 6 - x ^ 5) ^ (1 / 6 : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hfactor x hx).symm
  apply source_at_top_limit_of_eventual_natural_domain _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 ≤ x := by linarith
  constructor
  · exact add_nonneg (pow_nonneg hxpos 6) (pow_nonneg hxpos 5)
  · have heq : x ^ 6 - x ^ 5 = x ^ 5 * (x - 1) := by ring
    rw [heq]
    exact mul_nonneg (pow_nonneg hxpos 5) (by linarith)

end calculus.Chapter04.Section04TaylorLimitExercises
