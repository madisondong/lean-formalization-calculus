import calculus.Chapter03.Section07ComposedQuadraticRatioExercises
import calculus.Chapter03.Section07LogarithmicRatioExercises

/-!
§3.7 — Bài tập 3.7.11(m)

Nguồn: dòng 3695.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07FractionalRootRatioExercise
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section07LogarithmicRatioExercises


def fractionalRootRatioDomain : Set ℝ :=
  {x | Real.cos x ≠ 0 ∧ 1 + Real.tan x ^ 2 ∈ nthRootDomain 3 ∧
    1 - Real.tan x ^ 2 ∈ nthRootDomain 3 ∧ x ^ 2 ∈ nthRootDomain 3 ∧
    x + realNthRoot 3 (x ^ 2) ≠ 0}


theorem realNthRoot_three_continuousAt_zero : ContinuousAt (realNthRoot 3) 0 := by
  have hzero : realNthRoot 3 (0 : ℝ) = 0 := by norm_num [realNthRoot]
  change Tendsto (realNthRoot 3) (𝓝 (0 : ℝ)) (𝓝 (realNthRoot 3 (0 : ℝ)))
  rw [hzero]
  have hp : Tendsto (fun x : ℝ ↦ |x| ^ ((3 : ℝ)⁻¹)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, abs_zero, Real.zero_rpow (by norm_num : (3 : ℝ)⁻¹ ≠ 0)] using!
      (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)).comp continuous_abs).continuousAt (x := (0 : ℝ))).tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hp.congr
  intro x
  have he := Real.pow_rpow_inv_natCast (x := |realNthRoot 3 x|) (n := 3)
    (abs_nonneg _) (by decide : (3 : ℕ) ≠ 0)
  rw [← abs_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3))] at he
  simpa only [Real.norm_eq_abs, Nat.cast_ofNat] using he


theorem identity_over_square_cubic_root_at_zero :
    Tendsto (fun x : ℝ ↦ x / realNthRoot 3 (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (realNthRoot 3) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    have hzero : realNthRoot 3 (0 : ℝ) = 0 := by norm_num [realNthRoot]
    simpa only [hzero] using!
      realNthRoot_three_continuousAt_zero.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  apply (by decide : Odd 3).pow_injective
  change realNthRoot 3 x ^ (3 : ℕ) = (x / realNthRoot 3 (x ^ 2)) ^ (3 : ℕ)
  rw [div_pow, realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    realNthRoot_pow (by decide : 1 ≤ 3) (Or.inl (by decide : Odd 3)),
    show x ^ 3 = x ^ 2 * x by ring, mul_div_cancel_left₀ x (pow_ne_zero 2 hx)]


theorem square_over_fractional_root_denominator_at_zero :
    Tendsto (fun x : ℝ ↦ x ^ 2 / (x + realNthRoot 3 (x ^ 2)))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    have hi2 : Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using! hi.pow 2
    have hzero : realNthRoot 3 (0 : ℝ) = 0 := by norm_num [realNthRoot]
    simpa only [Function.comp_def, hzero] using!
      realNthRoot_three_continuousAt_zero.tendsto.comp hi2
  have hd : Tendsto (fun x : ℝ ↦ 1 + x / realNthRoot 3 (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using! identity_over_square_cubic_root_at_zero.const_add 1
  have ht : Tendsto (fun x : ℝ ↦ realNthRoot 3 (x ^ 2) ^ 2 /
      (1 + x / realNthRoot 3 (x ^ 2)))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.div_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using!
      (hr.pow 2).div hd one_ne_zero
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne, hd.eventually_ne one_ne_zero] with x hx hdn
  have hrpow := realNthRoot_pow (by decide : 1 ≤ 3)
    (show x ^ 2 ∈ nthRootDomain 3 from Or.inl (by decide : Odd 3))
  have hrne : realNthRoot 3 (x ^ 2) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hrpow
    exact (pow_ne_zero 2 hx) hrpow.symm
  have hden : x + realNthRoot 3 (x ^ 2) ≠ 0 := by
    intro hz
    apply hdn
    have hq : x / realNthRoot 3 (x ^ 2) = -1 := by
      apply (div_eq_iff hrne).mpr
      linarith
    rw [hq, add_neg_cancel]
  apply (div_eq_div_iff hdn hden).mpr
  have he : x + realNthRoot 3 (x ^ 2) =
      (1 + x / realNthRoot 3 (x ^ 2)) * realNthRoot 3 (x ^ 2) := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hrne]
    ring
  calc
    _ = (1 + x / realNthRoot 3 (x ^ 2)) * realNthRoot 3 (x ^ 2) ^ 3 := by rw [he]; ring
    _ = _ := by rw [hrpow]; ring


theorem normalized_fractional_root_numerator_at_zero :
    Tendsto (fun x : ℝ ↦ (realNthRoot 3 (1 + Real.tan x ^ 2) -
      realNthRoot 3 (1 - Real.tan x ^ 2)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 / 3 : ℝ)) := by
  have hplus : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_add 1
  have hminus : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hp : HasDerivAt (realNthRoot 3) ((3 : ℝ)⁻¹) (1 + (0 : ℝ)) := by
    simpa only [add_zero, Nat.cast_ofNat] using realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)
  have hm : HasDerivAt (realNthRoot 3) ((3 : ℝ)⁻¹) (1 - (0 : ℝ)) := by
    simpa only [sub_zero, Nat.cast_ofNat] using realNthRoot_hasDerivAt_one (by decide : 1 ≤ 3)
  have hψ : HasDerivAt (fun t : ℝ ↦ realNthRoot 3 (1 + t) - realNthRoot 3 (1 - t)) (2 / 3) 0 := by
    simpa only [Function.comp_def, show (3 : ℝ)⁻¹ * 1 - (3 : ℝ)⁻¹ * (-1) = 2 / 3 by norm_num] using!
      (hp.comp 0 hplus).sub (hm.comp 0 hminus)
  have ht : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using!
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ Real.tan x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using! ht.pow 2
  have hn : Tendsto (fun x : ℝ ↦ Real.tan x ^ 2 / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [div_pow, one_pow] using! tangent_equivalent_identity_zero.2.2.pow 2
  simpa only [mul_one] using! normalized_composition_increment 2 hψ
    (by simp only [add_zero, sub_zero, sub_self]) hu hn one_ne_zero

/-- Bài tập 3.7.11(m): giới hạn hai phía bằng 0. -/
theorem fractional_root_ratio_at_zero :
    DomainLimit fractionalRootRatioDomain
      (fun x ↦ (realNthRoot 3 (1 + Real.tan x ^ 2) - realNthRoot 3 (1 - Real.tan x ^ 2)) /
        (x + realNthRoot 3 (x ^ 2))) 0 0 := by
  have hd : Tendsto (fun x : ℝ ↦ 1 + x / realNthRoot 3 (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using! identity_over_square_cubic_root_at_zero.const_add 1
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ fractionalRootRatioDomain := by
    filter_upwards [tangent_eventually_defined_zero, punctured_zero_eventually_ne,
      hd.eventually_ne one_ne_zero] with x hc hx hdn
    have hrpow := realNthRoot_pow (by decide : 1 ≤ 3)
      (show x ^ 2 ∈ nthRootDomain 3 from Or.inl (by decide : Odd 3))
    have hrne : realNthRoot 3 (x ^ 2) ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hrpow
      exact (pow_ne_zero 2 hx) hrpow.symm
    have hden : x + realNthRoot 3 (x ^ 2) ≠ 0 := by
      intro hz
      apply hdn
      have hq : x / realNthRoot 3 (x ^ 2) = -1 := by
        apply (div_eq_iff hrne).mpr
        linarith
      rw [hq, add_neg_cancel]
    exact ⟨hc, Or.inl (by decide : Odd 3), Or.inl (by decide : Odd 3), Or.inl (by decide : Odd 3), hden⟩
  apply domainLimit_of_eventually_domain hD
  have ht : Tendsto (fun x : ℝ ↦ ((realNthRoot 3 (1 + Real.tan x ^ 2) -
      realNthRoot 3 (1 - Real.tan x ^ 2)) / x ^ 2) * (x ^ 2 / (x + realNthRoot 3 (x ^ 2))))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, mul_zero] using!
      normalized_fractional_root_numerator_at_zero.mul square_over_fractional_root_denominator_at_zero
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_mul_div_cancel₀ (pow_ne_zero 2 hx)

end calculus.Chapter03.Section07FractionalRootRatioExercise
