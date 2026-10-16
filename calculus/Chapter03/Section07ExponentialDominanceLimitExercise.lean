import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
§3.7 — Bài tập 3.7.14(a)

Nguồn: dòng 3749.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07ExponentialDominanceLimitExercise
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section07QuadraticRadicalInfinityExercises


def exponentialDominanceDomain : Set ℝ :=
  {x | 0 < x + 1 ∧ (3 : ℝ) ^ x - 4 * x ^ 6 + 5 * (4 : ℝ) ^ x ≠ 0}


theorem polynomial_over_four_power_atTop_zero (k : ℕ) :
    Tendsto (fun x : ℝ ↦ x ^ k / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
  have hp : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)] using!
    (isLittleO_pow_exp_pos_mul_atTop k hp).tendsto_div_nhds_zero


theorem shifted_log_thirtieth_over_four_power_atTop_zero :
    Tendsto (fun x : ℝ ↦ Real.log (x + 1) ^ 30 / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_id
  have hl : Tendsto (fun x : ℝ ↦ Real.log (x + 1) ^ 30 / (x + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, one_mul, add_zero] using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 30 one_ne_zero).comp ht
  have hp : Tendsto (fun x : ℝ ↦ (x + 1) / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
    have hs : Tendsto (fun x : ℝ ↦ x / (4 : ℝ) ^ x + 1 / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Pi.add_apply, pow_one, pow_zero, zero_add] using!
        (polynomial_over_four_power_atTop_zero 1).add (polynomial_over_four_power_atTop_zero 0)
    apply hs.congr
    intro x
    rw [← add_div]
  have hprod : Tendsto (fun x : ℝ ↦ (Real.log (x + 1) ^ 30 / (x + 1)) * ((x + 1) / (4 : ℝ) ^ x))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.mul_apply, zero_mul] using! hl.mul hp
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact div_mul_div_cancel₀ (by linarith : x + 1 ≠ 0)

/-- Bài tập 3.7.14(a): giới hạn tại +∞ bằng 1/5. -/
theorem exponential_dominance_ratio_at_infinity :
    DomainAtTopLimit exponentialDominanceDomain
      (fun x ↦ (x ^ 2 + Real.log (x + 1) ^ 30 - (2 : ℝ) ^ x + (4 : ℝ) ^ x) /
        ((3 : ℝ) ^ x - 4 * x ^ 6 + 5 * (4 : ℝ) ^ x)) (1 / 5) := by
  have htwo : Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ x / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 4)] using!
      tendsto_rpow_atTop_of_base_lt_one ((2 : ℝ) / 4) (by norm_num) (by norm_num)
  have hthree : Tendsto (fun x : ℝ ↦ (3 : ℝ) ^ x / (4 : ℝ) ^ x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 4)] using!
      tendsto_rpow_atTop_of_base_lt_one ((3 : ℝ) / 4) (by norm_num) (by norm_num)
  have hn : Tendsto (fun x : ℝ ↦ (x ^ 2 + Real.log (x + 1) ^ 30 - (2 : ℝ) ^ x + (4 : ℝ) ^ x) /
      (4 : ℝ) ^ x) atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ x ^ 2 / (4 : ℝ) ^ x + Real.log (x + 1) ^ 30 / (4 : ℝ) ^ x -
        (2 : ℝ) ^ x / (4 : ℝ) ^ x + 1) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Pi.add_apply, Pi.sub_apply, zero_add, sub_zero] using!
        (((polynomial_over_four_power_atTop_zero 2).add shifted_log_thirtieth_over_four_power_atTop_zero).sub htwo).add_const 1
    apply ht.congr
    intro x
    have hp : (4 : ℝ) ^ x ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) x).ne'
    rw [add_div, sub_div, add_div, div_self hp]
  have hd : Tendsto (fun x : ℝ ↦ ((3 : ℝ) ^ x - 4 * x ^ 6 + 5 * (4 : ℝ) ^ x) / (4 : ℝ) ^ x)
      atTop (𝓝 (5 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ (3 : ℝ) ^ x / (4 : ℝ) ^ x - 4 * (x ^ 6 / (4 : ℝ) ^ x) + 5)
        atTop (𝓝 (5 : ℝ)) := by
      simpa only [Pi.sub_apply, mul_zero, sub_zero, zero_add] using!
        (hthree.sub ((polynomial_over_four_power_atTop_zero 6).const_mul 4)).add_const 5
    apply ht.congr
    intro x
    have hp : (4 : ℝ) ^ x ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) x).ne'
    rw [add_div, sub_div, mul_div_assoc, mul_div_assoc, div_self hp, mul_one]
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ exponentialDominanceDomain := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne (by norm_num : (5 : ℝ) ≠ 0)] with x hx hdne
    exact ⟨by linarith, (div_ne_zero_iff.mp hdne).1⟩
  apply domainAtTopLimit_of_eventually_domain hD
  have hq : Tendsto (fun x : ℝ ↦
      ((x ^ 2 + Real.log (x + 1) ^ 30 - (2 : ℝ) ^ x + (4 : ℝ) ^ x) / (4 : ℝ) ^ x) /
        (((3 : ℝ) ^ x - 4 * x ^ 6 + 5 * (4 : ℝ) ^ x) / (4 : ℝ) ^ x)) atTop (𝓝 (1 / 5 : ℝ)) := by
    simpa only [Pi.div_apply] using! hn.div hd (by norm_num : (5 : ℝ) ≠ 0)
  apply hq.congr
  intro x
  exact div_div_div_cancel_right₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) x).ne' _ _

end calculus.Chapter03.Section07ExponentialDominanceLimitExercise
