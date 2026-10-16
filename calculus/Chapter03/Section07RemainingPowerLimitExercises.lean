import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
import calculus.Chapter03.Section06VariablePowerLimitExercises
import calculus.Chapter03.Section07Fundamental

/-!
§3.7 — Bài tập 3.7.12(c,d,e)

Nguồn: dòng 3714–3716.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07RemainingPowerLimitExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section06SourceIssues calculus.Chapter03.Section06VariablePowerLimitExercises
open calculus.Chapter03.Section07Fundamental calculus.Chapter03.Section07
open calculus.Chapter03.Section07QuadraticRadicalInfinityExercises


def growingQuadraticPowerDomain : Set ℝ :=
  {x | 2 * x ^ 2 - 1 ≠ 0 ∧
    (2 * x ^ 2 + 3) / (2 * x ^ 2 - 1) ∈ realPowerDomain (x ^ 2)}


def logarithmicCotangentPowerDomain : Set ℝ :=
  {x | 0 < Real.exp 1 + x ∧
    Real.log (Real.exp 1 + x) ∈ realPowerDomain (Real.cot x) ∧ Real.sin x ≠ 0}


def exponentialSixthRootDomain : Set ℝ :=
  {x | 2 - x ^ 2 ∈ nthRootDomain 6 ∧ 1 - realNthRoot 6 (2 - x ^ 2) ≠ 0 ∧
    (2 : ℝ) ∈ realPowerDomain x}


theorem quadratic_ratio_log_product_atTop :
    Tendsto (fun x : ℝ ↦ x ^ 2 * Real.log ((2 * x ^ 2 + 3) / (2 * x ^ 2 - 1)))
      atTop (𝓝 (2 : ℝ)) := by
  have hp : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  have hd : Tendsto (fun x : ℝ ↦ 2 * x ^ 2 - 1) atTop atTop := by
    simpa only [← sub_eq_add_neg] using!
      tendsto_atTop_add_const_right _ (-1 : ℝ)
        (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hp)
  have hu : Tendsto (fun x : ℝ ↦ 4 / (2 * x ^ 2 - 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using! hd.inv_tendsto_atTop.const_mul 4
  have htail : ∀ᶠ x : ℝ in atTop, 0 < 2 * x ^ 2 - 1 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    nlinarith [sq_nonneg (x - 1)]
  have hune : ∀ᶠ x : ℝ in atTop, 4 / (2 * x ^ 2 - 1) ≠ 0 :=
    htail.mono fun _ hx ↦ div_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hx.ne'
  have hup : Tendsto (fun x : ℝ ↦ 4 / (2 * x ^ 2 - 1)) atTop
      (domainApproachFilter univ (.point 0)) := by
    change Tendsto (fun x : ℝ ↦ 4 / (2 * x ^ 2 - 1)) atTop (𝓝[univ \ {0}] 0)
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu, ?_⟩
    filter_upwards [hune] with x hx
    exact ⟨mem_univ _, by simpa using hx⟩
  have hs : Tendsto (fun x : ℝ ↦ Real.log (1 + 4 / (2 * x ^ 2 - 1)) /
      (4 / (2 * x ^ 2 - 1))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def] using!
      logarithm_one_add_equivalent_identity_zero.2.2.comp hup
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ ↦ (4 / (2 * x ^ 2 - 1)) * x ^ 2)
      atTop (𝓝 (2 : ℝ)) := by
    have hn0 : Tendsto (fun x : ℝ ↦ 2 - x⁻¹ ^ 2) atTop (𝓝 (2 : ℝ)) := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using! (hi.pow 2).const_sub 2
    have hq : Tendsto (fun x : ℝ ↦ 4 / (2 - x⁻¹ ^ 2)) atTop (𝓝 (2 : ℝ)) := by
      simpa only [Pi.div_apply, show (4 : ℝ) / 2 = 2 by norm_num] using!
        (tendsto_const_nhds (x := (4 : ℝ))).div hn0 (by norm_num : (2 : ℝ) ≠ 0)
    apply hq.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hnorm : 2 - x⁻¹ ^ 2 = (2 * x ^ 2 - 1) / x ^ 2 := by
      rw [sub_div, mul_div_assoc, div_self (pow_ne_zero 2 hx0), mul_one, one_div, inv_pow]
    rw [hnorm, div_div_eq_mul_div]
    ring
  have ht : Tendsto (fun x : ℝ ↦ (Real.log (1 + 4 / (2 * x ^ 2 - 1)) /
      (4 / (2 * x ^ 2 - 1))) * ((4 / (2 * x ^ 2 - 1)) * x ^ 2))
      atTop (𝓝 (2 : ℝ)) := by
    simpa only [Pi.mul_apply, one_mul] using! hs.mul hn
  apply ht.congr'
  filter_upwards [htail] with x hx
  have huneq : 4 / (2 * x ^ 2 - 1) ≠ 0 := div_ne_zero (by norm_num) hx.ne'
  have hb : (2 * x ^ 2 + 3) / (2 * x ^ 2 - 1) = 1 + 4 / (2 * x ^ 2 - 1) := by
    calc
      _ = ((2 * x ^ 2 - 1) + 4) / (2 * x ^ 2 - 1) := by congr 1; ring
      _ = _ := by rw [add_div, div_self hx.ne']
  rw [hb]
  calc
    _ = ((Real.log (1 + 4 / (2 * x ^ 2 - 1)) / (4 / (2 * x ^ 2 - 1))) *
        (4 / (2 * x ^ 2 - 1))) * x ^ 2 := by ring
    _ = Real.log (1 + 4 / (2 * x ^ 2 - 1)) * x ^ 2 := by rw [div_mul_cancel₀ _ huneq]
    _ = _ := mul_comm _ _

/-- Bài tập 3.7.12(c): giới hạn tại +∞ bằng exp 2. -/
theorem growing_quadratic_variable_power_at_infinity :
    DomainAtTopLimit growingQuadraticPowerDomain
      (fun x ↦ ((2 * x ^ 2 + 3) / (2 * x ^ 2 - 1)) ^ (x ^ 2)) (Real.exp 2) := by
  have htail : ∀ᶠ x : ℝ in atTop,
      0 < 2 * x ^ 2 - 1 ∧ 0 < (2 * x ^ 2 + 3) / (2 * x ^ 2 - 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hd : 0 < 2 * x ^ 2 - 1 := by nlinarith [sq_nonneg (x - 1)]
    exact ⟨hd, div_pos (by nlinarith [sq_nonneg x]) hd⟩
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ growingQuadraticPowerDomain :=
    htail.mono fun _ hx ↦ ⟨hx.1.ne', positive_base_mem_variable_power_domain hx.2⟩
  exact domainAtTopLimit_of_eventually_domain hD
    (power_limit_of_log_product (htail.mono fun _ hx ↦ hx.2) quadratic_ratio_log_product_atTop)

/-- Bài tập 3.7.12(d): giới hạn bằng exp(1/e). -/
theorem logarithmic_cotangent_variable_power_at_zero :
    DomainLimit logarithmicCotangentPowerDomain
      (fun x ↦ Real.log (Real.exp 1 + x) ^ Real.cot x) 0 (Real.exp (1 / Real.exp 1)) := by
  have ha : HasDerivAt (fun x : ℝ ↦ Real.exp 1 + x) 1 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_add (Real.exp 1)
  have hb : HasDerivAt (fun x : ℝ ↦ Real.log (Real.exp 1 + x)) (1 / Real.exp 1) 0 := by
    simpa only [add_zero] using! ha.log (by simpa only [add_zero] using Real.exp_ne_zero (1 : ℝ))
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (Real.log (Real.exp 1 + x))) (1 / Real.exp 1) 0 := by
    simpa only [add_zero, Real.log_exp, div_one] using!
      hb.log (by norm_num only [add_zero, Real.log_exp])
  have hg : HasDerivAt Real.sin 1 0 := by simpa only [Real.cos_zero] using Real.hasDerivAt_sin (0 : ℝ)
  have hE : {x : ℝ | 0 < Real.exp 1 + x ∧ 0 < Real.log (Real.exp 1 + x)} ∈ 𝓝 (0 : ℝ) := by
    have hp : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), 0 < Real.exp 1 + x :=
      ha.continuousAt.tendsto.eventually (Ioi_mem_nhds (by simpa only [add_zero] using Real.exp_pos (1 : ℝ)))
    have hq : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), 0 < Real.log (Real.exp 1 + x) :=
      hb.continuousAt.tendsto.eventually (Ioi_mem_nhds (by simp only [add_zero, Real.log_exp]; norm_num))
    exact hp.and hq
  have hacc : AccumulationPointOf logarithmicCotangentPowerDomain 0 := by
    have hsin := derivative_quotient_domain_accumulation hg Real.sin_zero one_ne_zero
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds hsin hE)
    intro x hx
    exact ⟨hx.2.1, positive_base_mem_variable_power_domain hx.2.2, hx.1⟩
  have hr : DomainLimit logarithmicCotangentPowerDomain
      (fun x ↦ Real.log (Real.log (Real.exp 1 + x)) / Real.sin x) 0 (1 / Real.exp 1) := by
    simpa only [div_one] using! ratio_of_derivative_slopes hacc hf hg
      (by simp only [add_zero, Real.log_exp, Real.log_one]) Real.sin_zero one_ne_zero
  have hrat := (domainLimit_iff_tendsto hacc).mp hr
  have hc : Tendsto Real.cos (𝓝[logarithmicCotangentPowerDomain \ {0}] 0) (𝓝 (1 : ℝ)) := by
    simpa only [Real.cos_zero] using!
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun x : ℝ ↦ Real.cot x * Real.log (Real.log (Real.exp 1 + x)))
      (𝓝[logarithmicCotangentPowerDomain \ {0}] 0) (𝓝 (1 / Real.exp 1)) := by
    have hm : Tendsto (fun x : ℝ ↦ (Real.log (Real.log (Real.exp 1 + x)) / Real.sin x) * Real.cos x)
        (𝓝[logarithmicCotangentPowerDomain \ {0}] 0) (𝓝 (1 / Real.exp 1)) := by
      simpa only [Pi.mul_apply, mul_one] using! hrat.mul hc
    apply hm.congr
    intro x
    rw [Real.cot_eq_cos_div_sin]
    ring
  have hpos : ∀ᶠ x in 𝓝[logarithmicCotangentPowerDomain \ {0}] 0,
      0 < Real.log (Real.exp 1 + x) :=
    ((show ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
      0 < Real.exp 1 + x ∧ 0 < Real.log (Real.exp 1 + x) from hE).filter_mono
        nhdsWithin_le_nhds).mono (fun _ hx ↦ hx.2)
  exact (domainLimit_iff_tendsto hacc).mpr (power_limit_of_log_product hpos hprod)

/-- Bài tập 3.7.12(e): giới hạn tại 1 bằng 6 log 2. -/
theorem exponential_sixth_root_ratio_at_one :
    DomainLimit exponentialSixthRootDomain
      (fun x ↦ ((2 : ℝ) ^ x - 2) / (1 - realNthRoot 6 (2 - x ^ 2))) 1 (6 * Real.log 2) := by
  have hu : HasDerivAt (fun x : ℝ ↦ 2 - x ^ 2) (-2) 1 := by
    simpa using! ((hasDerivAt_id (1 : ℝ)).pow 2).const_sub 2
  have ho : HasDerivAt (realNthRoot 6) ((6 : ℝ)⁻¹) (2 - (1 : ℝ) ^ 2) := by
    simpa only [show (2 : ℝ) - 1 ^ 2 = 1 by norm_num, Nat.cast_ofNat] using
      realNthRoot_hasDerivAt_one (by decide : 1 ≤ 6)
  have hcoef : -((6 : ℝ)⁻¹ * (-2)) = 1 / 3 := by norm_num
  have hg : HasDerivAt (fun x : ℝ ↦ 1 - realNthRoot 6 (2 - x ^ 2)) (1 / 3) 1 := by
    simpa only [Function.comp_def, hcoef] using! (ho.comp 1 hu).const_sub 1
  have hpower : HasDerivAt (fun x : ℝ ↦ (2 : ℝ) ^ x) (Real.log 2 * 1 * (2 : ℝ) ^ (1 : ℝ)) 1 := by
    simpa only [id_eq] using! (hasDerivAt_id (1 : ℝ)).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hpowcoef : Real.log 2 * 1 * (2 : ℝ) ^ (1 : ℝ) = 2 * Real.log 2 := by
    rw [Real.rpow_one]
    ring
  have hf : HasDerivAt (fun x : ℝ ↦ (2 : ℝ) ^ x - 2) (2 * Real.log 2) 1 := by
    simpa only [hpowcoef] using! hpower.sub_const 2
  have hg0 : (1 - realNthRoot 6 (2 - (1 : ℝ) ^ 2)) = 0 := by
    norm_num [realNthRoot_one]
  have hE : {x : ℝ | 0 < 2 - x ^ 2} ∈ 𝓝 (1 : ℝ) :=
    (isOpen_lt continuous_const (continuous_const.sub (continuous_id.pow 2))).mem_nhds (by norm_num)
  have hacc : AccumulationPointOf exponentialSixthRootDomain 1 := by
    have hden := derivative_quotient_domain_accumulation hg hg0 (by norm_num : (1 / 3 : ℝ) ≠ 0)
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds hden hE)
    intro x hx
    exact ⟨Or.inr hx.2.le, hx.1, positive_base_mem_variable_power_domain (by norm_num : (0 : ℝ) < 2)⟩
  have hr := ratio_of_derivative_slopes hacc hf hg
    (by norm_num) hg0 (by norm_num : (1 / 3 : ℝ) ≠ 0)
  have hvalue : (2 * Real.log 2) / (1 / 3 : ℝ) = 6 * Real.log 2 := by ring
  simpa only [hvalue] using hr

end calculus.Chapter03.Section07RemainingPowerLimitExercises
