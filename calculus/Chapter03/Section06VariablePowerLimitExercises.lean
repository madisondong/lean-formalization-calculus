import calculus.Chapter03.Section03Exercises
import calculus.Chapter03.Section06SourceIssues
import calculus.Chapter03.Section01Powers
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# §3.6 — giới hạn lũy thừa trong Bài tập 3.6.8

Nguồn: `Ch3_gioihanhamso.tex`, dòng 3178–3186; câu (a,b,c) tại dòng 3181–3183.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace calculus.Chapter03.Section06VariablePowerLimitExercises

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section06SourceIssues calculus.Chapter03.Section01Powers


theorem positive_base_mem_variable_power_domain {x α : ℝ} (hx : 0 < x) :
    x ∈ realPowerDomain α := by
  classical
  unfold realPowerDomain
  split_ifs <;> first | exact mem_univ x | exact hx.ne' | exact hx


def cotangentPowerDomain : Set ℝ :=
  {x | 1 + x ∈ realPowerDomain (Real.cot x) ∧ Real.sin x ≠ 0}


def phaseTangentPowerDomain : Set ℝ :=
  {x | 2 - x ∈ realPowerDomain (Real.tan (Real.pi * x / 2)) ∧
    Real.cos (Real.pi * x / 2) ≠ 0}


def quadraticRatioPowerDomain : Set ℝ :=
  {x | (x ^ 2 - 1) / (x ^ 2 + 1) ∈ realPowerDomain ((x - 1) / (x + 1)) ∧
    x + 1 ≠ 0}


theorem cotangent_power_domain_accumulation : AccumulationPointOf cotangentPowerDomain 0 := by
  have hs : HasDerivAt Real.sin 1 0 := by
    simpa using Real.hasDerivAt_sin (0 : ℝ)
  have ha := derivative_quotient_domain_accumulation hs (by simp) (by norm_num)
  have hpos : {x : ℝ | 0 < 1 + x} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds (by norm_num)
  apply accumulationPointOf_mono (accumulationPointOf_inter_nhds ha hpos)
  intro x hx
  exact ⟨positive_base_mem_variable_power_domain hx.2, hx.1⟩


theorem phase_tangent_power_domain_accumulation :
    AccumulationPointOf phaseTangentPowerDomain 1 := by
  have hp : HasDerivAt (fun x : ℝ ↦ Real.pi * x / 2) (Real.pi / 2) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_mul Real.pi).div_const 2
  have hg : HasDerivAt (fun x : ℝ ↦ Real.cos (Real.pi * x / 2)) (-(Real.pi / 2)) 1 := by
    simpa using hp.cos
  have hn : -(Real.pi / 2) ≠ 0 := neg_ne_zero.mpr
    (div_ne_zero Real.pi_ne_zero (by norm_num))
  have ha := derivative_quotient_domain_accumulation hg (by simp) hn
  have hpos : {x : ℝ | 0 < 2 - x} ∈ 𝓝 (1 : ℝ) :=
    (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds (by norm_num)
  apply accumulationPointOf_mono (accumulationPointOf_inter_nhds ha hpos)
  intro x hx
  exact ⟨positive_base_mem_variable_power_domain hx.2, hx.1⟩


theorem quadratic_ratio_power_domain_unbounded : ¬ BddAbove quadraticRatioPowerDomain := by
  rintro ⟨M, hM⟩
  have hlarge : (2 : ℝ) ≤ max 2 (M + 1) := le_max_left _ _
  have hbound : M + 1 ≤ max 2 (M + 1) := le_max_right _ _
  have hx : max 2 (M + 1) ∈ quadraticRatioPowerDomain := by
    have hp : 0 < ((max 2 (M + 1)) ^ 2 - 1) / ((max 2 (M + 1)) ^ 2 + 1) := by
      apply div_pos
      · nlinarith
      · nlinarith [sq_nonneg (max 2 (M + 1))]
    exact ⟨positive_base_mem_variable_power_domain hp, by linarith⟩
  have hh := hM hx
  linarith

/-- Bài tập 3.6.8(a): (1+x)^(cot x)→e trên miền tự nhiên khi x→0. -/
theorem one_add_cotangent_power_limit :
    DomainLimit cotangentPowerDomain (fun x ↦ (1 + x) ^ Real.cot x) 0 (Real.exp 1) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hg : HasDerivAt Real.sin 1 0 := by
    simpa using Real.hasDerivAt_sin (0 : ℝ)
  have hr : DomainLimit cotangentPowerDomain (fun x ↦ Real.log (1 + x) / Real.sin x) 0 1 := by
    simpa using ratio_of_derivative_slopes cotangent_power_domain_accumulation hf hg
      (by norm_num) (by simp) (by norm_num)
  have ht := (domainLimit_iff_tendsto cotangent_power_domain_accumulation).mp hr
  have hc : Tendsto Real.cos (𝓝[cotangentPowerDomain \ {0}] 0) (𝓝 (1 : ℝ)) := by
    simpa only [Real.cos_zero] using (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds
  have hprod : Tendsto (fun x ↦ Real.cot x * Real.log (1 + x))
      (𝓝[cotangentPowerDomain \ {0}] 0) (𝓝 (1 : ℝ)) := by
    have hm := ht.mul hc
    simp only [one_mul] at hm
    apply hm.congr
    intro x
    rw [Real.cot_eq_cos_div_sin]
    ring
  apply (domainLimit_iff_tendsto cotangent_power_domain_accumulation).mpr
  have hpos : ∀ᶠ x : ℝ in 𝓝[cotangentPowerDomain \ {0}] 0, 0 < 1 + x := by
    have hn : {x : ℝ | 0 < 1 + x} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds (by norm_num)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hn
  exact power_limit_of_log_product hpos hprod

/-- Bài tập 3.6.8(b): giới hạn bằng exp(2/π). -/
theorem two_sub_phase_tangent_power_limit :
    DomainLimit phaseTangentPowerDomain
      (fun x ↦ (2 - x) ^ Real.tan (Real.pi * x / 2)) 1 (Real.exp (2 / Real.pi)) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (2 - x)) (-1) 1 := by
    simpa only [id_eq, show (2 : ℝ) - 1 = 1 by norm_num, div_one] using
      ((hasDerivAt_id (1 : ℝ)).const_sub 2).log (by norm_num : (2 : ℝ) - 1 ≠ 0)
  have hp : HasDerivAt (fun x : ℝ ↦ Real.pi * x / 2) (Real.pi / 2) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_mul Real.pi).div_const 2
  have hg : HasDerivAt (fun x : ℝ ↦ Real.cos (Real.pi * x / 2)) (-(Real.pi / 2)) 1 := by
    simpa using hp.cos
  have hn : -(Real.pi / 2) ≠ 0 := neg_ne_zero.mpr
    (div_ne_zero Real.pi_ne_zero (by norm_num))
  have hr := ratio_of_derivative_slopes phase_tangent_power_domain_accumulation hf hg
    (by norm_num) (by simp) hn
  have hvalue : (-1 : ℝ) / (-(Real.pi / 2)) = 2 / Real.pi := by
    field_simp [Real.pi_ne_zero]
  rw [hvalue] at hr
  have ht := (domainLimit_iff_tendsto phase_tangent_power_domain_accumulation).mp hr
  have hs : Tendsto (fun x : ℝ ↦ Real.sin (Real.pi * x / 2))
      (𝓝[phaseTangentPowerDomain \ {1}] 1) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.sin (Real.pi * x / 2)) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun x ↦ Real.tan (Real.pi * x / 2) * Real.log (2 - x))
      (𝓝[phaseTangentPowerDomain \ {1}] 1) (𝓝 (2 / Real.pi)) := by
    have hm := ht.mul hs
    simp only [mul_one] at hm
    apply hm.congr
    intro x
    rw [Real.tan_eq_sin_div_cos]
    ring
  apply (domainLimit_iff_tendsto phase_tangent_power_domain_accumulation).mpr
  have hpos : ∀ᶠ x : ℝ in 𝓝[phaseTangentPowerDomain \ {1}] 1, 0 < 2 - x := by
    have hn : {x : ℝ | 0 < 2 - x} ∈ 𝓝 (1 : ℝ) :=
      (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds (by norm_num)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hn
  exact power_limit_of_log_product hpos hprod

/-- Bài tập 3.6.8(c): giới hạn lũy thừa bằng 1 tại +∞. -/
theorem quadratic_ratio_rational_power_atTop_limit :
    DomainAtTopLimit quadraticRatioPowerDomain
      (fun x ↦ ((x ^ 2 - 1) / (x ^ 2 + 1)) ^ ((x - 1) / (x + 1))) 1 := by
  have hden : Tendsto (fun x : ℝ ↦ x ^ 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hi := hden.inv_tendsto_atTop
  have hbase : Tendsto (fun x : ℝ ↦ (x ^ 2 - 1) / (x ^ 2 + 1)) atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ 1 + (-2 : ℝ) * (x ^ 2 + 1)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul (-2 : ℝ))
    apply ht.congr
    intro x
    have hd : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
    field_simp [hd]
    ring
  have hshift : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_id
  have hj := hshift.inv_tendsto_atTop
  have hexponent : Tendsto (fun x : ℝ ↦ (x - 1) / (x + 1)) atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ 1 + (-2 : ℝ) * (x + 1)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hj.const_mul (-2 : ℝ))
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : x + 1 ≠ 0 := by linarith
    field_simp [hd]
    ring
  have hlog : Tendsto (fun x : ℝ ↦ Real.log ((x ^ 2 - 1) / (x ^ 2 + 1))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using hbase.log (by norm_num : (1 : ℝ) ≠ 0)
  have hprod : Tendsto (fun x : ℝ ↦ ((x - 1) / (x + 1)) *
      Real.log ((x ^ 2 - 1) / (x ^ 2 + 1))) (atTop ⊓ 𝓟 quadraticRatioPowerDomain) (𝓝 0) := by
    simpa only [mul_zero] using (hexponent.mul hlog).mono_left inf_le_left
  have hpos : ∀ᶠ x : ℝ in atTop ⊓ 𝓟 quadraticRatioPowerDomain,
      0 < (x ^ 2 - 1) / (x ^ 2 + 1) := by
    filter_upwards [(eventually_gt_atTop (1 : ℝ)).filter_mono inf_le_left] with x hx
    exact div_pos (by nlinarith) (by nlinarith [sq_nonneg x])
  apply (domainAtTopLimit_iff_tendsto quadratic_ratio_power_domain_unbounded).mpr
  simpa only [Real.exp_zero] using power_limit_of_log_product hpos hprod

end calculus.Chapter03.Section06VariablePowerLimitExercises
