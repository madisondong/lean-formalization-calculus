import calculus.Chapter03.Section03Exercises
import calculus.Chapter03.Section06SourceIssues
import calculus.Chapter03.Section01Powers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.8(d): lũy thừa `(sin x)^(tan x)`. -/
namespace calculus.Chapter03.Section06SineTangentPowerLimit
open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section06SourceIssues calculus.Chapter03.Section01Powers

theorem positive_base_mem_sine_power_domain {x α : ℝ} (hx : 0 < x) :
    x ∈ realPowerDomain α := by
  classical
  unfold realPowerDomain
  split_ifs <;> first | exact mem_univ x | exact hx.ne' | exact hx

def sineTangentPowerDomain : Set ℝ :=
  {x | Real.sin x ∈ realPowerDomain (Real.tan x) ∧ Real.cos x ≠ 0}

theorem sine_tangent_power_domain_accumulation :
    AccumulationPointOf sineTangentPowerDomain (Real.pi/2) := by
  have hg : HasDerivAt Real.cos (-1) (Real.pi/2) := by
    simpa only [Real.sin_pi_div_two] using Real.hasDerivAt_cos (Real.pi/2)
  have ha := derivative_quotient_domain_accumulation hg Real.cos_pi_div_two (by norm_num)
  have hpos : {x : ℝ | 0 < Real.sin x} ∈ 𝓝 (Real.pi/2) :=
    (isOpen_lt continuous_const Real.continuous_sin).mem_nhds
      (by change 0 < Real.sin (Real.pi/2); rw [Real.sin_pi_div_two]; norm_num)
  apply accumulationPointOf_mono (accumulationPointOf_inter_nhds ha hpos)
  intro x hx
  exact ⟨positive_base_mem_sine_power_domain hx.2, hx.1⟩

/-- Bài tập 3.6.8(d): (sin x)^(tan x)→1 khi x→π/2 từ hai phía. -/
theorem sine_tangent_power_limit :
    DomainLimit sineTangentPowerDomain
      (fun x : ℝ ↦ (Real.sin x)^(Real.tan x)) (Real.pi/2) 1 := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (Real.sin x)) 0 (Real.pi/2) := by
    simpa only [Real.sin_pi_div_two, Real.cos_pi_div_two, zero_div] using
      (Real.hasDerivAt_sin (Real.pi/2)).log (by rw [Real.sin_pi_div_two]; norm_num)
  have hg : HasDerivAt Real.cos (-1) (Real.pi/2) := by
    simpa only [Real.sin_pi_div_two] using Real.hasDerivAt_cos (Real.pi/2)
  have hr := ratio_of_derivative_slopes sine_tangent_power_domain_accumulation hf hg
    (by simp [Real.sin_pi_div_two]) Real.cos_pi_div_two (by norm_num)
  have ht : Tendsto (fun x : ℝ ↦ Real.log (Real.sin x)/Real.cos x)
      (𝓝[sineTangentPowerDomain \ {Real.pi/2}] (Real.pi/2)) (𝓝 (0 : ℝ)) := by
    simpa using (domainLimit_iff_tendsto sine_tangent_power_domain_accumulation).mp hr
  have hs : Tendsto Real.sin (𝓝[sineTangentPowerDomain \ {Real.pi/2}] (Real.pi/2))
      (𝓝 (1 : ℝ)) := by
    simpa only [Real.sin_pi_div_two] using
      (Real.continuous_sin.continuousAt (x := Real.pi/2)).tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun x : ℝ ↦ Real.tan x*Real.log (Real.sin x))
      (𝓝[sineTangentPowerDomain \ {Real.pi/2}] (Real.pi/2)) (𝓝 (0 : ℝ)) := by
    have hprod : Tendsto (fun x : ℝ ↦ Real.sin x*(Real.log (Real.sin x)/Real.cos x))
        (𝓝[sineTangentPowerDomain \ {Real.pi/2}] (Real.pi/2)) (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hs.mul ht
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hx.1.2]
  have hpos : ∀ᶠ x : ℝ in
      𝓝[sineTangentPowerDomain \ {Real.pi/2}] (Real.pi/2), 0 < Real.sin x := by
    have hn : {x : ℝ | 0 < Real.sin x} ∈ 𝓝 (Real.pi/2) :=
      (isOpen_lt continuous_const Real.continuous_sin).mem_nhds
        (by change 0 < Real.sin (Real.pi/2); rw [Real.sin_pi_div_two]; norm_num)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hn
  apply (domainLimit_iff_tendsto sine_tangent_power_domain_accumulation).mpr
  simpa only [Real.exp_zero] using power_limit_of_log_product hpos hp

end calculus.Chapter03.Section06SineTangentPowerLimit
