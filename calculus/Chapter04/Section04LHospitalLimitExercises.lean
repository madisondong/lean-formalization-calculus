import calculus.Chapter04.Section04LHospitalLimitCalculations

/-!
# §4.4 Bài 1: chín giới hạn trên miền tự nhiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1662–1676. Các giới hạn giữ miền xác định tự nhiên; tham số `n` được xét trên ℝ.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04LHospitalLimitExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section01Powers
open calculus.Chapter04.Section04TaylorLimitCoefficients
open calculus.Chapter04.Section04LHospitalLimitCalculations

def exponentialSineCosineDomain : Set ℝ := {x | Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}
def logarithmReciprocalCancellationDomain : Set ℝ := {x | 0 < x ∧ Real.log x ≠ 0 ∧ x ≠ 1}
def cosineDoubleSineDomain : Set ℝ := {x | x ≠ 0 ∧ Real.sin x ≠ 0}
def cubicPowerDomain : Set ℝ := {x | x ≠ 0}
def sineTangentRatioDomain : Set ℝ := {x | Real.cos x ≠ 0 ∧ x - Real.tan x ≠ 0}
def logarithmCotangentDomain : Set ℝ := {x | 0 < x ∧ Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}
def arctangentTailLogarithmDomain : Set ℝ :=
  {x | x ≠ 0 ∧ 0 < 1 + 1 / x ∧ Real.log (1 + 1 / x) ≠ 0}
def squareRootDomain : Set ℝ := {x | 0 ≤ x}
def affinePowerDomain (n : ℝ) : Set ℝ := {x | x ≠ 0 ∧ 1 + x ∈ realPowerDomain n}

theorem source_exponential_difference_sine_cosine_limit :
    DomainLimit exponentialSineCosineDomain
      (fun x : ℝ ↦ (Real.exp x - Real.exp (-x)) / (Real.sin x * Real.cos x)) 0 2 := by
  apply source_limit_of_eventual_natural_domain _ exp_difference_div_sine_cosine_lhospital
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.2.1, hx.2.2.1⟩

theorem source_logarithm_reciprocal_cancellation_right_limit :
    DomainRightLimit logarithmReciprocalCancellationDomain
      (fun x : ℝ ↦ 1 / Real.log x - 1 / (x - 1)) 1 (1 / 2) := by
  have harg : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using! ((hasDerivAt_id (1 : ℝ)).sub_const 1).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
      change 0 < x - 1
      linarith
  have ht := log_one_add_reciprocal_cancellation_lhospital_right.comp harg
  have hshift (x : ℝ) : 1 + (x - 1) = x := by ring
  have hlim : Tendsto (fun x : ℝ ↦ 1 / Real.log x - 1 / (x - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Function.comp_def, hshift] using! ht
  apply source_right_limit_of_eventual_natural_domain _ hlim
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  exact ⟨by linarith, ne_of_gt (Real.log_pos hx), ne_of_gt hx⟩

theorem source_cosine_double_sine_limit :
    DomainLimit cosineDoubleSineDomain
      (fun x : ℝ ↦ (1 - Real.cos (2 * x)) / (x * Real.sin x)) 0 2 := by
  apply source_limit_of_eventual_natural_domain _ one_sub_cosine_double_div_identity_sine_lhospital
  filter_upwards [basic_natural_domains_eventually] with x hx
  exact ⟨hx.1, hx.2.1⟩

theorem source_identity_sub_arctangent_cubic_limit :
    DomainLimit cubicPowerDomain (fun x : ℝ ↦ (x - Real.arctan x) / x ^ 3) 0 (1 / 3) := by
  apply source_limit_of_eventual_natural_domain _ identity_sub_arctangent_cubic_lhospital
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa [cubicPowerDomain] using hx

theorem source_identity_sine_tangent_ratio_limit :
    DomainLimit sineTangentRatioDomain
      (fun x : ℝ ↦ (x - Real.sin x) / (x - Real.tan x)) 0 (-1 / 2) := by
  apply source_limit_of_eventual_natural_domain _ identity_sine_tangent_ratio_lhospital
  filter_upwards [basic_natural_domains_eventually,
    identity_sine_tangent_ratio_lhospital.eventually_ne (by norm_num : (-1 / 2 : ℝ) ≠ 0)]
    with x hx hq
  refine ⟨hx.2.2.1, ?_⟩
  intro he
  exact hq (by simp only [he, div_zero])

theorem source_logarithm_cotangent_right_limit :
    DomainRightLimit logarithmCotangentDomain
      (fun x : ℝ ↦ Real.log x / Real.cot x) 0 0 := by
  apply source_right_limit_of_eventual_natural_domain _ logarithm_div_cotangent_lhospital_right
  filter_upwards [self_mem_nhdsWithin,
    basic_natural_domains_eventually.filter_mono (nhdsGT_le_nhdsNE (0 : ℝ))]
    with x (hx : 0 < x) hd
  exact ⟨hx, hd.2.1, hd.2.2.1⟩

theorem source_arctangent_tail_logarithm_limit :
    DomainAtTopLimit arctangentTailLogarithmDomain
      (fun x : ℝ ↦ (Real.pi / 2 - Real.arctan x) / Real.log (1 + 1 / x)) 1 := by
  apply source_at_top_limit_of_eventual_natural_domain _ arctangent_tail_div_log_reciprocal_lhospital
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hu : 0 < 1 / x := one_div_pos.mpr hx
  exact ⟨hx.ne', by linarith, ne_of_gt (Real.log_pos (by linarith))⟩

theorem source_square_root_exp_negative_limit :
    DomainAtTopLimit squareRootDomain (fun x : ℝ ↦ Real.sqrt x * Real.exp (-x)) 0 := by
  apply source_at_top_limit_of_eventual_natural_domain _ square_root_exp_negative_lhospital
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact hx.le

theorem source_affine_power_second_coefficient_limit (n : ℝ) :
    DomainLimit (affinePowerDomain n)
      (fun x : ℝ ↦ ((1 + x) ^ n - 1 - n * x) / x ^ 2) 0 (n * (n - 1) / 2) := by
  apply source_limit_of_eventual_natural_domain _ (affine_power_second_coefficient_lhospital n)
  filter_upwards [basic_natural_domains_eventually] with x hx
  refine ⟨hx.1, ?_⟩
  unfold realPowerDomain
  split_ifs
  · exact mem_univ _
  · exact ne_of_gt hx.2.2.2.1
  · exact hx.2.2.2.1

end calculus.Chapter04.Section04LHospitalLimitExercises
