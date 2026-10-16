import calculus.Chapter04.Section04LHospitalLimitCalculations
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# §4.4 Bài 2: sáu giới hạn lũy thừa biến thiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1678–1688. Miền lũy thừa gồm cả cơ số âm khi số mũ nguyên cho phép.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04VariablePowerLimitExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section01Powers
open calculus.Chapter04.Section04TaylorLimitCoefficients
open calculus.Chapter04.Section04LHospitalLimitCalculations
open calculus.Chapter04.Section04ElementaryLimitExamples

def identityPowerTangentDomain : Set ℝ :=
  {x | x ∈ realPowerDomain x ∧ Real.cos (x ^ x) ≠ 0}
def sineExponentDomain : Set ℝ := {x | x ∈ realPowerDomain (Real.sin x)}
def reciprocalExponentDomain : Set ℝ := {x | x ≠ 0 ∧ x ∈ realPowerDomain (1 / x)}
def logarithmicReciprocalExponentDomain : Set ℝ :=
  {x | 0 < x ∧ Real.log x ≠ 0 ∧ x ∈ realPowerDomain (1 / Real.log x)}
def affineRationalPowerDomain : Set ℝ :=
  {x | 2 * x + 5 ≠ 0 ∧ (2 * x - 3) / (2 * x + 5) ∈ realPowerDomain (2 * x + 1)}
def oneSubIdentityExponentDomain : Set ℝ :=
  {x | 1 - x ≠ 0 ∧ x ∈ realPowerDomain (1 / (1 - x))}

theorem positive_base_mem_source_power_domain (α x : ℝ) (hx : 0 < x) :
    x ∈ realPowerDomain α := by
  unfold realPowerDomain
  split_ifs
  · exact mem_univ _
  · exact hx.ne'
  · exact hx

theorem identity_power_lhospital_right :
    Tendsto (fun x : ℝ ↦ x ^ x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp source_identity_mul_log_right
  have ht' : Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log x))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [Real.rpow_def_of_pos hx, mul_comm]

theorem cosine_one_ne_zero : Real.cos (1 : ℝ) ≠ 0 := by
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_three]

theorem source_identity_power_tangent_right_limit :
    DomainRightLimit identityPowerTangentDomain (fun x : ℝ ↦ Real.tan (x ^ x)) 0 (Real.tan 1) := by
  have hcos : ∀ᶠ x in 𝓝[>] (0 : ℝ), Real.cos (x ^ x) ≠ 0 :=
    (Real.continuous_cos.continuousAt.tendsto.comp identity_power_lhospital_right).eventually_ne
      cosine_one_ne_zero
  have hlim := (Real.hasDerivAt_tan cosine_one_ne_zero).continuousAt.tendsto.comp
    identity_power_lhospital_right
  apply source_right_limit_of_eventual_natural_domain _ hlim
  filter_upwards [self_mem_nhdsWithin, hcos] with x (hx : 0 < x) hc
  exact ⟨positive_base_mem_source_power_domain x x hx, hc⟩

theorem sine_exponent_lhospital_right :
    Tendsto (fun x : ℝ ↦ x ^ Real.sin x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlog := (sine_linear_quotient_tendsto.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))).mul
    source_identity_mul_log_right
  norm_num only [mul_zero] at hlog
  have hlog' : Tendsto (fun x : ℝ ↦ Real.log x * Real.sin x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    field_simp [hx.ne']
  have ht := Real.continuous_exp.continuousAt.tendsto.comp hlog'
  have ht' : Tendsto (fun x : ℝ ↦ Real.exp (Real.log x * Real.sin x))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  exact (Real.rpow_def_of_pos hx (Real.sin x)).symm

theorem source_sine_exponent_right_limit :
    DomainRightLimit sineExponentDomain (fun x : ℝ ↦ x ^ Real.sin x) 0 1 := by
  apply source_right_limit_of_eventual_natural_domain _ sine_exponent_lhospital_right
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  exact positive_base_mem_source_power_domain (Real.sin x) x hx

theorem logarithm_div_identity_lhospital_at_top :
    Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
  apply calculus.Chapter04.Section04InfiniteExtensions.source_lhopital_infinite_atTop
    (a := 0)
    (fun x hx ↦ Real.hasDerivAt_log (ne_of_gt hx))
    (fun x _ ↦ hasDerivAt_id x) (fun _ _ ↦ by norm_num)
    (Or.inl Real.tendsto_log_atTop) (Or.inl tendsto_id) _ (Or.inl ⟨0, rfl⟩)
  simpa only [div_one, one_div] using tendsto_inv_atTop_zero

theorem source_reciprocal_exponent_limit :
    DomainAtTopLimit reciprocalExponentDomain (fun x : ℝ ↦ x ^ (1 / x : ℝ)) 1 := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp logarithm_div_identity_lhospital_at_top
  have ht' : Tendsto (fun x : ℝ ↦ Real.exp (Real.log x / x)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using ht
  have hlim : Tendsto (fun x : ℝ ↦ x ^ (1 / x : ℝ)) atTop (𝓝 1) := by
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  apply source_at_top_limit_of_eventual_natural_domain _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact ⟨hx.ne', positive_base_mem_source_power_domain (1 / x) x hx⟩

theorem logarithm_self_ratio_lhospital_at_top :
    Tendsto (fun x : ℝ ↦ Real.log x / Real.log x) atTop (𝓝 1) := by
  apply calculus.Chapter04.Section04InfiniteExtensions.source_lhopital_infinite_atTop
    (a := 0)
    (fun x hx ↦ Real.hasDerivAt_log (ne_of_gt hx))
    (fun x hx ↦ Real.hasDerivAt_log (ne_of_gt hx))
    (fun x hx ↦ inv_ne_zero (ne_of_gt hx))
    (Or.inl Real.tendsto_log_atTop) (Or.inl Real.tendsto_log_atTop) _ (Or.inl ⟨1, rfl⟩)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (div_self (inv_ne_zero hx.ne')).symm

theorem source_logarithmic_reciprocal_exponent_limit :
    DomainAtTopLimit logarithmicReciprocalExponentDomain
      (fun x : ℝ ↦ x ^ (1 / Real.log x : ℝ)) (Real.exp 1) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp logarithm_self_ratio_lhospital_at_top
  have hlim : Tendsto (fun x : ℝ ↦ x ^ (1 / Real.log x : ℝ)) atTop (𝓝 (Real.exp 1)) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
    dsimp only [Function.comp_def]
    congr 1
    ring
  apply source_at_top_limit_of_eventual_natural_domain _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact ⟨by linarith, ne_of_gt (Real.log_pos hx),
    positive_base_mem_source_power_domain (1 / Real.log x) x (by linarith)⟩

theorem affine_rational_log_lhospital_at_top :
    Tendsto (fun x : ℝ ↦ Real.log ((2 * x - 3) / (2 * x + 5)) / (1 / (2 * x + 1)))
      atTop (𝓝 (-8 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hbase : Tendsto (fun x : ℝ ↦ (2 * x - 3) / (2 * x + 5)) atTop (𝓝 1) := by
    have ht := ((hinv.const_mul 3).const_sub 2).div
      ((hinv.const_mul 5).const_add 2) (by norm_num : (2 + 5 * (0 : ℝ)) ≠ 0)
    have ht' : Tendsto (fun x : ℝ ↦ (2 - 3 * (1 / x)) / (2 + 5 * (1 / x)))
        atTop (𝓝 1) := by simpa using! ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hn : x ≠ 0 := by linarith
    have hd : 2 * x + 5 ≠ 0 := by linarith
    have hd' : 2 + 5 * (1 / x) ≠ 0 := by positivity
    field_simp [hn, hd, hd']
  have hf {x : ℝ} (hx : 2 < x) :
      HasDerivAt (fun y : ℝ ↦ Real.log ((2 * y - 3) / (2 * y + 5)))
        (16 / ((2 * x - 3) * (2 * x + 5))) x := by
    have hd : 2 * x + 5 ≠ 0 := by linarith
    have hb : (2 * x - 3) / (2 * x + 5) ≠ 0 := by
      exact div_ne_zero (by linarith) hd
    have ht := (((hasDerivAt_id x).const_mul 2).sub_const 3).div
      (((hasDerivAt_id x).const_mul 2).add_const 5) hd
    have hlog := ht.log hb
    simp only [Pi.div_apply, id_eq] at hlog
    convert! hlog using 1
    field_simp [hd, (by linarith : 2 * x - 3 ≠ 0)]
    ring
  have hg {x : ℝ} (hx : 2 < x) : HasDerivAt (fun y : ℝ ↦ 1 / (2 * y + 1))
      (-2 / (2 * x + 1) ^ 2) x := by
    have ht := (((hasDerivAt_id x).const_mul 2).add_const 1).inv
      (by linarith : 2 * x + 1 ≠ 0)
    simpa only [one_div, id_eq, mul_one, neg_div] using! ht
  have hq : Tendsto (fun x : ℝ ↦ (16 / ((2 * x - 3) * (2 * x + 5))) /
      (-2 / (2 * x + 1) ^ 2)) atTop (𝓝 (-8 : ℝ)) := by
    have hnum := ((hinv.const_add 2).pow 2).const_mul (-8 : ℝ)
    have hden := ((hinv.const_mul 3).const_sub 2).mul ((hinv.const_mul 5).const_add 2)
    have ht := hnum.div hden (by norm_num : (2 - 3 * (0 : ℝ)) * (2 + 5 * (0 : ℝ)) ≠ 0)
    norm_num at ht
    have ht' : Tendsto (fun x : ℝ ↦ -8 * (2 + 1 / x) ^ 2 /
        ((2 - 3 * (1 / x)) * (2 + 5 * (1 / x)))) atTop (𝓝 (-8 : ℝ)) := by
      simpa using! ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hn : x ≠ 0 := by linarith
    have h₁ : 2 * x - 3 ≠ 0 := by linarith
    have h₂ : 2 * x + 5 ≠ 0 := by linarith
    have h₃ : 2 * x + 1 ≠ 0 := by linarith
    have h₄ : 2 - 3 * (1 / x) ≠ 0 := by
      have ht : 0 < 2 - 3 * (1 / x) := by
        have hh : 1 / x < 1 / 2 := (one_div_lt_one_div_of_lt (by norm_num) hx)
        linarith
      exact ht.ne'
    have h₅ : 2 + 5 * (1 / x) ≠ 0 := by positivity
    field_simp [hn, h₁, h₂, h₃, h₄, h₅]
    ring
  apply HasDerivAt.lhopital_zero_atTop
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    exact hf hx
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    exact hg hx
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 (by linarith))
  · simpa only [Real.log_one, Function.comp_def] using!
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hbase
  · have harg : Tendsto (fun x : ℝ ↦ 2 * x + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [one_div, Function.comp_def] using! tendsto_inv_atTop_zero.comp harg
  · exact hq

theorem source_affine_rational_power_limit :
    DomainAtTopLimit affineRationalPowerDomain
      (fun x : ℝ ↦ ((2 * x - 3) / (2 * x + 5)) ^ (2 * x + 1 : ℝ)) (Real.exp (-8)) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp affine_rational_log_lhospital_at_top
  have hlim : Tendsto (fun x : ℝ ↦ ((2 * x - 3) / (2 * x + 5)) ^ (2 * x + 1 : ℝ))
      atTop (𝓝 (Real.exp (-8))) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hb : 0 < (2 * x - 3) / (2 * x + 5) := div_pos (by linarith) (by linarith)
    rw [Real.rpow_def_of_pos hb]
    dsimp only [Function.comp_def]
    congr 1
    simp only [div_eq_mul_inv, one_mul, inv_inv]
  apply source_at_top_limit_of_eventual_natural_domain _ hlim
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  exact ⟨by linarith, positive_base_mem_source_power_domain (2 * x + 1)
    ((2 * x - 3) / (2 * x + 5)) (div_pos (by linarith) (by linarith))⟩

theorem logarithm_div_one_sub_identity_lhospital_right :
    Tendsto (fun x : ℝ ↦ Real.log x / (1 - x)) (𝓝[>] (1 : ℝ)) (𝓝 (-1 : ℝ)) := by
  have hf : ∀ᶠ x in 𝓝[>] (1 : ℝ), HasDerivAt Real.log (1 / x) x := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simpa only [one_div] using Real.hasDerivAt_log (by linarith : x ≠ 0)
  have hg (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using! (hasDerivAt_id x).const_sub 1
  apply HasDerivAt.lhopital_zero_nhdsGT hf (Eventually.of_forall hg)
    (Eventually.of_forall (fun (_ : ℝ) ↦ by norm_num))
  · simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (hg 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun x : ℝ ↦ (1 / x) / (-1)) 1 := by
      fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem source_one_sub_identity_exponent_right_limit :
    DomainRightLimit oneSubIdentityExponentDomain
      (fun x : ℝ ↦ x ^ (1 / (1 - x) : ℝ)) 1 (Real.exp (-1)) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp logarithm_div_one_sub_identity_lhospital_right
  have hlim : Tendsto (fun x : ℝ ↦ x ^ (1 / (1 - x) : ℝ))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.exp (-1))) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
    dsimp only [Function.comp_def]
    congr 1
    ring
  apply source_right_limit_of_eventual_natural_domain _ hlim
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  exact ⟨by linarith, positive_base_mem_source_power_domain (1 / (1 - x)) x (by linarith)⟩

end calculus.Chapter04.Section04VariablePowerLimitExercises
