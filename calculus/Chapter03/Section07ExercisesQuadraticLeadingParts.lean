import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §3.7 — phần chính bậc hai và phép khử căn

Nguồn: Bài tập 3.7.3(f,g,k), `Ch3_gioihanhamso.tex`, dòng 3492, dòng 3493, dòng 3497.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesQuadraticLeadingParts

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Orders
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts

/-- Thương sai phân của exp, gán giá trị 1 tại 0. -/
noncomputable def normalizedExponentialIncrement : ℝ → ℝ :=
  Function.update (fun u ↦ (Real.exp u - 1) / u) 0 1


theorem normalized_exponential_increment_continuousAt :
    ContinuousAt normalizedExponentialIncrement 0 := by
  have he : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp (0 : ℝ)
  simpa only [normalizedExponentialIncrement, Real.exp_zero, sub_zero] using he.continuousAt_div


theorem normalized_exponential_increment_mul (u : ℝ) :
    normalizedExponentialIncrement u * u = Real.exp u - 1 := by
  by_cases hu : u = 0
  · simp [hu, normalizedExponentialIncrement]
  · simp [normalizedExponentialIncrement, hu]


theorem cosine_sub_double_cosine_div_square_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.cos x - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (3 / 2 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ ↦
      2 * (Real.sin x / x) ^ 2 - (1 - Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (3 / 2 : ℝ)) := by
    convert! ((sine_equivalent_identity_zero.2.2.pow 2).const_mul 2).sub
      one_sub_cos_div_square_tendsto using 1
    norm_num
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  have hcos : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    nlinarith [Real.cos_two_mul x, Real.sin_sq_add_cos_sq x]
  rw [hcos]
  field_simp [hx]
  ring

/-- Bài tập 3.7.3(f): hiệu hai hàm mũ có phần chính (3e/2)x². -/
theorem exponential_cosine_difference_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.exp (Real.cos x) - Real.exp (Real.cos (2 * x)))
      (fun x ↦ x) 2 (3 * Real.exp 1 / 2) := by
  have hc : ContinuousAt (fun x : ℝ ↦ Real.cos x - Real.cos (2 * x)) 0 := by fun_prop
  have hi : Tendsto (fun x : ℝ ↦
      normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x)))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hn : ContinuousAt (fun x : ℝ ↦
        normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x))) 0 := by
      apply ContinuousAt.comp
      · simpa only [normalizedExponentialIncrement, mul_zero, Real.cos_zero, sub_self] using!
          normalized_exponential_increment_continuousAt
      · exact hc
    simpa only [domainApproachFilter, mul_zero, Real.cos_zero, sub_self,
      normalizedExponentialIncrement, Function.update_self] using
      hn.tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun x : ℝ ↦ Real.exp (Real.cos (2 * x)))
      (domainApproachFilter univ (.point 0)) (𝓝 (Real.exp 1)) := by
    have hn : ContinuousAt (fun x : ℝ ↦ Real.exp (Real.cos (2 * x))) 0 := by fun_prop
    simpa [domainApproachFilter] using hn.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ Real.exp (Real.cos (2 * x)) *
      normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x)) *
      ((Real.cos x - Real.cos (2 * x)) / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (3 * Real.exp 1 / 2)) := by
    have hvalue : Real.exp 1 * 1 * (3 / 2 : ℝ) = 3 * Real.exp 1 / 2 := by ring
    simpa only [hvalue] using (he.mul hi).mul cosine_sub_double_cosine_div_square_tendsto
  apply hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0)
    (by norm_num : 0 < (2 : ℕ)) (by nlinarith [Real.exp_pos 1])
  · have hn : ContinuousAt (fun x : ℝ ↦
        Real.exp (Real.cos x) - Real.exp (Real.cos (2 * x))) 0 := by fun_prop
    simpa [domainApproachFilter] using hn.tendsto.mono_left nhdsWithin_le_nhds
  · apply ht.congr'
    apply Eventually.of_forall
    intro x
    have hid := normalized_exponential_increment_mul (Real.cos x - Real.cos (2 * x))
    have hex : Real.exp (Real.cos x) =
        Real.exp (Real.cos (2 * x)) * Real.exp (Real.cos x - Real.cos (2 * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change Real.exp (Real.cos (2 * x)) *
      normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x)) *
      ((Real.cos x - Real.cos (2 * x)) / x ^ 2) =
      (Real.exp (Real.cos x) - Real.exp (Real.cos (2 * x))) / x ^ 2
    rw [hex]
    calc
      Real.exp (Real.cos (2 * x)) *
          normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x)) *
          ((Real.cos x - Real.cos (2 * x)) / x ^ 2) =
          Real.exp (Real.cos (2 * x)) *
          (normalizedExponentialIncrement (Real.cos x - Real.cos (2 * x)) *
          (Real.cos x - Real.cos (2 * x))) / x ^ 2 := by ring
      _ = (Real.exp (Real.cos (2 * x)) *
          Real.exp (Real.cos x - Real.cos (2 * x)) - Real.exp (Real.cos (2 * x))) / x ^ 2 := by
        rw [hid]
        ring


def exponentialCosineRootDomain : Set ℝ := {x | 0 ≤ Real.cos (2 * x)}


theorem exponential_cosine_root_domain_nhds : exponentialCosineRootDomain ∈ 𝓝 (0 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ ↦ Real.cos (2 * x)) 0 := by fun_prop
  have he := hc.tendsto.eventually (Ioi_mem_nhds
    (by norm_num : (0 : ℝ) < Real.cos (2 * 0)))
  exact he.mono fun _ hx ↦ le_of_lt hx


theorem exponential_cosine_root_domain_accumulation :
    AccumulationPointOf exponentialCosineRootDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) exponential_cosine_root_domain_nhds

/-- Bài tập 3.7.3(g): exp(x²)−√(cos 2x) có phần chính 2x². -/
theorem exponential_square_sub_cosine_root_principal_part :
    HasPowerPrincipalPartAlong exponentialCosineRootDomain (.point 0)
      (fun x ↦ Real.exp (x ^ 2) - Real.sqrt (Real.cos (2 * x))) (fun x ↦ x) 2 2 := by
  have hn : ContinuousAt (fun x : ℝ ↦ normalizedExponentialIncrement (x ^ 2)) 0 := by
    apply ContinuousAt.comp
    · simpa only [normalizedExponentialIncrement, zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
        normalized_exponential_increment_continuousAt
    · fun_prop
  have hi : Tendsto (fun x : ℝ ↦ normalizedExponentialIncrement (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, zero_pow (by decide : (2 : ℕ) ≠ 0),
      normalizedExponentialIncrement, Function.update_self] using
      hn.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun x : ℝ ↦
      (1 - Real.cos (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    have ht := (sine_equivalent_identity_zero.2.2.pow 2).const_mul 2
    apply (show Tendsto (fun x : ℝ ↦ 2 * (Real.sin x / x) ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) from by simpa using ht).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    have hid : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
      nlinarith [Real.cos_two_mul x, Real.sin_sq_add_cos_sq x]
    rw [hid]
    field_simp [hx]
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (Real.cos (2 * x)) + 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    have hct : ContinuousAt (fun x : ℝ ↦ Real.sqrt (Real.cos (2 * x)) + 1) 0 := by fun_prop
    simpa only [domainApproachFilter, mul_zero, Real.cos_zero, Real.sqrt_one,
      one_add_one_eq_two] using! hct.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ normalizedExponentialIncrement (x ^ 2) +
      ((1 - Real.cos (2 * x)) / x ^ 2) / (Real.sqrt (Real.cos (2 * x)) + 1))
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    convert! hi.add (hc.div hd (by norm_num : (2 : ℝ) ≠ 0)) using 1; norm_num
  apply hasPowerPrincipalPartAlong_nat_of_tendsto exponential_cosine_root_domain_accumulation
    (by norm_num : 0 < (2 : ℕ)) (by norm_num : (2 : ℝ) ≠ 0)
  · have hct : ContinuousAt (fun x : ℝ ↦
        Real.exp (x ^ 2) - Real.sqrt (Real.cos (2 * x))) 0 := by fun_prop
    simpa [domainApproachFilter] using hct.tendsto.mono_left nhdsWithin_le_nhds
  · apply (ht.mono_left (nhdsWithin_mono 0
      (sdiff_subset_sdiff_left (subset_univ exponentialCosineRootDomain)))).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxn : x ≠ 0 := by simpa using hx.2
    have hxx : x ^ 2 ≠ 0 := pow_ne_zero 2 hxn
    have hroot : Real.sqrt (Real.cos (2 * x)) ^ 2 = Real.cos (2 * x) := Real.sq_sqrt hx.1
    have hden : Real.sqrt (Real.cos (2 * x)) + 1 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (Real.cos (2 * x))]
    simp only [normalizedExponentialIncrement, Function.update_of_ne hxx]
    field_simp [hxx, hden]
    have hroot_normalized : Real.sqrt (Real.cos (x * 2)) ^ 2 = Real.cos (x * 2) := by
      simpa only [mul_comm 2 x] using hroot
    nlinarith [hroot_normalized]


def quarticRootDomain : Set ℝ := {x | 0 ≤ 4 - x ^ 4}


theorem quartic_root_domain_nhds : quarticRootDomain ∈ 𝓝 (0 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ ↦ 4 - x ^ 4) 0 := by fun_prop
  have he := hc.tendsto.eventually (Ioi_mem_nhds
    (by norm_num : (0 : ℝ) < 4 - (0 : ℝ) ^ 4))
  exact he.mono fun _ hx ↦ le_of_lt hx


theorem quartic_root_domain_accumulation : AccumulationPointOf quarticRootDomain 0 := by
  simpa only [univ_inter] using accumulationPointOf_inter_nhds
    (univ_accumulation 0) quartic_root_domain_nhds

/-- Bài tập 3.7.3(k): √(4−x⁴)+x²−2 có phần chính x². -/
theorem quartic_root_add_square_principal_part :
    HasPowerPrincipalPartAlong quarticRootDomain (.point 0)
      (fun x ↦ Real.sqrt (4 - x ^ 4) + x ^ 2 - 2) (fun x ↦ x) 2 1 := by
  have hs4 : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hi : Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ 2) 0 := by fun_prop
    simpa [domainApproachFilter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (4 - x ^ 4) + 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.sqrt (4 - x ^ 4) + 2) 0 := by fun_prop
    have hvalue : (2 : ℝ) + 2 = 4 := by norm_num
    simpa only [domainApproachFilter, zero_pow (by decide : (4 : ℕ) ≠ 0), sub_zero,
      hs4, hvalue] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ 1 - x ^ 2 / (Real.sqrt (4 - x ^ 4) + 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (hi.div hd (by norm_num : (4 : ℝ) ≠ 0))
  apply hasPowerPrincipalPartAlong_nat_of_tendsto quartic_root_domain_accumulation
    (by norm_num : 0 < (2 : ℕ)) (by norm_num : (1 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦ Real.sqrt (4 - x ^ 4) + x ^ 2 - 2) 0 := by fun_prop
    simpa [domainApproachFilter, hs4] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply (ht.mono_left (nhdsWithin_mono 0
      (sdiff_subset_sdiff_left (subset_univ quarticRootDomain)))).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxn : x ≠ 0 := by simpa using hx.2
    have hxx : x ^ 2 ≠ 0 := pow_ne_zero 2 hxn
    have hroot : Real.sqrt (4 - x ^ 4) ^ 2 = 4 - x ^ 4 := Real.sq_sqrt hx.1
    have hden : Real.sqrt (4 - x ^ 4) + 2 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (4 - x ^ 4)]
    field_simp [hxx, hden]
    nlinarith [hroot, sq_nonneg x]

end calculus.Chapter03.Section07ExercisesQuadraticLeadingParts
