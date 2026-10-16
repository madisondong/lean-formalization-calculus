import calculus.Chapter04.Section04TaylorLimitCoefficients
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Positivity

/-!
# §4.4 Bài 5: đạo hàm sau khi khử cực tại 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1719–1726.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04ExponentialCancellationDifferentiability
open calculus.Chapter04.Section04TaylorLimitCoefficients

def exponentialCancellation (u : ℝ) : ℝ :=
  if u = 0 then 1 / 2 else 1 / u - 1 / (Real.exp u - 1)

def baseTwoCancellation (x : ℝ) : ℝ :=
  if x = 0 then 1 / 2 else 1 / (x * Real.log 2) - 1 / ((2 : ℝ) ^ x - 1)

theorem exponential_sub_one_ne_zero {u : ℝ} (hu : u ≠ 0) : Real.exp u - 1 ≠ 0 := by
  intro he
  have hexp : Real.exp u = Real.exp 0 := by simpa using (sub_eq_zero.mp he)
  exact hu (Real.exp_injective hexp)

theorem source_base_two_denominators_ne_zero {x : ℝ} (hx : x ≠ 0) :
    x * Real.log 2 ≠ 0 ∧ (2 : ℝ) ^ x - 1 ≠ 0 := by
  have hc : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨mul_ne_zero hx hc, ?_⟩
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact exponential_sub_one_ne_zero (mul_ne_zero hc hx)

theorem exponential_linear_residual_tendsto :
    Tendsto (fun u : ℝ ↦ (Real.exp u - 1) / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa only [slope_fun_def_field, sub_zero, Real.exp_zero] using! (Real.hasDerivAt_exp 0).tendsto_slope

theorem exponential_quadratic_residual_tendsto :
    Tendsto (fun u : ℝ ↦ (Real.exp u - 1 - u) / u ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hid : Tendsto (fun u : ℝ ↦ u) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hid.mul exponential_cubic_quotient_tendsto).add_const (1 / 2 : ℝ)
  norm_num only [zero_mul, zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  field_simp [hu0]
  ring

theorem exponentialCancellation_hasDerivAt_zero :
    HasDerivAt exponentialCancellation (-1 / 12) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht := ((exponential_cubic_quotient_tendsto.const_mul 2).sub
    exponential_quadratic_residual_tendsto).div (exponential_linear_residual_tendsto.const_mul 2)
      (by norm_num : (2 * (1 : ℝ)) ≠ 0)
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  have he := exponential_sub_one_ne_zero hu0
  dsimp only [Pi.div_apply]
  rw [slope_def_field]
  simp [exponentialCancellation, hu0]
  field_simp [hu0, he]
  ring

theorem baseTwoCancellation_eq_exponentialCancellation (x : ℝ) :
    baseTwoCancellation x = exponentialCancellation (Real.log 2 * x) := by
  have hc : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  by_cases hx : x = 0
  · simp [hx, baseTwoCancellation, exponentialCancellation]
  · simp only [baseTwoCancellation, exponentialCancellation, if_neg hx,
      if_neg (mul_ne_zero hc hx), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm x]

theorem source_base_two_cancellation_hasDerivAt_zero :
    HasDerivAt baseTwoCancellation (-Real.log 2 / 12) 0 := by
  have hlinear : HasDerivAt (fun x : ℝ ↦ Real.log 2 * x) (Real.log 2) 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).const_mul (Real.log 2)
  have houter : HasDerivAt exponentialCancellation (-1 / 12) (Real.log 2 * 0) := by
    simpa only [mul_zero] using exponentialCancellation_hasDerivAt_zero
  have ht := houter.comp 0 hlinear
  have hfunc : exponentialCancellation ∘ (fun x : ℝ ↦ Real.log 2 * x) = baseTwoCancellation := by
    funext x
    exact (baseTwoCancellation_eq_exponentialCancellation x).symm
  rw [hfunc] at ht
  apply ht.congr_deriv
  ring

theorem source_base_two_cancellation_differentiableAt_zero :
    DifferentiableAt ℝ baseTwoCancellation 0 :=
  source_base_two_cancellation_hasDerivAt_zero.differentiableAt

theorem base_two_cancellation_deriv_at_zero :
    deriv baseTwoCancellation 0 = -Real.log 2 / 12 :=
  source_base_two_cancellation_hasDerivAt_zero.deriv

end calculus.Chapter04.Section04ExponentialCancellationDifferentiability
