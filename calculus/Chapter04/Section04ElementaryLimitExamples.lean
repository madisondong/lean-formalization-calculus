import calculus.Chapter04.Section04
import calculus.Chapter04.Section04Infinite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ba ví dụ giới hạn sơ cấp trong §4.4

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1541–1547, dòng 1615–1619, dòng 1642–1652.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ElementaryLimitExamples
open Set Filter
open scoped Topology


theorem exp_neg_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using ((hasDerivAt_id x).neg.exp)


theorem exp_odd_numerator_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp y - Real.exp (-y) - 2 * y)
      (Real.exp x + Real.exp (-x) - 2) x := by
  have ht := ((Real.hasDerivAt_exp x).fun_sub (exp_neg_hasDerivAt x)).fun_sub
    ((hasDerivAt_id x).const_mul 2)
  apply ht.congr_deriv
  ring


theorem exp_even_numerator_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp y + Real.exp (-y) - 2)
      (Real.exp x - Real.exp (-x)) x := by
  have ht := ((Real.hasDerivAt_exp x).fun_add (exp_neg_hasDerivAt x)).sub_const 2
  apply ht.congr_deriv
  ring


theorem one_sub_cos_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 1 - Real.cos y) (Real.sin x) x := by
  simpa only [neg_neg] using (Real.hasDerivAt_cos x).const_sub 1


theorem cosine_ne_zero_punctured :
    ∀ᶠ x : ℝ in 𝓝[≠] 0, Real.cos x ≠ 0 := by
  have hl : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  exact hl.eventually_ne one_ne_zero


theorem sine_ne_zero_punctured :
    ∀ᶠ x : ℝ in 𝓝[≠] 0, Real.sin x ≠ 0 := by
  have hI : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ∈ Ioo (-Real.pi) Real.pi :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioo_mem_nhds (by linarith [Real.pi_pos] : -Real.pi < (0 : ℝ)) Real.pi_pos)
  filter_upwards [hI, self_mem_nhdsWithin] with x hx hxn
  have hne : x ≠ 0 := by simpa using hxn
  intro hs
  exact hne ((Real.sin_eq_zero_iff_of_lt_of_lt hx.1 hx.2).mp hs)


theorem one_sub_cos_ne_zero_punctured :
    ∀ᶠ x : ℝ in 𝓝[≠] 0, 1 - Real.cos x ≠ 0 := by
  filter_upwards [sine_ne_zero_punctured] with x hx
  intro hz
  apply hx
  apply Real.sin_eq_zero_iff_cos_eq.mpr
  left
  linarith


theorem exp_odd_second_ratio_limit :
    Tendsto (fun x : ℝ ↦ (Real.exp x - Real.exp (-x)) / Real.cos x)
      (𝓝[≠] 0) (𝓝 0) := by
  have he : Tendsto Real.exp (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hen : Tendsto (fun x : ℝ ↦ Real.exp (-x)) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [neg_zero, Real.exp_zero] using
      (exp_neg_hasDerivAt 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hc : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  simpa only [Pi.div_def, sub_self, zero_div] using (he.sub hen).div hc one_ne_zero


theorem exp_odd_first_ratio_limit :
    Tendsto (fun x : ℝ ↦ (Real.exp x + Real.exp (-x) - 2) / Real.sin x)
      (𝓝[≠] 0) (𝓝 0) := by
  apply Section04.lhopital_zero_punctured
    (Eventually.of_forall exp_even_numerator_hasDerivAt)
    (Eventually.of_forall Real.hasDerivAt_sin) cosine_ne_zero_punctured
  · convert (exp_even_numerator_hasDerivAt 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0) using 1; norm_num
  · simpa only [Real.sin_zero] using
      Real.continuous_sin.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · exact exp_odd_second_ratio_limit

/-- Ví dụ 3: thương tiến về 0 khi `x → 0` từ hai phía. -/
theorem source_exp_odd_quotient_limit :
    Tendsto (fun x : ℝ ↦ (Real.exp x - Real.exp (-x) - 2 * x) / (1 - Real.cos x))
      (𝓝[≠] 0) (𝓝 0) := by
  apply Section04.lhopital_zero_punctured
    (Eventually.of_forall exp_odd_numerator_hasDerivAt)
    (Eventually.of_forall one_sub_cos_hasDerivAt) sine_ne_zero_punctured
  · simpa only [neg_zero, Real.exp_zero, mul_zero, sub_self, sub_zero] using
      (exp_odd_numerator_hasDerivAt 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · simpa only [Real.cos_zero, sub_self] using
      (one_sub_cos_hasDerivAt 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · exact exp_odd_first_ratio_limit


theorem logarithm_right_atBot : Tendsto Real.log (𝓝[>] (0 : ℝ)) atBot :=
  Real.tendsto_log_nhdsGT_zero


theorem reciprocal_right_atTop :
    Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop := by
  simpa only [one_div] using (tendsto_inv_nhdsGT_zero :
    Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[>] 0) atTop)


theorem logarithm_reciprocal_derivative_ratio {x : ℝ} (hx : 0 < x) :
    deriv Real.log x / deriv (fun y : ℝ ↦ 1 / y) x = -x := by
  have hd : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa only [one_div] using (hasDerivAt_inv hx.ne')
  rw [(Real.hasDerivAt_log hx.ne').deriv, hd.deriv]
  field_simp [hx.ne']


theorem logarithm_div_reciprocal_right :
    Tendsto (fun x : ℝ ↦ Real.log x / (1 / x)) (𝓝[>] 0) (𝓝 0) := by
  have hlog (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) := Real.hasDerivAt_log hx.1.ne'
  have hinv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun y : ℝ ↦ 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa only [one_div] using (hasDerivAt_inv hx.1.ne')
  have hq : Tendsto (fun x : ℝ ↦ deriv Real.log x / deriv (fun y : ℝ ↦ 1 / y) x)
      (𝓝[>] 0) (𝓝 0) := by
    have hn : Tendsto (fun x : ℝ ↦ -x) (𝓝[>] 0) (𝓝 0) := by
      simpa only [id_eq, neg_zero] using
        (continuous_id.continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).neg
    apply hn.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact (logarithm_reciprocal_derivative_ratio hx).symm
  apply Section04Infinite.source_lhopital_infinite_right_finite
    (a := 0) (b := 1) (by norm_num)
    (fun x hx ↦ (hlog x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hinv x hx).differentiableAt.differentiableWithinAt)
  · intro x hx
    rw [(hinv x hx).deriv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hx.1.ne'))
  · exact Or.inr logarithm_right_atBot
  · exact Or.inl reciprocal_right_atTop
  · exact hq

/-- Ví dụ 5: `x log x → 0` khi `x → 0⁺`. -/
theorem source_identity_mul_log_right :
    Tendsto (fun x : ℝ ↦ x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  apply logarithm_div_reciprocal_right.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  field_simp [hx.ne']


theorem sine_four_base_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 1 + Real.sin (4 * y)) (4 * Real.cos (4 * x)) x := by
  have ht : HasDerivAt (fun y : ℝ ↦ 1 + Real.sin (4 * y))
      (Real.cos (4 * x) * 4) x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).const_mul 4).sin).const_add 1
  exact ht.congr_deriv (by ring)


theorem sine_four_local_domain {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (Real.pi / 8)) :
    0 < 1 + Real.sin (4 * x) ∧ 0 < Real.cos x ∧
      0 < Real.sin x ∧ 0 < Real.tan x := by
  have hs4 : 0 < Real.sin (4 * x) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1
    (by linarith [hx.2, Real.pi_pos])
  refine ⟨by linarith, hc, hs, ?_⟩
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos hs hc


theorem sine_four_base_right :
    Tendsto (fun x : ℝ ↦ 1 + Real.sin (4 * x)) (𝓝[>] 0) (𝓝 1) := by
  simpa only [mul_zero, Real.sin_zero, add_zero] using
    (sine_four_base_hasDerivAt 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)


theorem cotangent_right_atTop : Tendsto Real.cot (𝓝[>] (0 : ℝ)) atTop := by
  have ht : Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.tan_zero] using
      (Real.hasDerivAt_tan (by simp : Real.cos (0 : ℝ) ≠ 0)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, Real.tan x ∈ Ioi (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 8)] with x hx
    exact (sine_four_local_domain hx).2.2.2
  have ht' : Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, hpos⟩
  simpa only [Pi.inv_def, Real.tan_inv_eq_cot] using ht'.inv_tendsto_nhdsGT_zero


theorem sine_power_derivative_ratio_right :
    Tendsto (fun x : ℝ ↦ (4 * Real.cos (4 * x) / (1 + Real.sin (4 * x))) /
      (1 / Real.cos x ^ 2)) (𝓝[>] 0) (𝓝 4) := by
  have hcos : Tendsto Real.cos (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hfour : Tendsto (fun x : ℝ ↦ 4 * x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq, mul_zero] using
      (continuous_id.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).const_mul 4
  have hcos4 : Tendsto (fun x : ℝ ↦ Real.cos (4 * x)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hfour
  have hnum : Tendsto (fun x : ℝ ↦ 4 * Real.cos (4 * x)) (𝓝[>] 0) (𝓝 4) := by
    simpa only [mul_one] using hcos4.const_mul 4
  have hden : Tendsto (fun x : ℝ ↦ 1 / Real.cos x ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds.div (hcos.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0))
  simpa only [Pi.div_def, div_one] using
    (hnum.div sine_four_base_right one_ne_zero).div hden one_ne_zero


theorem logarithm_div_tangent_right :
    Tendsto (fun x : ℝ ↦ Real.log (1 + Real.sin (4 * x)) / Real.tan x)
      (𝓝[>] 0) (𝓝 4) := by
  have hlog (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (Real.pi / 8)) :
      HasDerivAt (fun y : ℝ ↦ Real.log (1 + Real.sin (4 * y)))
        (4 * Real.cos (4 * x) / (1 + Real.sin (4 * x))) x :=
    (sine_four_base_hasDerivAt x).log (sine_four_local_domain hx).1.ne'
  have htan (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (Real.pi / 8)) :
      HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
    Real.hasDerivAt_tan (sine_four_local_domain hx).2.1.ne'
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (by positivity : (0 : ℝ) < Real.pi / 8) hlog htan
  · intro x hx
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 (sine_four_local_domain hx).2.1.ne')
  · have hd : HasDerivAt (fun x : ℝ ↦ Real.log (1 + Real.sin (4 * x))) 4 0 := by
      convert (sine_four_base_hasDerivAt 0).log
        (by norm_num : 1 + Real.sin (4 * (0 : ℝ)) ≠ 0) using 1; norm_num
    simpa only [mul_zero, Real.sin_zero, add_zero, Real.log_one] using
      hd.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · simpa only [Real.tan_zero] using
      (Real.hasDerivAt_tan (by simp : Real.cos (0 : ℝ) ≠ 0)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · exact sine_power_derivative_ratio_right


theorem sine_power_log_eventually_eq :
    ∀ᶠ x : ℝ in 𝓝[>] 0,
      Real.log ((1 + Real.sin (4 * x)) ^ Real.cot x) =
        Real.log (1 + Real.sin (4 * x)) / Real.tan x := by
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 8)] with x hx
  rw [Real.log_rpow (sine_four_local_domain hx).1, ← Real.tan_inv_eq_cot,
    div_eq_mul_inv]
  ring


theorem source_sine_power_log_right :
    Tendsto (fun x : ℝ ↦ Real.log ((1 + Real.sin (4 * x)) ^ Real.cot x))
      (𝓝[>] 0) (𝓝 4) := by
  apply logarithm_div_tangent_right.congr'
  filter_upwards [sine_power_log_eventually_eq] with x hx
  exact hx.symm

/-- Ví dụ 7: `(1 + sin 4x)^(cot x) → exp 4` khi `x → 0⁺`. -/
theorem source_sine_power_right :
    Tendsto (fun x : ℝ ↦ (1 + Real.sin (4 * x)) ^ Real.cot x)
      (𝓝[>] 0) (𝓝 (Real.exp 4)) := by
  have he : Tendsto (fun x : ℝ ↦ Real.exp
      (Real.log ((1 + Real.sin (4 * x)) ^ Real.cot x)))
      (𝓝[>] 0) (𝓝 (Real.exp 4)) :=
    Real.continuous_exp.continuousAt.tendsto.comp source_sine_power_log_right
  apply he.congr'
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 8)] with x hx
  exact Real.exp_log (Real.rpow_pos_of_pos (sine_four_local_domain hx).1 (Real.cot x))

end calculus.Chapter04.Section04ElementaryLimitExamples
