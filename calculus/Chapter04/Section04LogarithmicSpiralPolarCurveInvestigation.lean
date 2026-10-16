import calculus.Chapter04.Section04PolarEquations
import calculus.Chapter04.Section04PolarTangents
import calculus.Chapter04.Section04ArchimedeanSpiralPolarCurveInvestigation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 16(f): đường xoắn logarit

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2798, `r=a exp(bφ)`, với `a,b,φ∈ℝ`. Bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04LogarithmicSpiralPolarCurveInvestigation
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04ArchimedeanSpiralPolarCurveInvestigation

def logarithmicRadius (a b t : ℝ) : ℝ := a * Real.exp (b*t)
def logarithmicPoint (a b t : ℝ) : ℂ := signedPolarPoint (logarithmicRadius a b t) t
def logarithmicCurve (a b : ℝ) : Set ℂ := polarCurveImage (logarithmicRadius a b)
def logarithmicDX (a b t : ℝ) : ℝ := logarithmicRadius a b t * (b*Real.cos t-Real.sin t)
def logarithmicDY (a b t : ℝ) : ℝ := logarithmicRadius a b t * (b*Real.sin t+Real.cos t)
def logarithmicDDX (a b t : ℝ) : ℝ :=
  logarithmicRadius a b t * ((b^2-1)*Real.cos t-2*b*Real.sin t)
def logarithmicDDY (a b t : ℝ) : ℝ :=
  logarithmicRadius a b t * ((b^2-1)*Real.sin t+2*b*Real.cos t)

theorem logarithmic_complete_image (a b : ℝ) (z : ℂ) :
    z ∈ logarithmicCurve a b ↔ ∃ t : ℝ,
      z.re = a*Real.exp (b*t)*Real.cos t ∧ z.im = a*Real.exp (b*t)*Real.sin t := by
  rw [logarithmicCurve, source_polar_explicit_membership]
  apply exists_congr
  intro t
  exact signed_polar_equation_coordinates (a*Real.exp (b*t)) t z

theorem logarithmic_zero_scale (b : ℝ) : logarithmicCurve 0 b = {0} := by
  ext z
  rw [logarithmic_complete_image, mem_singleton_iff]
  constructor
  · rintro ⟨t, hx, hy⟩
    apply Complex.ext
    · simpa using hx
    · simpa using hy
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

theorem logarithmic_zero_rate_circle (a : ℝ) (z : ℂ) :
    z ∈ logarithmicCurve a 0 ↔ ‖z‖ = |a| := by
  have he : logarithmicRadius a 0 = (fun _ : ℝ ↦ a) := by
    funext t
    simp [logarithmicRadius]
  rw [logarithmicCurve, he]
  exact constant_radius_locus a z

theorem logarithmic_radius_distance (a b t : ℝ) :
    ‖logarithmicPoint a b t‖ = |a| * Real.exp (b*t) := by
  rw [logarithmicPoint, norm_signedPolarPoint, logarithmicRadius, abs_mul,
    abs_of_pos (Real.exp_pos _)]

theorem logarithmic_origin_iff (a b t : ℝ) : logarithmicPoint a b t = 0 ↔ a = 0 := by
  rw [logarithmicPoint, signedPolarPoint_eq_zero_iff, logarithmicRadius,
    mul_eq_zero, or_iff_left (Real.exp_ne_zero _)]

theorem logarithmic_actual_first_derivatives (a b t : ℝ) :
    HasDerivAt (logarithmicRadius a b) (b*logarithmicRadius a b t) t ∧
      HasDerivAt (polarX (logarithmicRadius a b)) (logarithmicDX a b t) t ∧
      HasDerivAt (polarY (logarithmicRadius a b)) (logarithmicDY a b t) t := by
  have hr : HasDerivAt (logarithmicRadius a b) (b*logarithmicRadius a b t) t := by
    have h := (((hasDerivAt_id t).const_mul b).exp).const_mul a
    apply h.congr_deriv
    simp only [id_eq, mul_one, logarithmicRadius]
    ring
  refine ⟨hr, (polarX_hasDerivAt hr).congr_deriv ?_, (polarY_hasDerivAt hr).congr_deriv ?_⟩
  · unfold logarithmicDX
    ring
  · unfold logarithmicDY
    ring

theorem logarithmic_derivative_functions (a b : ℝ) :
    deriv (polarX (logarithmicRadius a b)) = logarithmicDX a b ∧
      deriv (polarY (logarithmicRadius a b)) = logarithmicDY a b := by
  exact ⟨funext (fun t ↦ (logarithmic_actual_first_derivatives a b t).2.1.deriv),
    funext (fun t ↦ (logarithmic_actual_first_derivatives a b t).2.2.deriv)⟩

theorem logarithmic_actual_second_derivatives (a b t : ℝ) :
    HasDerivAt (deriv (polarX (logarithmicRadius a b))) (logarithmicDDX a b t) t ∧
      HasDerivAt (deriv (polarY (logarithmicRadius a b))) (logarithmicDDY a b t) t := by
  rw [(logarithmic_derivative_functions a b).1, (logarithmic_derivative_functions a b).2]
  have hr := (logarithmic_actual_first_derivatives a b t).1
  constructor
  · have h := hr.fun_mul (((Real.hasDerivAt_cos t).const_mul b).fun_sub (Real.hasDerivAt_sin t))
    apply h.congr_deriv
    unfold logarithmicDDX
    ring
  · have h := hr.fun_mul (((Real.hasDerivAt_sin t).const_mul b).fun_add (Real.hasDerivAt_cos t))
    apply h.congr_deriv
    unfold logarithmicDDY
    ring

theorem logarithmic_velocity_square (a b t : ℝ) :
    (logarithmicDX a b t)^2+(logarithmicDY a b t)^2 =
      (logarithmicRadius a b t)^2*(b^2+1) := by
  unfold logarithmicDX logarithmicDY
  nlinarith [congrArg (fun q : ℝ ↦ (logarithmicRadius a b t)^2*q)
      (Real.sin_sq_add_cos_sq t),
    congrArg (fun q : ℝ ↦ (logarithmicRadius a b t)^2*b^2*q)
      (Real.sin_sq_add_cos_sq t)]

theorem logarithmic_regular_iff (a b t : ℝ) :
    logarithmicDX a b t ≠ 0 ∨ logarithmicDY a b t ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha
    rcases h with h | h <;> apply h <;> simp [ha, logarithmicRadius, logarithmicDX, logarithmicDY]
  · intro ha
    by_contra h
    push Not at h
    have hv := logarithmic_velocity_square a b t
    rw [h.1,h.2] at hv
    have hr : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
    have hp := mul_pos (sq_pos_of_ne_zero hr) (by nlinarith [sq_nonneg b] : 0 < b^2+1)
    nlinarith

theorem logarithmic_curvature_numerator (a b t : ℝ) :
    deriv (polarX (logarithmicRadius a b)) t * deriv (deriv (polarY (logarithmicRadius a b))) t -
      deriv (deriv (polarX (logarithmicRadius a b))) t * deriv (polarY (logarithmicRadius a b)) t =
        (logarithmicRadius a b t)^2*(1+b^2) := by
  rw [(logarithmic_actual_first_derivatives a b t).2.1.deriv,
    (logarithmic_actual_first_derivatives a b t).2.2.deriv,
    (logarithmic_actual_second_derivatives a b t).1.deriv,
    (logarithmic_actual_second_derivatives a b t).2.deriv]
  unfold logarithmicDX logarithmicDY logarithmicDDX logarithmicDDY
  nlinarith [congrArg (fun q : ℝ ↦ (logarithmicRadius a b t)^2*q)
      (Real.sin_sq_add_cos_sq t),
    congrArg (fun q : ℝ ↦ (logarithmicRadius a b t)^2*b^2*q)
      (Real.sin_sq_add_cos_sq t)]

theorem logarithmic_curvature_numerator_positive {a : ℝ} (ha : a ≠ 0) (b t : ℝ) :
    0 < (logarithmicRadius a b t)^2*(1+b^2) := by
  have hr : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
  exact mul_pos (sq_pos_of_ne_zero hr) (by nlinarith [sq_nonneg b])


theorem logarithmic_radial_tangent_angle (a b t : ℝ) :
    (logarithmicPoint a b t).re * logarithmicDX a b t +
      (logarithmicPoint a b t).im * logarithmicDY a b t = b*(logarithmicRadius a b t)^2 ∧
    (logarithmicPoint a b t).re * logarithmicDY a b t -
      (logarithmicPoint a b t).im * logarithmicDX a b t = (logarithmicRadius a b t)^2 := by
  simp only [logarithmicPoint, signedPolarPoint_re, signedPolarPoint_im]
  unfold logarithmicDX logarithmicDY
  constructor
  · nlinarith [congrArg (fun q : ℝ ↦ b*(logarithmicRadius a b t)^2*q)
      (Real.sin_sq_add_cos_sq t)]
  · nlinarith [congrArg (fun q : ℝ ↦ (logarithmicRadius a b t)^2*q)
      (Real.sin_sq_add_cos_sq t)]

theorem logarithmic_turn_dilation (a b t : ℝ) :
    logarithmicPoint a b (t+2*Real.pi) =
      (Real.exp (2*Real.pi*b) : ℂ)*logarithmicPoint a b t := by
  apply Complex.ext
  · simp only [logarithmicPoint, signedPolarPoint_re, logarithmicRadius,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Real.cos_add_two_pi]
    rw [show b*(t+2*Real.pi)=b*t+2*Real.pi*b by ring,Real.exp_add]
    ring
  · simp only [logarithmicPoint, signedPolarPoint_im, logarithmicRadius,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Real.sin_add_two_pi]
    rw [show b*(t+2*Real.pi)=b*t+2*Real.pi*b by ring,Real.exp_add]
    ring

theorem logarithmic_distance_monotonicity {a b : ℝ} (ha : a ≠ 0) :
    (0 < b → StrictMono (fun t : ℝ ↦ ‖logarithmicPoint a b t‖)) ∧
      (b < 0 → StrictAnti (fun t : ℝ ↦ ‖logarithmicPoint a b t‖)) := by
  constructor
  · intro hb s t hst
    simp only [logarithmic_radius_distance]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hst hb)) (abs_pos.mpr ha)
  · intro hb s t hst
    simp only [logarithmic_radius_distance]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hst hb)) (abs_pos.mpr ha)

theorem logarithmic_parameter_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (logarithmicPoint a b) := by
  intro s t hp
  have hn := congrArg (fun z : ℂ ↦ ‖z‖) hp
  rcases lt_or_gt_of_ne hb with hb | hb
  · exact (logarithmic_distance_monotonicity ha).2 hb |>.injective hn
  · exact (logarithmic_distance_monotonicity ha).1 hb |>.injective hn


theorem logarithmic_inverse_parameter {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (t : ℝ) :
    Real.log (‖logarithmicPoint a b t‖/|a|)/b=t := by
  rw [logarithmic_radius_distance,mul_div_cancel_left₀ _ (abs_ne_zero.mpr ha),Real.log_exp]
  exact mul_div_cancel_left₀ t hb

theorem logarithmic_complete_inverse_image {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (z : ℂ) :
    z ∈ logarithmicCurve a b ↔ z ≠ 0 ∧
      logarithmicPoint a b (Real.log (‖z‖/|a|)/b)=z := by
  rw [logarithmicCurve,source_polar_explicit_membership]
  constructor
  · rintro ⟨t,hp⟩
    change logarithmicPoint a b t=z at hp
    refine ⟨by rw [← hp]; exact (logarithmic_origin_iff a b t).not.mpr ha,?_⟩
    rw [← hp,logarithmic_inverse_parameter ha hb]
  · rintro ⟨_,hp⟩
    exact ⟨Real.log (‖z‖/|a|)/b,hp⟩


theorem logarithmic_distance_end_limits {a b : ℝ} (ha : a ≠ 0) :
    (0 < b → Tendsto (fun t : ℝ ↦ ‖logarithmicPoint a b t‖) atTop atTop ∧
      Tendsto (logarithmicPoint a b) atBot (𝓝 0)) ∧
    (b < 0 → Tendsto (logarithmicPoint a b) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ ↦ ‖logarithmicPoint a b t‖) atBot atTop) := by
  have hnorm {F : Filter ℝ} (he : Tendsto (fun t : ℝ ↦ Real.exp (b*t)) F (𝓝 0)) :
      Tendsto (logarithmicPoint a b) F (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [logarithmic_radius_distance,mul_zero] using! he.const_mul |a|
  have hinfty {F : Filter ℝ} (he : Tendsto (fun t : ℝ ↦ Real.exp (b*t)) F atTop) :
      Tendsto (fun t : ℝ ↦ ‖logarithmicPoint a b t‖) F atTop := by
    simpa only [logarithmic_radius_distance] using! he.const_mul_atTop (abs_pos.mpr ha)
  constructor
  · intro hb
    have hT : Tendsto (fun t : ℝ ↦ b*t) atTop atTop := tendsto_id.const_mul_atTop hb
    have hB : Tendsto (fun t : ℝ ↦ b*t) atBot atBot := tendsto_id.const_mul_atBot hb
    exact ⟨hinfty (Real.tendsto_exp_atTop.comp hT),hnorm (Real.tendsto_exp_atBot.comp hB)⟩
  · intro hb
    have hT : Tendsto (fun t : ℝ ↦ b*t) atTop atBot := tendsto_id.const_mul_atTop_of_neg hb
    have hB : Tendsto (fun t : ℝ ↦ b*t) atBot atTop := tendsto_id.const_mul_atBot_of_neg hb
    exact ⟨hnorm (Real.tendsto_exp_atBot.comp hT),hinfty (Real.tendsto_exp_atTop.comp hB)⟩

theorem logarithmic_axis_intersections {a : ℝ} (ha : a ≠ 0) (b t : ℝ) :
    ((logarithmicPoint a b t).re=0 ↔ Real.cos t=0) ∧
      ((logarithmicPoint a b t).im=0 ↔ Real.sin t=0) := by
  have hr : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
  simp only [logarithmicPoint,signedPolarPoint_re,signedPolarPoint_im,mul_eq_zero,hr,false_or]
  trivial



theorem logarithmic_horizontal_tangent_iff {a b t : ℝ} (ha : a ≠ 0)
    (hx : logarithmicDX a b t ≠ 0) :
    HasHorizontalPolarTangent univ (logarithmicRadius a b) t ↔
      b*Real.sin t+Real.cos t=0 := by
  have hr : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
  have hx' : b*logarithmicRadius a b t*Real.cos t-logarithmicRadius a b t*Real.sin t ≠ 0 := by
    convert hx using 1
    unfold logarithmicDX
    ring
  rw [horizontal_polar_tangent_iff (by simp)
    (logarithmic_actual_first_derivatives a b t).1 hx']
  rw [show b*logarithmicRadius a b t*Real.sin t+logarithmicRadius a b t*Real.cos t=
    logarithmicRadius a b t*(b*Real.sin t+Real.cos t) by ring,mul_eq_zero,or_iff_right hr]


theorem logarithmic_vertical_tangent_iff {a b t : ℝ} (ha : a ≠ 0)
    (hy : logarithmicDY a b t ≠ 0) :
    HasVerticalPolarTangent univ (logarithmicRadius a b) t ↔
      b*Real.cos t-Real.sin t=0 := by
  have hr : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
  have hy' : b*logarithmicRadius a b t*Real.sin t+logarithmicRadius a b t*Real.cos t ≠ 0 := by
    convert hy using 1
    unfold logarithmicDY
    ring
  rw [vertical_polar_tangent_iff (by simp)
    (logarithmic_actual_first_derivatives a b t).1 hy']
  rw [show b*logarithmicRadius a b t*Real.cos t-logarithmicRadius a b t*Real.sin t=
    logarithmicRadius a b t*(b*Real.cos t-Real.sin t) by ring,mul_eq_zero,or_iff_right hr]


theorem logarithmic_no_affine_asymptote_at_escaping_end {a b : ℝ} (ha : a ≠ 0)
    (u v w : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    (0 < b → ¬ Tendsto (fun t : ℝ ↦ u*(logarithmicPoint a b t).re+
      v*(logarithmicPoint a b t).im+w) atTop (𝓝 0)) ∧
    (b < 0 → ¬ Tendsto (fun t : ℝ ↦ u*(logarithmicPoint a b t).re+
      v*(logarithmicPoint a b t).im+w) atBot (𝓝 0)) := by
  have hn (t : ℝ) : logarithmicRadius a b t ≠ 0 := mul_ne_zero ha (Real.exp_ne_zero _)
  have hi {F : Filter ℝ} (h : Tendsto (fun t : ℝ ↦ Real.exp (b*t)) F atTop) :
      Tendsto (fun t : ℝ ↦ (logarithmicRadius a b t)⁻¹) F (𝓝 0) := by
    simpa only [logarithmicRadius,mul_inv_rev,Pi.inv_apply,zero_mul] using!
      h.inv_tendsto_atTop.mul_const a⁻¹
  constructor
  · intro hb
    have he := Real.tendsto_exp_atTop.comp
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop).const_mul_atTop hb)
    simpa only [logarithmicPoint,signedPolarPoint_re,signedPolarPoint_im] using!
      rotating_radius_no_affine_residual_atTop (hi he) (Filter.Eventually.of_forall hn) u v w huv
  · intro hb
    have he := Real.tendsto_exp_atTop.comp
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) atBot atBot).const_mul_atBot_of_neg hb)
    simpa only [logarithmicPoint,signedPolarPoint_re,signedPolarPoint_im] using!
      rotating_radius_no_affine_residual_atBot (hi he) (Filter.Eventually.of_forall hn) u v w huv

theorem source_logarithmic_polar_curve_investigation (a b : ℝ) :
    (∀ z : ℂ, z ∈ logarithmicCurve a b ↔ ∃ t : ℝ,
      z.re=a*Real.exp (b*t)*Real.cos t ∧ z.im=a*Real.exp (b*t)*Real.sin t) ∧
    (a=0 → logarithmicCurve a b={0}) ∧
    (b=0 → ∀ z : ℂ, z ∈ logarithmicCurve a b ↔ ‖z‖=|a|) ∧
    (∀ t : ℝ, HasDerivAt (logarithmicRadius a b) (b*logarithmicRadius a b t) t ∧
      HasDerivAt (polarX (logarithmicRadius a b)) (logarithmicDX a b t) t ∧
      HasDerivAt (polarY (logarithmicRadius a b)) (logarithmicDY a b t) t) ∧
    (∀ t : ℝ, logarithmicDX a b t ≠ 0 ∨ logarithmicDY a b t ≠ 0 ↔ a≠0) ∧
    (a≠0 → b≠0 → Function.Injective (logarithmicPoint a b)) ∧
    (∀ t : ℝ, logarithmicPoint a b (t+2*Real.pi)=
      (Real.exp (2*Real.pi*b) : ℂ)*logarithmicPoint a b t) := by
  refine ⟨logarithmic_complete_image a b,fun ha ↦ ha ▸ logarithmic_zero_scale b,?_,
    logarithmic_actual_first_derivatives a b,logarithmic_regular_iff a b,
    fun ha hb ↦ logarithmic_parameter_injective ha hb,logarithmic_turn_dilation a b⟩
  rintro rfl
  exact logarithmic_zero_rate_circle a

end calculus.Chapter04.Section04LogarithmicSpiralPolarCurveInvestigation
