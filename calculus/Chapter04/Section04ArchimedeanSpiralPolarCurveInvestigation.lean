import calculus.Chapter04.Section04PolarEquations
import calculus.Chapter04.Section04PolarTangents
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 16(e): đường xoắn r=aφ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2797. Tham số và góc là số thực tùy ý; bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04ArchimedeanSpiralPolarCurveInvestigation
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarTangents


def archimedeanRadius (a t : ℝ) : ℝ := a * t
def archimedeanPoint (a t : ℝ) : ℂ := signedPolarPoint (archimedeanRadius a t) t
def archimedeanCurve (a : ℝ) : Set ℂ := polarCurveImage (archimedeanRadius a)
def archimedeanDX (a t : ℝ) : ℝ := a * (Real.cos t - t * Real.sin t)
def archimedeanDY (a t : ℝ) : ℝ := a * (Real.sin t + t * Real.cos t)
def archimedeanDDX (a t : ℝ) : ℝ := a * (-2 * Real.sin t - t * Real.cos t)
def archimedeanDDY (a t : ℝ) : ℝ := a * (2 * Real.cos t - t * Real.sin t)


theorem archimedean_complete_image (a : ℝ) (z : ℂ) :
    z ∈ archimedeanCurve a ↔
      ∃ t : ℝ, z.re = a * t * Real.cos t ∧ z.im = a * t * Real.sin t := by
  rw [archimedeanCurve, source_polar_explicit_membership]
  apply exists_congr
  intro t
  exact signed_polar_equation_coordinates (a * t) t z

theorem archimedean_zero_scale : archimedeanCurve 0 = {0} := by
  ext z
  rw [archimedean_complete_image, mem_singleton_iff]
  constructor
  · rintro ⟨t, hx, hy⟩
    apply Complex.ext
    · simpa using hx
    · simpa using hy
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

theorem archimedean_actual_first_derivatives (a t : ℝ) :
    HasDerivAt (archimedeanRadius a) a t ∧
      HasDerivAt (polarX (archimedeanRadius a)) (archimedeanDX a t) t ∧
      HasDerivAt (polarY (archimedeanRadius a)) (archimedeanDY a t) t := by
  have hr : HasDerivAt (archimedeanRadius a) a t := by
    simpa only [archimedeanRadius, id_eq, mul_one] using! (hasDerivAt_id t).const_mul a
  refine ⟨hr, (polarX_hasDerivAt hr).congr_deriv ?_, (polarY_hasDerivAt hr).congr_deriv ?_⟩
  · unfold archimedeanRadius archimedeanDX
    ring
  · unfold archimedeanRadius archimedeanDY
    ring

theorem archimedean_derivative_functions (a : ℝ) :
    deriv (polarX (archimedeanRadius a)) = archimedeanDX a ∧
      deriv (polarY (archimedeanRadius a)) = archimedeanDY a := by
  exact ⟨funext (fun t ↦ (archimedean_actual_first_derivatives a t).2.1.deriv),
    funext (fun t ↦ (archimedean_actual_first_derivatives a t).2.2.deriv)⟩

theorem archimedean_actual_second_derivatives (a t : ℝ) :
    HasDerivAt (deriv (polarX (archimedeanRadius a))) (archimedeanDDX a t) t ∧
      HasDerivAt (deriv (polarY (archimedeanRadius a))) (archimedeanDDY a t) t := by
  rw [(archimedean_derivative_functions a).1, (archimedean_derivative_functions a).2]
  constructor
  · have h := ((Real.hasDerivAt_cos t).fun_sub
      ((hasDerivAt_id t).fun_mul (Real.hasDerivAt_sin t))).const_mul a
    apply h.congr_deriv
    simp only [id_eq, one_mul, archimedeanDDX]
    ring
  · have h := ((Real.hasDerivAt_sin t).fun_add
      ((hasDerivAt_id t).fun_mul (Real.hasDerivAt_cos t))).const_mul a
    apply h.congr_deriv
    simp only [id_eq, one_mul, archimedeanDDY]
    ring

theorem archimedean_velocity_square (a t : ℝ) :
    (archimedeanDX a t)^2 + (archimedeanDY a t)^2 = a^2 * (1 + t^2) := by
  unfold archimedeanDX archimedeanDY
  nlinarith [congrArg (fun q : ℝ ↦ a^2 * q) (Real.sin_sq_add_cos_sq t),
    congrArg (fun q : ℝ ↦ a^2 * t^2 * q) (Real.sin_sq_add_cos_sq t)]


theorem archimedean_regular_iff (a t : ℝ) :
    archimedeanDX a t ≠ 0 ∨ archimedeanDY a t ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha
    rcases h with h | h <;> apply h <;> simp [ha, archimedeanDX, archimedeanDY]
  · intro ha
    by_contra h
    push Not at h
    have hv := archimedean_velocity_square a t
    rw [h.1, h.2] at hv
    have hp := mul_pos (sq_pos_of_ne_zero ha) (by nlinarith [sq_nonneg t] : 0 < 1 + t^2)
    nlinarith

theorem archimedean_curvature_numerator (a t : ℝ) :
    deriv (polarX (archimedeanRadius a)) t * deriv (deriv (polarY (archimedeanRadius a))) t -
      deriv (deriv (polarX (archimedeanRadius a))) t * deriv (polarY (archimedeanRadius a)) t =
        a^2 * (t^2 + 2) := by
  rw [(archimedean_actual_first_derivatives a t).2.1.deriv,
    (archimedean_actual_first_derivatives a t).2.2.deriv,
    (archimedean_actual_second_derivatives a t).1.deriv,
    (archimedean_actual_second_derivatives a t).2.deriv]
  unfold archimedeanDX archimedeanDY archimedeanDDX archimedeanDDY
  nlinarith [congrArg (fun q : ℝ ↦ a^2*t^2*q) (Real.sin_sq_add_cos_sq t),
    congrArg (fun q : ℝ ↦ 2*a^2*q) (Real.sin_sq_add_cos_sq t)]

theorem archimedean_curvature_numerator_positive {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    0 < a^2 * (t^2 + 2) :=
  mul_pos (sq_pos_of_ne_zero ha) (by nlinarith [sq_nonneg t])


theorem archimedean_reflection (a t : ℝ) :
    (archimedeanPoint a (-t)).re = -(archimedeanPoint a t).re ∧
      (archimedeanPoint a (-t)).im = (archimedeanPoint a t).im := by
  simp only [archimedeanPoint, archimedeanRadius, signedPolarPoint_re, signedPolarPoint_im,
    Real.cos_neg, Real.sin_neg]
  constructor <;> ring

theorem archimedean_radius_distance (a t : ℝ) :
    ‖archimedeanPoint a t‖ = |a| * |t| := by
  rw [archimedeanPoint, norm_signedPolarPoint, archimedeanRadius, abs_mul]

theorem archimedean_origin_iff {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    archimedeanPoint a t = 0 ↔ t = 0 := by
  rw [archimedeanPoint, signedPolarPoint_eq_zero_iff, archimedeanRadius,
    mul_eq_zero, or_iff_right ha]


theorem archimedean_selfintersection_iff {a : ℝ} (ha : a ≠ 0) (s t : ℝ) :
    s ≠ t ∧ archimedeanPoint a s = archimedeanPoint a t ↔
      s = -t ∧ t ≠ 0 ∧ Real.cos t = 0 := by
  constructor
  · rintro ⟨hst, hp⟩
    have hn := congrArg (fun z : ℂ ↦ ‖z‖) hp
    rw [archimedean_radius_distance, archimedean_radius_distance] at hn
    have habs : |s| = |t| := (mul_left_cancel₀ (abs_ne_zero.mpr ha) hn)
    rcases (abs_eq_abs.mp habs) with he | he
    · exact False.elim (hst he)
    · have hs : s = -t := he
      have ht : t ≠ 0 := by intro ht; apply hst; simp [hs, ht]
      have hx := congrArg Complex.re hp
      rw [hs, (archimedean_reflection a t).1] at hx
      have hz : (archimedeanPoint a t).re = 0 := by linarith
      have hprod : (a*t)*Real.cos t = 0 := by simpa only [archimedeanPoint, archimedeanRadius, signedPolarPoint_re] using hz
      exact ⟨hs, ht, (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ha ht)⟩
  · rintro ⟨rfl, ht, hc⟩
    refine ⟨by intro h; apply ht; linarith, ?_⟩
    apply Complex.ext
    · rw [(archimedean_reflection a t).1]
      simp only [archimedeanPoint, signedPolarPoint_re, hc, mul_zero, neg_zero]
    · exact (archimedean_reflection a t).2

theorem archimedean_turn_spacing (a t : ℝ) :
    archimedeanRadius a (t + 2*Real.pi) - archimedeanRadius a t = 2*Real.pi*a := by
  unfold archimedeanRadius
  ring

theorem archimedean_radius_monotonicity {a : ℝ} :
    (0 < a → StrictMono (archimedeanRadius a)) ∧
      (a < 0 → StrictAnti (archimedeanRadius a)) := by
  constructor
  · intro ha s t hst
    exact mul_lt_mul_of_pos_left hst ha
  · intro ha s t hst
    exact mul_lt_mul_of_neg_left hst ha

theorem archimedean_distance_infinite_ends {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun t : ℝ ↦ ‖archimedeanPoint a t‖) atTop atTop ∧
      Tendsto (fun t : ℝ ↦ ‖archimedeanPoint a t‖) atBot atTop := by
  have hT : Tendsto (fun t : ℝ ↦ |a| * t) atTop atTop :=
    (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop).const_mul_atTop (abs_pos.mpr ha)
  have hB : Tendsto (fun t : ℝ ↦ |a| * (-t)) atBot atTop := by
    exact hT.comp tendsto_neg_atBot_atTop
  constructor
  · apply hT.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [archimedean_radius_distance, abs_of_pos ht]
  · apply hB.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    rw [archimedean_radius_distance, abs_of_neg ht]

theorem archimedean_origin_tangent {a : ℝ} (ha : a ≠ 0) :
    HasHorizontalPolarTangent univ (archimedeanRadius a) 0 := by
  apply source_horizontal_polar_tangent (by simp) (archimedean_actual_first_derivatives a 0).1
  · simp [archimedeanRadius]
  · simpa [archimedeanRadius] using ha


theorem archimedean_horizontal_tangent_iff {a t : ℝ} (ha : a ≠ 0)
    (hx : archimedeanDX a t ≠ 0) :
    HasHorizontalPolarTangent univ (archimedeanRadius a) t ↔
      Real.sin t + t * Real.cos t = 0 := by
  have hx' : a * Real.cos t - archimedeanRadius a t * Real.sin t ≠ 0 := by
    convert hx using 1
    unfold archimedeanRadius archimedeanDX
    ring
  rw [horizontal_polar_tangent_iff (by simp)
    (archimedean_actual_first_derivatives a t).1 hx']
  have he : a * Real.sin t + archimedeanRadius a t * Real.cos t =
      a * (Real.sin t + t * Real.cos t) := by unfold archimedeanRadius; ring
  rw [he, mul_eq_zero, or_iff_right ha]


theorem archimedean_vertical_tangent_iff {a t : ℝ} (ha : a ≠ 0)
    (hy : archimedeanDY a t ≠ 0) :
    HasVerticalPolarTangent univ (archimedeanRadius a) t ↔
      Real.cos t - t * Real.sin t = 0 := by
  have hy' : a * Real.sin t + archimedeanRadius a t * Real.cos t ≠ 0 := by
    convert hy using 1
    unfold archimedeanRadius archimedeanDY
    ring
  rw [vertical_polar_tangent_iff (by simp)
    (archimedean_actual_first_derivatives a t).1 hy']
  have he : a * Real.cos t - archimedeanRadius a t * Real.sin t =
      a * (Real.cos t - t * Real.sin t) := by unfold archimedeanRadius; ring
  rw [he, mul_eq_zero, or_iff_right ha]


theorem archimedean_axis_intersections {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    ((archimedeanPoint a t).re = 0 ↔ t = 0 ∨ Real.cos t = 0) ∧
      ((archimedeanPoint a t).im = 0 ↔ t = 0 ∨ Real.sin t = 0) := by
  simp only [archimedeanPoint, signedPolarPoint_re, signedPolarPoint_im,
    archimedeanRadius, mul_eq_zero, ha, false_or]
  trivial


theorem archimedean_double_point_transverse {a t : ℝ} (ha : a ≠ 0)
    (ht : t ≠ 0) (hc : Real.cos t = 0) :
    archimedeanDX a t * archimedeanDY a (-t) -
      archimedeanDY a t * archimedeanDX a (-t) = 2*a^2*t ∧
      2*a^2*t ≠ 0 := by
  have hs : Real.sin t ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  constructor
  · unfold archimedeanDX archimedeanDY
    rw [Real.cos_neg, Real.sin_neg, hc]
    nlinarith [congrArg (fun q : ℝ ↦ 2*a^2*t*q) hs]
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) ht



theorem rotating_radius_no_affine_residual_atTop {r : ℝ → ℝ}
    (hi : Tendsto (fun t : ℝ ↦ (r t)⁻¹) atTop (𝓝 0))
    (hn : ∀ᶠ t : ℝ in atTop, r t ≠ 0) (u v w : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    ¬ Tendsto (fun t : ℝ ↦ u*(r t*Real.cos t)+v*(r t*Real.sin t)+w)
      atTop (𝓝 0) := by
  intro h
  have hq : Tendsto (fun t : ℝ ↦ u*Real.cos t+v*Real.sin t+w*(r t)⁻¹)
      atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ ↦
      (u*(r t*Real.cos t)+v*(r t*Real.sin t)+w)*(r t)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using! h.mul hi
    apply hh.congr'
    filter_upwards [hn] with t ht
    field_simp [ht]
  have hphase (φ : ℝ) : u*Real.cos φ+v*Real.sin φ=0 := by
    have ht : Tendsto (fun n : ℕ ↦ φ+(n : ℝ)*(2*Real.pi)) atTop atTop :=
      tendsto_atTop_add_const_left atTop φ
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity))
    have hc : Tendsto (fun n : ℕ ↦ u*Real.cos φ+v*Real.sin φ+
      w*(r (φ+(n : ℝ)*(2*Real.pi)))⁻¹) atTop (𝓝 (u*Real.cos φ+v*Real.sin φ)) := by
      simpa only [mul_zero,add_zero] using!
        ((hi.comp ht).const_mul w).const_add (u*Real.cos φ+v*Real.sin φ)
    have hz : Tendsto (fun n : ℕ ↦ u*Real.cos φ+v*Real.sin φ+
      w*(r (φ+(n : ℝ)*(2*Real.pi)))⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Real.cos_add_nat_mul_two_pi,
        Real.sin_add_nat_mul_two_pi] using! hq.comp ht
    exact tendsto_nhds_unique hc hz
  have hu : u=0 := by simpa only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] using hphase 0
  have hv : v=0 := by simpa only [Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_add] using hphase (Real.pi/2)
  rcases huv with h | h
  · exact h hu
  · exact h hv


theorem rotating_radius_no_affine_residual_atBot {r : ℝ → ℝ}
    (hi : Tendsto (fun t : ℝ ↦ (r t)⁻¹) atBot (𝓝 0))
    (hn : ∀ᶠ t : ℝ in atBot, r t ≠ 0) (u v w : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    ¬ Tendsto (fun t : ℝ ↦ u*(r t*Real.cos t)+v*(r t*Real.sin t)+w)
      atBot (𝓝 0) := by
  intro h
  have hi' : Tendsto (fun t : ℝ ↦ (r (-t))⁻¹) atTop (𝓝 0) :=
    hi.comp tendsto_neg_atTop_atBot
  have hn' : ∀ᶠ t : ℝ in atTop, r (-t) ≠ 0 := tendsto_neg_atTop_atBot.eventually hn
  have hv : u ≠ 0 ∨ -v ≠ 0 := huv.imp id neg_ne_zero.mpr
  apply rotating_radius_no_affine_residual_atTop hi' hn' u (-v) w hv
  simpa only [Function.comp_def,Real.cos_neg,Real.sin_neg,mul_neg,neg_mul] using!
    h.comp tendsto_neg_atTop_atBot


theorem archimedean_no_affine_asymptote {a : ℝ} (ha : a ≠ 0)
    (u v w : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    (¬ Tendsto (fun t : ℝ ↦ u*(archimedeanPoint a t).re+v*(archimedeanPoint a t).im+w)
      atTop (𝓝 0)) ∧
    (¬ Tendsto (fun t : ℝ ↦ u*(archimedeanPoint a t).re+v*(archimedeanPoint a t).im+w)
      atBot (𝓝 0)) := by
  have hi {F : Filter ℝ} (h : Tendsto (fun t : ℝ ↦ t⁻¹) F (𝓝 0)) :
      Tendsto (fun t : ℝ ↦ (archimedeanRadius a t)⁻¹) F (𝓝 0) := by
    simpa only [archimedeanRadius,mul_inv_rev,zero_mul] using! h.mul_const a⁻¹
  have hnT : ∀ᶠ t : ℝ in atTop, archimedeanRadius a t ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact mul_ne_zero ha ht.ne'
  have hnB : ∀ᶠ t : ℝ in atBot, archimedeanRadius a t ≠ 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    exact mul_ne_zero ha ht.ne
  simpa only [archimedeanPoint,signedPolarPoint_re,signedPolarPoint_im] using!
    (And.intro (rotating_radius_no_affine_residual_atTop (hi tendsto_inv_atTop_zero) hnT u v w huv)
      (rotating_radius_no_affine_residual_atBot (hi tendsto_inv_atBot_zero) hnB u v w huv))

/-- Bài 16(e): khảo sát đường xoắn `r = aφ` với bán kính có dấu. -/
theorem source_archimedean_polar_curve_investigation (a : ℝ) :
    (∀ z : ℂ, z ∈ archimedeanCurve a ↔ ∃ t : ℝ,
      z.re = a*t*Real.cos t ∧ z.im = a*t*Real.sin t) ∧
    (a = 0 → archimedeanCurve a = {0}) ∧
    (∀ t : ℝ, HasDerivAt (archimedeanRadius a) a t ∧
      HasDerivAt (polarX (archimedeanRadius a)) (archimedeanDX a t) t ∧
      HasDerivAt (polarY (archimedeanRadius a)) (archimedeanDY a t) t) ∧
    (∀ t : ℝ, archimedeanDX a t ≠ 0 ∨ archimedeanDY a t ≠ 0 ↔ a ≠ 0) ∧
    (a ≠ 0 → ∀ s t : ℝ, s ≠ t ∧ archimedeanPoint a s = archimedeanPoint a t ↔
      s = -t ∧ t ≠ 0 ∧ Real.cos t = 0) ∧
    (∀ t : ℝ, archimedeanRadius a (t+2*Real.pi)-archimedeanRadius a t = 2*Real.pi*a) ∧
    (a ≠ 0 → Tendsto (fun t : ℝ ↦ ‖archimedeanPoint a t‖) atTop atTop ∧
      Tendsto (fun t : ℝ ↦ ‖archimedeanPoint a t‖) atBot atTop) := by
  exact ⟨archimedean_complete_image a, fun h ↦ h ▸ archimedean_zero_scale,
    archimedean_actual_first_derivatives a, archimedean_regular_iff a,
    fun ha ↦ archimedean_selfintersection_iff ha, archimedean_turn_spacing a,
    archimedean_distance_infinite_ends⟩

end calculus.Chapter04.Section04ArchimedeanSpiralPolarCurveInvestigation
