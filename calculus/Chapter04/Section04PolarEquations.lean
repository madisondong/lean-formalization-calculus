import calculus.Chapter04.Section04PolarRepresentation
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# §4.4: phương trình tọa độ cực và quỹ tích

Nguồn: dòng 2532–2570. Góc chạy trên ℝ; bán kính có dấu. Công thức ngược ở dòng 2539 yêu cầu bán kính không âm và hoành độ khác 0.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section04PolarEquations
open Set
open calculus.Chapter04.Section04PolarRepresentation


def polarLocus (E : ℝ → ℝ → Prop) : Set ℂ :=
  {z | ∃ r θ : ℝ, E r θ ∧ signedPolarPoint r θ = z}

/-- Phương trình cực in tại dòng 2554. -/
def polarCurveImage (f : ℝ → ℝ) : Set ℂ :=
  polarLocus (fun r θ ↦ r = f θ)

/-- Phương trình cực ẩn in tại dòng 2558. -/
def implicitPolarLocus (F : ℝ → ℝ → ℝ) : Set ℂ :=
  polarLocus (fun r θ ↦ F r θ = 0)

theorem signed_polar_equation_coordinates (r θ : ℝ) (z : ℂ) :
    signedPolarPoint r θ = z ↔ z.re = r * Real.cos θ ∧ z.im = r * Real.sin θ := by
  constructor
  · intro h
    exact ⟨by rw [← h, signedPolarPoint_re], by rw [← h, signedPolarPoint_im]⟩
  · rintro ⟨hx, hy⟩
    apply Complex.ext
    · rw [signedPolarPoint_re, hx]
    · rw [signedPolarPoint_im, hy]

theorem source_polar_explicit_membership (f : ℝ → ℝ) (z : ℂ) :
    z ∈ polarCurveImage f ↔ ∃ θ : ℝ, signedPolarPoint (f θ) θ = z := by
  constructor
  · rintro ⟨r, θ, hr, hz⟩
    exact ⟨θ, hr ▸ hz⟩
  · rintro ⟨θ, hz⟩
    exact ⟨f θ, θ, rfl, hz⟩

theorem source_polar_implicit_membership (F : ℝ → ℝ → ℝ) (z : ℂ) :
    z ∈ implicitPolarLocus F ↔ ∃ r θ : ℝ, F r θ = 0 ∧ signedPolarPoint r θ = z := Iff.rfl


theorem source_polar_equations_as_cartesian_loci (f : ℝ → ℝ) (F : ℝ → ℝ → ℝ) :
    (∀ z : ℂ, z ∈ polarCurveImage f ↔
      ∃ θ : ℝ, z.re = f θ * Real.cos θ ∧ z.im = f θ * Real.sin θ) ∧
    (∀ z : ℂ, z ∈ implicitPolarLocus F ↔
      ∃ r θ : ℝ, F r θ = 0 ∧ z.re = r * Real.cos θ ∧ z.im = r * Real.sin θ) := by
  constructor
  · intro z
    rw [source_polar_explicit_membership]
    exact exists_congr (fun θ ↦ signed_polar_equation_coordinates (f θ) θ z)
  · intro z
    rw [source_polar_implicit_membership]
    apply exists_congr
    intro r
    apply exists_congr
    intro θ
    exact and_congr_right (fun _ ↦ signed_polar_equation_coordinates r θ z)

theorem source_point_P_cartesian :
    signedPolarPoint 2 (Real.pi / 3) = Complex.mk 1 (Real.sqrt 3) := by
  apply Complex.ext
  · rw [signedPolarPoint_re, Real.cos_pi_div_three]
    norm_num
  · rw [signedPolarPoint_im, Real.sin_pi_div_three]
    change 2 * (Real.sqrt 3 / 2) = Real.sqrt 3
    ring

theorem square_root_two_half_product : Real.sqrt 2 * (Real.sqrt 2 / 2) = (1 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem point_Q_negative_angle :
    signedPolarPoint (Real.sqrt 2) (-Real.pi / 4) = Complex.mk 1 (-1) := by
  apply Complex.ext
  · rw [signedPolarPoint_re, neg_div, Real.cos_neg, Real.cos_pi_div_four]
    exact square_root_two_half_product
  · rw [signedPolarPoint_im, neg_div, Real.sin_neg, Real.sin_pi_div_four]
    change Real.sqrt 2 * -(Real.sqrt 2 / 2) = -1
    nlinarith [square_root_two_half_product]

theorem source_point_Q_polar :
    signedPolarPoint (Real.sqrt 2) (-Real.pi / 4) = Complex.mk 1 (-1) ∧
      signedPolarPoint (Real.sqrt 2) (7 * Real.pi / 4) = Complex.mk 1 (-1) ∧
      Real.sqrt ((1 : ℝ)^2 + (-1)^2) = Real.sqrt 2 ∧
      Real.tan (-Real.pi / 4) = -1 ∧ Real.tan (7 * Real.pi / 4) = -1 := by
  refine ⟨point_Q_negative_angle, ?_, ?_, ?_, ?_⟩
  · rw [show 7 * Real.pi / 4 = -Real.pi / 4 + 2 * Real.pi by ring,
      signedPolarPoint_add_two_pi]
    exact point_Q_negative_angle
  · norm_num
  · rw [neg_div, Real.tan_neg, Real.tan_pi_div_four]
  · rw [show 7 * Real.pi / 4 = (-Real.pi / 4 + Real.pi) + Real.pi by ring,
      Real.tan_add_pi, Real.tan_add_pi, neg_div, Real.tan_neg, Real.tan_pi_div_four]

theorem signed_polar_square_sum (r θ : ℝ) :
    (signedPolarPoint r θ).re^2 + (signedPolarPoint r θ).im^2 = r^2 := by
  rw [signedPolarPoint_re, signedPolarPoint_im]
  nlinarith [congrArg (fun t : ℝ ↦ r^2*t) (Real.sin_sq_add_cos_sq θ)]


theorem repaired_nonnegative_polar_inverse (r θ : ℝ) (hr : 0 ≤ r)
    (hx : (signedPolarPoint r θ).re ≠ 0) :
    r = Real.sqrt ((signedPolarPoint r θ).re^2 + (signedPolarPoint r θ).im^2) ∧
      Real.tan θ = (signedPolarPoint r θ).im / (signedPolarPoint r θ).re := by
  constructor
  · rw [signed_polar_square_sum, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
  · rw [signedPolarPoint_re] at hx
    have hr0 : r ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hc : Real.cos θ ≠ 0 := (mul_ne_zero_iff.mp hx).2
    rw [signedPolarPoint_im, signedPolarPoint_re, Real.tan_eq_sin_div_cos]
    field_simp [hr0, hc]

theorem constant_radius_locus (a : ℝ) (z : ℂ) :
    z ∈ polarLocus (fun r _ ↦ r = a) ↔ ‖z‖ = |a| := by
  constructor
  · rintro ⟨r, θ, rfl, rfl⟩
    exact norm_signedPolarPoint r θ
  · intro hz
    rcases le_or_gt 0 a with ha | ha
    · refine ⟨a, nonnegativePolarAngle z, rfl, ?_⟩
      have hrad : a = ‖z‖ := by rw [hz, abs_of_nonneg ha]
      rw [hrad]
      exact signedPolarPoint_norm_nonnegativePolarAngle z
    · refine ⟨a, nonnegativePolarAngle z + Real.pi, rfl, ?_⟩
      rw [← signedPolarPoint_neg_radius_eq_add_pi]
      have hrad : -a = ‖z‖ := by rw [hz, abs_of_neg ha]
      rw [hrad]
      exact signedPolarPoint_norm_nonnegativePolarAngle z

theorem fixed_quarter_angle_locus (z : ℂ) :
    z ∈ polarLocus (fun _ θ ↦ θ = Real.pi / 4) ↔ z.im = z.re := by
  constructor
  · rintro ⟨r, θ, rfl, rfl⟩
    rw [signedPolarPoint_im, signedPolarPoint_re, Real.sin_pi_div_four, Real.cos_pi_div_four]
  · intro hz
    refine ⟨Real.sqrt 2 * z.re, Real.pi / 4, rfl, ?_⟩
    have hv : (Real.sqrt 2 * z.re) * (Real.sqrt 2 / 2) = z.re := by
      calc
        _ = z.re * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by ring
        _ = z.re := by rw [square_root_two_half_product, mul_one]
    apply Complex.ext
    · rw [signedPolarPoint_re, Real.cos_pi_div_four]
      exact hv
    · rw [signedPolarPoint_im, Real.sin_pi_div_four, hz]
      exact hv


theorem source_constant_radius_and_fixed_angle :
    (∀ a : ℝ, ∀ z : ℂ, z ∈ polarLocus (fun r _ ↦ r = a) ↔ dist z 0 = |a|) ∧
      (∀ z : ℂ, z ∈ polarLocus (fun _ θ ↦ θ = Real.pi / 4) ↔ z.im = z.re) := by
  exact ⟨fun a z ↦ by simpa only [dist_zero_right] using constant_radius_locus a z,
    fixed_quarter_angle_locus⟩


theorem source_cosine_polar_circle (z : ℂ) :
    z ∈ polarCurveImage (fun θ ↦ 2 * Real.cos θ) ↔ (z.re - 1)^2 + z.im^2 = 1 := by
  constructor
  · rintro ⟨r, θ, hr, rfl⟩
    have hs := signed_polar_square_sum r θ
    have hm : r^2 = 2*r*Real.cos θ := by rw [hr]; ring
    rw [signedPolarPoint_re] at hs ⊢
    nlinarith
  · intro hz
    by_cases hzero : z = 0
    · subst z
      exact ⟨0, Real.pi / 2, by change (0 : ℝ) = 2 * Real.cos (Real.pi / 2); rw [Real.cos_pi_div_two]; ring, signedPolarPoint_zero_radius _⟩
    · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hzero
      have hs : ‖z‖^2 = 2*z.re := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith
      have hx : ‖z‖ * Real.cos (nonnegativePolarAngle z) = z.re := by
        have h := congrArg Complex.re (signedPolarPoint_norm_nonnegativePolarAngle z)
        simpa only [signedPolarPoint_re] using h
      have hm : ‖z‖ * (‖z‖ - 2*Real.cos (nonnegativePolarAngle z)) = 0 := by nlinarith
      have hr : ‖z‖ = 2*Real.cos (nonnegativePolarAngle z) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hpos.ne')
      exact ⟨‖z‖, nonnegativePolarAngle z, hr, signedPolarPoint_norm_nonnegativePolarAngle z⟩

end calculus.Chapter04.Section04PolarEquations
