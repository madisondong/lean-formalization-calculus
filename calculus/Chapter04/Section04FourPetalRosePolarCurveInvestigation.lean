import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Ví dụ 4.4.32: hoa bốn cánh `r = cos(2φ)`

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2599–2658; quy ước bán kính có dấu tại dòng 2450–2453, 2488–2493. Chu kỳ bán kính là `π`, còn chu kỳ điểm Descartes là `2π`.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04FourPetalRosePolarCurveInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

def fourRoseRadius (θ : ℝ) : ℝ := Real.cos (2 * θ)
def fourRoseDX (θ : ℝ) : ℝ :=
  -2 * Real.sin (2 * θ) * Real.cos θ - fourRoseRadius θ * Real.sin θ
def fourRoseDY (θ : ℝ) : ℝ :=
  -2 * Real.sin (2 * θ) * Real.sin θ + fourRoseRadius θ * Real.cos θ
def fourRoseDDX (θ : ℝ) : ℝ :=
  -5 * fourRoseRadius θ * Real.cos θ + 4 * Real.sin (2 * θ) * Real.sin θ
def fourRoseDDY (θ : ℝ) : ℝ :=
  -5 * fourRoseRadius θ * Real.sin θ - 4 * Real.sin (2 * θ) * Real.cos θ

theorem four_rose_actual_derivatives (θ : ℝ) :
    HasDerivAt fourRoseRadius (-2 * Real.sin (2 * θ)) θ ∧
      HasDerivAt (polarX fourRoseRadius) (fourRoseDX θ) θ ∧
      HasDerivAt (polarY fourRoseRadius) (fourRoseDY θ) θ := by
  have hr : HasDerivAt fourRoseRadius (-2 * Real.sin (2 * θ)) θ := by
    have h := ((hasDerivAt_id θ).const_mul 2).cos
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  exact ⟨hr, polarX_hasDerivAt hr, polarY_hasDerivAt hr⟩

theorem four_rose_actual_second_derivatives (θ : ℝ) :
    HasDerivAt (deriv (polarX fourRoseRadius)) (fourRoseDDX θ) θ ∧
      HasDerivAt (deriv (polarY fourRoseRadius)) (fourRoseDDY θ) θ := by
  have hR := (four_rose_actual_derivatives θ).1
  have hS : HasDerivAt (fun t : ℝ ↦ Real.sin (2 * t)) (2 * fourRoseRadius θ) θ := by
    have h := ((hasDerivAt_id θ).const_mul 2).sin
    apply h.congr_deriv
    simp only [id_eq, mul_one, fourRoseRadius]
    ring
  have hX : HasDerivAt fourRoseDX (fourRoseDDX θ) θ := by
    have h := ((hS.const_mul (-2)).fun_mul (Real.hasDerivAt_cos θ)).fun_sub
      (hR.fun_mul (Real.hasDerivAt_sin θ))
    apply h.congr_deriv
    dsimp only [fourRoseDDX]
    ring
  have hY : HasDerivAt fourRoseDY (fourRoseDDY θ) θ := by
    have h := ((hS.const_mul (-2)).fun_mul (Real.hasDerivAt_sin θ)).fun_add
      (hR.fun_mul (Real.hasDerivAt_cos θ))
    apply h.congr_deriv
    dsimp only [fourRoseDDY]
    ring
  constructor
  · apply hX.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (four_rose_actual_derivatives t).2.1.deriv
  · apply hY.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (four_rose_actual_derivatives t).2.2.deriv

theorem four_rose_coordinate_derivative_factors (θ : ℝ) :
    fourRoseDX θ = Real.sin θ * (1 - 6 * Real.cos θ ^ 2) ∧
      fourRoseDY θ = Real.cos θ * (1 - 6 * Real.sin θ ^ 2) := by
  have ht := Real.sin_sq_add_cos_sq θ
  constructor
  · dsimp only [fourRoseDX, fourRoseRadius]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    nlinarith [congrArg (fun q : ℝ ↦ Real.sin θ * q) ht]
  · dsimp only [fourRoseDY, fourRoseRadius]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    nlinarith [congrArg (fun q : ℝ ↦ Real.cos θ * q) ht]

theorem four_rose_speed_sq_and_curvature_numerator (θ : ℝ) :
    fourRoseDX θ ^ 2 + fourRoseDY θ ^ 2 = 4 - 3 * fourRoseRadius θ ^ 2 ∧
      fourRoseDX θ * fourRoseDDY θ - fourRoseDY θ * fourRoseDDX θ =
        8 - 3 * fourRoseRadius θ ^ 2 ∧
      1 ≤ fourRoseDX θ ^ 2 + fourRoseDY θ ^ 2 ∧
      5 ≤ fourRoseDX θ * fourRoseDDY θ - fourRoseDY θ * fourRoseDDX θ := by
  have ht : Real.sin (2 * θ) ^ 2 + fourRoseRadius θ ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * θ)
  have hX : fourRoseDX θ ^ 2 + fourRoseDY θ ^ 2 = 4 - 3 * fourRoseRadius θ ^ 2 := by
    dsimp only [fourRoseDX, fourRoseDY]
    nlinarith [congrArg (fun q : ℝ ↦ 4 * Real.sin (2 * θ) ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ fourRoseRadius θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]
  have hK : fourRoseDX θ * fourRoseDDY θ - fourRoseDY θ * fourRoseDDX θ =
      8 - 3 * fourRoseRadius θ ^ 2 := by
    dsimp only [fourRoseDX, fourRoseDY, fourRoseDDX, fourRoseDDY]
    nlinarith [congrArg (fun q : ℝ ↦ 8 * Real.sin (2 * θ) ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ 5 * fourRoseRadius θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]
  refine ⟨hX, hK, ?_, ?_⟩
  · rw [hX]
    nlinarith [sq_nonneg (Real.sin (2 * θ))]
  · rw [hK]
    nlinarith [sq_nonneg (Real.sin (2 * θ))]

theorem four_rose_sextic_polar (r θ : ℝ) :
    ((signedPolarPoint r θ).re ^ 2 + (signedPolarPoint r θ).im ^ 2) ^ 3 -
      ((signedPolarPoint r θ).re ^ 2 - (signedPolarPoint r θ).im ^ 2) ^ 2 =
      r ^ 4 * (r ^ 2 - fourRoseRadius θ ^ 2) := by
  rw [signed_polar_square_sum, signedPolarPoint_re, signedPolarPoint_im]
  have hc : Real.cos θ ^ 2 - Real.sin θ ^ 2 = fourRoseRadius θ := by
    rw [fourRoseRadius, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    (r ^ 2) ^ 3 - ((r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2) ^ 2 =
        r ^ 4 * (r ^ 2 - (Real.cos θ ^ 2 - Real.sin θ ^ 2) ^ 2) := by ring
    _ = r ^ 4 * (r ^ 2 - fourRoseRadius θ ^ 2) := by rw [hc]

theorem four_rose_radius_add_pi (θ : ℝ) :
    fourRoseRadius (θ + Real.pi) = fourRoseRadius θ := by
  rw [fourRoseRadius, show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring,
    Real.cos_add_two_pi]
  rfl


theorem four_rose_mem_curve_image_iff (z : ℂ) :
    z ∈ polarCurveImage fourRoseRadius ↔
      (z.re ^ 2 + z.im ^ 2) ^ 3 = (z.re ^ 2 - z.im ^ 2) ^ 2 := by
  rw [source_polar_explicit_membership]
  constructor
  · rintro ⟨θ, rfl⟩
    have h := four_rose_sextic_polar (fourRoseRadius θ) θ
    rw [sub_self, mul_zero] at h
    exact sub_eq_zero.mp h
  · intro h
    by_cases hz : z = 0
    · subst z
      refine ⟨Real.pi / 4, ?_⟩
      rw [fourRoseRadius, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
        Real.cos_pi_div_two, signedPolarPoint_zero_radius]
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hq := four_rose_sextic_polar ‖z‖ (nonnegativePolarAngle z)
      rw [signedPolarPoint_norm_nonnegativePolarAngle, h, sub_self] at hq
      have hs : ‖z‖ ^ 2 = fourRoseRadius (nonnegativePolarAngle z) ^ 2 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hq.symm).resolve_left (pow_ne_zero 4 hp.ne'))
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hr | hr
      · exact ⟨nonnegativePolarAngle z, by rw [← hr]; exact signedPolarPoint_norm_nonnegativePolarAngle z⟩
      · have hr' : fourRoseRadius (nonnegativePolarAngle z) = -‖z‖ := by linarith
        refine ⟨nonnegativePolarAngle z + Real.pi, ?_⟩
        rw [four_rose_radius_add_pi, hr', signedPolarPoint_neg_radius_eq_add_pi,
          show nonnegativePolarAngle z + Real.pi + Real.pi = nonnegativePolarAngle z + 2 * Real.pi by ring,
          signedPolarPoint_add_two_pi]
        exact signedPolarPoint_norm_nonnegativePolarAngle z

theorem four_rose_distance (θ : ℝ) :
    ‖signedPolarPoint (fourRoseRadius θ) θ‖ ≤ 1 ∧
      (‖signedPolarPoint (fourRoseRadius θ) θ‖ = 0 ↔ fourRoseRadius θ = 0) ∧
      (‖signedPolarPoint (fourRoseRadius θ) θ‖ = 1 ↔
        fourRoseRadius θ = 1 ∨ fourRoseRadius θ = -1) := by
  rw [norm_signedPolarPoint]
  refine ⟨abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩, abs_eq_zero, ?_⟩
  simpa only [abs_one] using (abs_eq_abs : |fourRoseRadius θ| = |(1 : ℝ)| ↔ _)

theorem four_rose_compact_curve_image : IsCompact (polarCurveImage fourRoseRadius) := by
  have hs : polarCurveImage fourRoseRadius =
      {z : ℂ | (z.re ^ 2 + z.im ^ 2) ^ 3 = (z.re ^ 2 - z.im ^ 2) ^ 2} := by
    ext z
    exact four_rose_mem_curve_image_iff z
  have hc : IsClosed (polarCurveImage fourRoseRadius) := by
    rw [hs]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc
  intro z hz
  obtain ⟨θ, rfl⟩ := (source_polar_explicit_membership fourRoseRadius z).mp hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using (four_rose_distance θ).1

theorem four_rose_opposite_point (θ : ℝ) :
    signedPolarPoint (fourRoseRadius (θ + Real.pi)) (θ + Real.pi) =
      -signedPolarPoint (fourRoseRadius θ) θ := by
  rw [four_rose_radius_add_pi, signed_polar_add_pi]

theorem four_rose_point_period (θ : ℝ) :
    signedPolarPoint (fourRoseRadius (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
      signedPolarPoint (fourRoseRadius θ) θ := by
  have hr : fourRoseRadius (θ + 2 * Real.pi) = fourRoseRadius θ := by
    rw [show θ + 2 * Real.pi = θ + Real.pi + Real.pi by ring,
      four_rose_radius_add_pi, four_rose_radius_add_pi]
  rw [hr, signedPolarPoint_add_two_pi]

theorem four_rose_quarter_turn (θ : ℝ) :
    signedPolarPoint (fourRoseRadius (θ - Real.pi / 2)) (θ - Real.pi / 2) =
      Circle.exp (Real.pi / 2) * signedPolarPoint (fourRoseRadius θ) θ := by
  have hr : fourRoseRadius (θ - Real.pi / 2) = -fourRoseRadius θ := by
    rw [fourRoseRadius, show 2 * (θ - Real.pi / 2) = 2 * θ - Real.pi by ring,
      Real.cos_sub_pi]
    rfl
  rw [hr, signedPolarPoint_neg_radius_eq_add_pi,
    show θ - Real.pi / 2 + Real.pi = θ + Real.pi / 2 by ring]
  dsimp only [signedPolarPoint]
  rw [Circle.exp_add, Circle.coe_mul]
  ring

theorem four_rose_axis_symmetries (z : ℂ) :
    (z ∈ polarCurveImage fourRoseRadius ↔ polarAxisReflection z ∈ polarCurveImage fourRoseRadius) ∧
      (z ∈ polarCurveImage fourRoseRadius ↔ perpendicularAxisReflection z ∈ polarCurveImage fourRoseRadius) ∧
      (z ∈ polarCurveImage fourRoseRadius ↔ -z ∈ polarCurveImage fourRoseRadius) := by
  constructor
  · rw [four_rose_mem_curve_image_iff, four_rose_mem_curve_image_iff]
    simp only [polarAxisReflection, neg_sq]
  · constructor
    · rw [four_rose_mem_curve_image_iff, four_rose_mem_curve_image_iff]
      simp only [perpendicularAxisReflection, neg_sq]
    · rw [four_rose_mem_curve_image_iff, four_rose_mem_curve_image_iff]
      simp only [Complex.neg_re, Complex.neg_im, neg_sq]

theorem four_rose_named_points :
    signedPolarPoint (fourRoseRadius 0) 0 = (1 : ℂ) ∧
      signedPolarPoint (fourRoseRadius (Real.pi / 2)) (Real.pi / 2) = (⟨0, -1⟩ : ℂ) ∧
      signedPolarPoint (fourRoseRadius Real.pi) Real.pi = (-1 : ℂ) ∧
      signedPolarPoint (fourRoseRadius (3 * Real.pi / 2)) (3 * Real.pi / 2) = (⟨0, 1⟩ : ℂ) := by
  have h0 : signedPolarPoint (fourRoseRadius 0) 0 = (1 : ℂ) := by
    apply Complex.ext
    · simp [signedPolarPoint_re, fourRoseRadius]
    · simp [signedPolarPoint_im, fourRoseRadius]
  have hhalf : signedPolarPoint (fourRoseRadius (Real.pi / 2)) (Real.pi / 2) = (⟨0, -1⟩ : ℂ) := by
    apply Complex.ext
    · simp [signedPolarPoint_re, fourRoseRadius, show 2 * (Real.pi / 2) = Real.pi by ring]
    · simp [signedPolarPoint_im, fourRoseRadius, show 2 * (Real.pi / 2) = Real.pi by ring]
  refine ⟨h0, hhalf, ?_, ?_⟩
  · simpa only [zero_add, h0] using four_rose_opposite_point 0
  · have h := four_rose_opposite_point (Real.pi / 2)
    rw [hhalf, show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring] at h
    exact h.trans (by
      apply Complex.ext
      · norm_num
      · norm_num)

theorem four_rose_radius_strict_descent :
    StrictAntiOn fourRoseRadius (Icc 0 (Real.pi / 2)) := by
  have hc : Continuous fourRoseRadius := by unfold fourRoseRadius; fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (Real.pi / 2)) hc.continuousOn
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(four_rose_actual_derivatives θ).1.deriv]
  have hp : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  linarith


theorem four_rose_fundamental_radius_table :
    fourRoseRadius 0 = 1 ∧ fourRoseRadius (Real.pi / 4) = 0 ∧
      fourRoseRadius (Real.pi / 2) = -1 ∧
      StrictAntiOn fourRoseRadius (Icc 0 (Real.pi / 2)) := by
  refine ⟨?_, ?_, ?_, four_rose_radius_strict_descent⟩
  · simp [fourRoseRadius]
  · rw [fourRoseRadius, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  · rw [fourRoseRadius, show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]


theorem four_rose_regular_slope {θ : ℝ} (hx : fourRoseDX θ ≠ 0) :
    DomainLimit (xSecantDomain univ fourRoseRadius θ)
      (fun t ↦ (polarY fourRoseRadius t - polarY fourRoseRadius θ) /
        (polarX fourRoseRadius t - polarX fourRoseRadius θ)) θ
      (fourRoseDY θ / fourRoseDX θ) :=
  polar_secant_slope_limit Filter.univ_mem (four_rose_actual_derivatives θ).1 hx

theorem four_rose_inverse_regular_slope {θ : ℝ} (hy : fourRoseDY θ ≠ 0) :
    DomainLimit (ySecantDomain univ fourRoseRadius θ)
      (fun t ↦ (polarX fourRoseRadius t - polarX fourRoseRadius θ) /
        (polarY fourRoseRadius t - polarY fourRoseRadius θ)) θ
      (fourRoseDX θ / fourRoseDY θ) :=
  polar_inverse_secant_slope_limit Filter.univ_mem (four_rose_actual_derivatives θ).1 hy

theorem four_rose_tangents_iff (θ : ℝ) :
    (HasHorizontalPolarTangent univ fourRoseRadius θ ↔ fourRoseDY θ = 0) ∧
      (HasVerticalPolarTangent univ fourRoseRadius θ ↔ fourRoseDX θ = 0) := by
  have hX := (four_rose_actual_derivatives θ).2.1
  have hY := (four_rose_actual_derivatives θ).2.2
  have hv := (four_rose_speed_sq_and_curvature_numerator θ).2.2.1
  constructor
  · constructor
    · exact fun h ↦ secant_zero_implies_deriv_zero hY hX h
    · intro hy
      apply source_horizontal_polar_tangent Filter.univ_mem (four_rose_actual_derivatives θ).1 hy
      change fourRoseDX θ ≠ 0
      intro hx
      rw [hx, hy] at hv
      norm_num at hv
  · constructor
    · exact fun h ↦ secant_zero_implies_deriv_zero hX hY h
    · intro hx
      apply source_vertical_polar_tangent Filter.univ_mem (four_rose_actual_derivatives θ).1 hx
      change fourRoseDY θ ≠ 0
      intro hy
      rw [hx, hy] at hv
      norm_num at hv

theorem four_rose_tangent_conditions (θ : ℝ) :
    (HasHorizontalPolarTangent univ fourRoseRadius θ ↔ Real.cos θ = 0 ∨ Real.sin θ ^ 2 = 1 / 6) ∧
      (HasVerticalPolarTangent univ fourRoseRadius θ ↔ Real.sin θ = 0 ∨ Real.cos θ ^ 2 = 1 / 6) := by
  rw [(four_rose_tangents_iff θ).1, (four_rose_tangents_iff θ).2,
    (four_rose_coordinate_derivative_factors θ).1, (four_rose_coordinate_derivative_factors θ).2,
    mul_eq_zero, mul_eq_zero]
  constructor
  · constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  · constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)

theorem four_rose_coordinate_extrema (θ : ℝ) :
    ((IsLocalMinimumOn (polarX fourRoseRadius) univ θ ↔ fourRoseDX θ = 0 ∧ 0 < fourRoseDDX θ) ∧
      (IsLocalMaximumOn (polarX fourRoseRadius) univ θ ↔ fourRoseDX θ = 0 ∧ fourRoseDDX θ < 0)) ∧
      ((IsLocalMinimumOn (polarY fourRoseRadius) univ θ ↔ fourRoseDY θ = 0 ∧ 0 < fourRoseDDY θ) ∧
      (IsLocalMaximumOn (polarY fourRoseRadius) univ θ ↔ fourRoseDY θ = 0 ∧ fourRoseDDY θ < 0)) := by
  have hk : 0 < fourRoseDX θ * fourRoseDDY θ - fourRoseDY θ * fourRoseDDX θ :=
    lt_of_lt_of_le (by norm_num) (four_rose_speed_sq_and_curvature_numerator θ).2.2.2
  have hx : deriv (polarX fourRoseRadius) θ = 0 → deriv (deriv (polarX fourRoseRadius)) θ ≠ 0 := by
    rw [(four_rose_actual_derivatives θ).2.1.deriv, (four_rose_actual_second_derivatives θ).1.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hy : deriv (polarY fourRoseRadius) θ = 0 → deriv (deriv (polarY fourRoseRadius)) θ ≠ 0 := by
    rw [(four_rose_actual_derivatives θ).2.2.deriv, (four_rose_actual_second_derivatives θ).2.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hX := nondegenerate_extrema_iff (four_rose_actual_derivatives θ).2.1.differentiableAt hx
  have hY := nondegenerate_extrema_iff (four_rose_actual_derivatives θ).2.2.differentiableAt hy
  rw [(four_rose_actual_derivatives θ).2.1.deriv, (four_rose_actual_second_derivatives θ).1.deriv] at hX
  rw [(four_rose_actual_derivatives θ).2.2.deriv, (four_rose_actual_second_derivatives θ).2.deriv] at hY
  exact ⟨hX, hY⟩

theorem four_rose_radius_second_derivative (θ : ℝ) :
    HasDerivAt (deriv fourRoseRadius) (-4 * fourRoseRadius θ) θ := by
  have h := (((hasDerivAt_id θ).const_mul 2).sin).const_mul (-2)
  have hc : HasDerivAt (fun t : ℝ ↦ -2 * Real.sin (2 * t)) (-4 * fourRoseRadius θ) θ := by
    apply h.congr_deriv
    simp only [id_eq, mul_one, fourRoseRadius]
    ring
  apply hc.congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (four_rose_actual_derivatives t).1.deriv

theorem four_rose_radius_extrema (θ : ℝ) :
    (IsLocalMinimumOn fourRoseRadius univ θ ↔ fourRoseRadius θ = -1) ∧
      (IsLocalMaximumOn fourRoseRadius univ θ ↔ fourRoseRadius θ = 1) := by
  have ht : Real.sin (2 * θ) ^ 2 + fourRoseRadius θ ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * θ)
  have hne : deriv fourRoseRadius θ = 0 → deriv (deriv fourRoseRadius) θ ≠ 0 := by
    rw [(four_rose_actual_derivatives θ).1.deriv, (four_rose_radius_second_derivative θ).deriv]
    intro hd hdd
    nlinarith
  have h := nondegenerate_extrema_iff (four_rose_actual_derivatives θ).1.differentiableAt hne
  rw [(four_rose_actual_derivatives θ).1.deriv, (four_rose_radius_second_derivative θ).deriv] at h
  constructor
  · rw [h.1]
    constructor
    · rintro ⟨hs, hp⟩
      have he : fourRoseRadius θ ^ 2 = 1 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show fourRoseRadius θ ^ 2 = (1 : ℝ) ^ 2 from by simpa only [one_pow] using he) with hr | hr
      · nlinarith
      · exact hr
    · intro hr
      have hs : Real.sin (2 * θ) = 0 := sq_eq_zero_iff.mp (by nlinarith)
      rw [hr, hs]
      norm_num
  · rw [h.2]
    constructor
    · rintro ⟨hs, hn⟩
      have he : fourRoseRadius θ ^ 2 = 1 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show fourRoseRadius θ ^ 2 = (1 : ℝ) ^ 2 from by simpa only [one_pow] using he) with hr | hr
      · exact hr
      · nlinarith
    · intro hr
      have hs : Real.sin (2 * θ) = 0 := sq_eq_zero_iff.mp (by nlinarith)
      rw [hr, hs]
      norm_num

theorem four_rose_pole_parameters (θ : ℝ) :
    signedPolarPoint (fourRoseRadius θ) θ = 0 ↔
      ∃ k : ℤ, θ = (2 * (k : ℝ) + 1) * Real.pi / 4 := by
  rw [signedPolarPoint_eq_zero_iff, fourRoseRadius, Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

theorem four_rose_pole_tangents {θ : ℝ} (hr : fourRoseRadius θ = 0) :
    Real.cos θ ≠ 0 ∧ (Real.sin θ / Real.cos θ) ^ 2 = 1 ∧
      DomainLimit (xSecantDomain univ fourRoseRadius θ)
        (fun t ↦ (polarY fourRoseRadius t - polarY fourRoseRadius θ) /
          (polarX fourRoseRadius t - polarX fourRoseRadius θ)) θ (Real.sin θ / Real.cos θ) := by
  have he : Real.cos θ ^ 2 - Real.sin θ ^ 2 = 0 := by
    rw [fourRoseRadius, Real.cos_two_mul] at hr
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hc : Real.cos θ ≠ 0 := by
    intro hc
    rw [hc] at he
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hS : Real.sin (2 * θ) ≠ 0 := by
    intro hS
    have h := Real.sin_sq_add_cos_sq (2 * θ)
    change Real.sin (2 * θ) ^ 2 + fourRoseRadius θ ^ 2 = 1 at h
    rw [hr, hS] at h
    norm_num at h
  have hx : -2 * Real.sin (2 * θ) * Real.cos θ - fourRoseRadius θ * Real.sin θ ≠ 0 := by
    rw [hr, zero_mul, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hS) hc
  refine ⟨hc, ?_, ?_⟩
  · rw [div_pow]
    exact (div_eq_one_iff_eq (pow_ne_zero 2 hc)).mpr (by linarith)
  · have h := polar_secant_slope_limit Filter.univ_mem (four_rose_actual_derivatives θ).1 hx
    convert h using 1
    rw [hr]
    simp only [zero_mul, add_zero, sub_zero]
    field_simp [hS, hc]

theorem four_rose_named_tangents :
    HasVerticalPolarTangent univ fourRoseRadius 0 ∧
      HasHorizontalPolarTangent univ fourRoseRadius (Real.pi / 2) := by
  constructor
  · rw [(four_rose_tangent_conditions 0).2]
    exact Or.inl Real.sin_zero
  · rw [(four_rose_tangent_conditions (Real.pi / 2)).1]
    exact Or.inl Real.cos_pi_div_two


theorem four_rose_injective_off_pole {θ ψ : ℝ}
    (hθ : θ ∈ Ico 0 (2 * Real.pi)) (hψ : ψ ∈ Ico 0 (2 * Real.pi))
    (hn : fourRoseRadius θ ≠ 0)
    (he : signedPolarPoint (fourRoseRadius θ) θ = signedPolarPoint (fourRoseRadius ψ) ψ) : θ = ψ := by
  have hcube (t : ℝ) :
      (signedPolarPoint (fourRoseRadius t) t).re ^ 2 -
        (signedPolarPoint (fourRoseRadius t) t).im ^ 2 = fourRoseRadius t ^ 3 := by
    rw [signedPolarPoint_re, signedPolarPoint_im]
    have hc : Real.cos t ^ 2 - Real.sin t ^ 2 = fourRoseRadius t := by
      rw [fourRoseRadius, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq t]
    calc
      (fourRoseRadius t * Real.cos t) ^ 2 - (fourRoseRadius t * Real.sin t) ^ 2 =
          fourRoseRadius t ^ 2 * (Real.cos t ^ 2 - Real.sin t ^ 2) := by ring
      _ = fourRoseRadius t ^ 3 := by rw [hc]; ring
  have h3 : fourRoseRadius θ ^ 3 = fourRoseRadius ψ ^ 3 := by
    rw [← hcube θ, he, hcube ψ]
  have hp : 0 < fourRoseRadius θ ^ 2 + fourRoseRadius θ * fourRoseRadius ψ + fourRoseRadius ψ ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (fourRoseRadius θ + fourRoseRadius ψ), sq_nonneg (fourRoseRadius ψ)]
  have hf : (fourRoseRadius θ - fourRoseRadius ψ) *
      (fourRoseRadius θ ^ 2 + fourRoseRadius θ * fourRoseRadius ψ + fourRoseRadius ψ ^ 2) = 0 := by
    nlinarith
  have hr : fourRoseRadius θ = fourRoseRadius ψ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')
  rw [← hr] at he
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hθ hψ
  apply Circle.ext
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn) he


theorem corrected_four_rose_complete_polar_curve_investigation :
    (∀ z : ℂ, z ∈ polarCurveImage fourRoseRadius ↔
      (z.re ^ 2 + z.im ^ 2) ^ 3 = (z.re ^ 2 - z.im ^ 2) ^ 2) ∧
      IsCompact (polarCurveImage fourRoseRadius) ∧
      (∀ θ : ℝ, HasDerivAt fourRoseRadius (-2 * Real.sin (2 * θ)) θ ∧
        HasDerivAt (polarX fourRoseRadius) (fourRoseDX θ) θ ∧
        HasDerivAt (polarY fourRoseRadius) (fourRoseDY θ) θ) ∧
      (∀ θ : ℝ, 1 ≤ fourRoseDX θ ^ 2 + fourRoseDY θ ^ 2) ∧
      (∀ θ : ℝ, 5 ≤ fourRoseDX θ * fourRoseDDY θ - fourRoseDY θ * fourRoseDDX θ) ∧
      (∀ θ : ℝ, HasHorizontalPolarTangent univ fourRoseRadius θ ↔
        Real.cos θ = 0 ∨ Real.sin θ ^ 2 = 1 / 6) ∧
      (∀ θ : ℝ, HasVerticalPolarTangent univ fourRoseRadius θ ↔
        Real.sin θ = 0 ∨ Real.cos θ ^ 2 = 1 / 6) ∧
      (∀ θ : ℝ, signedPolarPoint (fourRoseRadius (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
        signedPolarPoint (fourRoseRadius θ) θ) := by
  exact ⟨four_rose_mem_curve_image_iff, four_rose_compact_curve_image, four_rose_actual_derivatives,
    fun θ ↦ (four_rose_speed_sq_and_curvature_numerator θ).2.2.1,
    fun θ ↦ (four_rose_speed_sq_and_curvature_numerator θ).2.2.2,
    fun θ ↦ (four_rose_tangent_conditions θ).1,
    fun θ ↦ (four_rose_tangent_conditions θ).2, four_rose_point_period⟩

end calculus.Chapter04.Section04FourPetalRosePolarCurveInvestigation
