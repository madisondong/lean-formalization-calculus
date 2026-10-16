import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

/-!
# Bài 4.4.16(c): hoa ba cánh r=sin(3φ)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2795. Góc chạy trên ℝ; bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ThreePetalRosePolarCurveInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

def roseRadius (θ : ℝ) : ℝ := Real.sin (3 * θ)
def roseDX (θ : ℝ) : ℝ := 3 * Real.cos (3 * θ) * Real.cos θ - roseRadius θ * Real.sin θ
def roseDY (θ : ℝ) : ℝ := 3 * Real.cos (3 * θ) * Real.sin θ + roseRadius θ * Real.cos θ
def roseDDX (θ : ℝ) : ℝ := -10 * roseRadius θ * Real.cos θ - 6 * Real.cos (3 * θ) * Real.sin θ
def roseDDY (θ : ℝ) : ℝ := -10 * roseRadius θ * Real.sin θ + 6 * Real.cos (3 * θ) * Real.cos θ

theorem rose_angle_identity (θ : ℝ) :
    roseRadius θ = Real.sin θ * (3 * Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
  rw [roseRadius, Real.sin_three_mul]
  nlinarith [congrArg (fun q : ℝ ↦ 3 * Real.sin θ * q) (Real.sin_sq_add_cos_sq θ)]

theorem rose_actual_derivatives (θ : ℝ) :
    HasDerivAt roseRadius (3 * Real.cos (3 * θ)) θ ∧
      HasDerivAt (polarX roseRadius) (roseDX θ) θ ∧
      HasDerivAt (polarY roseRadius) (roseDY θ) θ := by
  have hr : HasDerivAt roseRadius (3 * Real.cos (3 * θ)) θ := by
    have h := ((hasDerivAt_id θ).const_mul 3).sin
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  exact ⟨hr, polarX_hasDerivAt hr, polarY_hasDerivAt hr⟩

theorem rose_actual_second_derivatives (θ : ℝ) :
    HasDerivAt (deriv (polarX roseRadius)) (roseDDX θ) θ ∧
      HasDerivAt (deriv (polarY roseRadius)) (roseDDY θ) θ := by
  have hR := (rose_actual_derivatives θ).1
  have hC : HasDerivAt (fun t : ℝ ↦ Real.cos (3 * t)) (-3 * roseRadius θ) θ := by
    have h := ((hasDerivAt_id θ).const_mul 3).cos
    apply h.congr_deriv
    simp only [id_eq, mul_one, roseRadius]
    ring
  have hX : HasDerivAt roseDX (roseDDX θ) θ := by
    have h := ((hC.const_mul 3).fun_mul (Real.hasDerivAt_cos θ)).fun_sub
      (hR.fun_mul (Real.hasDerivAt_sin θ))
    apply h.congr_deriv
    dsimp only [roseDDX]
    ring
  have hY : HasDerivAt roseDY (roseDDY θ) θ := by
    have h := ((hC.const_mul 3).fun_mul (Real.hasDerivAt_sin θ)).fun_add
      (hR.fun_mul (Real.hasDerivAt_cos θ))
    apply h.congr_deriv
    dsimp only [roseDDY]
    ring
  constructor
  · apply hX.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (rose_actual_derivatives t).2.1.deriv
  · apply hY.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (rose_actual_derivatives t).2.2.deriv

theorem rose_speed_sq_and_curvature_numerator (θ : ℝ) :
    roseDX θ ^ 2 + roseDY θ ^ 2 = 9 - 8 * roseRadius θ ^ 2 ∧
      roseDX θ * roseDDY θ - roseDY θ * roseDDX θ = 18 - 8 * roseRadius θ ^ 2 ∧
      1 ≤ roseDX θ ^ 2 + roseDY θ ^ 2 ∧
      10 ≤ roseDX θ * roseDDY θ - roseDY θ * roseDDX θ := by
  have ht : roseRadius θ ^ 2 + Real.cos (3 * θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * θ)
  have hX : roseDX θ ^ 2 + roseDY θ ^ 2 = 9 - 8 * roseRadius θ ^ 2 := by
    dsimp only [roseDX, roseDY]
    nlinarith [congrArg (fun q : ℝ ↦ 9 * Real.cos (3 * θ) ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ roseRadius θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]
  have hK : roseDX θ * roseDDY θ - roseDY θ * roseDDX θ = 18 - 8 * roseRadius θ ^ 2 := by
    dsimp only [roseDX, roseDY, roseDDX, roseDDY]
    nlinarith [congrArg (fun q : ℝ ↦ 18 * Real.cos (3 * θ) ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ 10 * roseRadius θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]
  refine ⟨hX, hK, ?_, ?_⟩
  · rw [hX]
    nlinarith [sq_nonneg (Real.cos (3 * θ))]
  · rw [hK]
    nlinarith [sq_nonneg (Real.cos (3 * θ))]


theorem rose_quartic_polar (r θ : ℝ) :
    ((signedPolarPoint r θ).re ^ 2 + (signedPolarPoint r θ).im ^ 2) ^ 2 -
      (signedPolarPoint r θ).im *
        (3 * (signedPolarPoint r θ).re ^ 2 - (signedPolarPoint r θ).im ^ 2) =
      r ^ 3 * (r - roseRadius θ) := by
  rw [signed_polar_square_sum, signedPolarPoint_re, signedPolarPoint_im, rose_angle_identity]
  ring


theorem rose_mem_curve_image_iff (z : ℂ) :
    z ∈ polarCurveImage roseRadius ↔
      (z.re ^ 2 + z.im ^ 2) ^ 2 = z.im * (3 * z.re ^ 2 - z.im ^ 2) := by
  rw [source_polar_explicit_membership]
  constructor
  · rintro ⟨θ, rfl⟩
    have h := rose_quartic_polar (roseRadius θ) θ
    rw [sub_self, mul_zero] at h
    exact sub_eq_zero.mp h
  · intro h
    by_cases hz : z = 0
    · subst z
      exact ⟨0, by rw [roseRadius, mul_zero, Real.sin_zero, signedPolarPoint_zero_radius]⟩
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hq := rose_quartic_polar ‖z‖ (nonnegativePolarAngle z)
      rw [signedPolarPoint_norm_nonnegativePolarAngle, h, sub_self] at hq
      have hr : ‖z‖ = roseRadius (nonnegativePolarAngle z) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hq.symm).resolve_left (pow_ne_zero 3 hp.ne'))
      exact ⟨nonnegativePolarAngle z, by rw [← hr]; exact signedPolarPoint_norm_nonnegativePolarAngle z⟩

theorem rose_distance (θ : ℝ) :
    ‖signedPolarPoint (roseRadius θ) θ‖ ≤ 1 ∧
      (‖signedPolarPoint (roseRadius θ) θ‖ = 0 ↔ roseRadius θ = 0) ∧
      (‖signedPolarPoint (roseRadius θ) θ‖ = 1 ↔ roseRadius θ = 1 ∨ roseRadius θ = -1) := by
  rw [norm_signedPolarPoint]
  refine ⟨abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩, abs_eq_zero, ?_⟩
  simpa only [abs_one] using (abs_eq_abs : |roseRadius θ| = |(1 : ℝ)| ↔ _)

theorem rose_point_period (θ : ℝ) :
    signedPolarPoint (roseRadius (θ + Real.pi)) (θ + Real.pi) = signedPolarPoint (roseRadius θ) θ := by
  have hr : roseRadius (θ + Real.pi) = -roseRadius θ := by
    rw [roseRadius, show 3 * (θ + Real.pi) = 3 * θ + Real.pi + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_add_pi]
    rfl
  rw [hr, signedPolarPoint_neg_radius_eq_add_pi,
    show θ + Real.pi + Real.pi = θ + 2 * Real.pi by ring, signedPolarPoint_add_two_pi]


theorem rose_threefold_rotation (θ : ℝ) :
    signedPolarPoint (roseRadius (θ + 2 * Real.pi / 3)) (θ + 2 * Real.pi / 3) =
      Circle.exp (2 * Real.pi / 3) * signedPolarPoint (roseRadius θ) θ := by
  have hr : roseRadius (θ + 2 * Real.pi / 3) = roseRadius θ := by
    rw [roseRadius, show 3 * (θ + 2 * Real.pi / 3) = 3 * θ + 2 * Real.pi by ring, Real.sin_add_two_pi]
    rfl
  rw [hr]
  dsimp only [signedPolarPoint]
  rw [Circle.exp_add, Circle.coe_mul]
  ring

theorem rose_perpendicular_symmetry (z : ℂ) :
    z ∈ polarCurveImage roseRadius ↔ perpendicularAxisReflection z ∈ polarCurveImage roseRadius := by
  rw [rose_mem_curve_image_iff, rose_mem_curve_image_iff]
  simp only [perpendicularAxisReflection, neg_sq]


theorem rose_injective_off_pole {θ ψ : ℝ} (hθ : θ ∈ Ico 0 Real.pi) (hψ : ψ ∈ Ico 0 Real.pi)
    (hn : roseRadius θ ≠ 0)
    (he : signedPolarPoint (roseRadius θ) θ = signedPolarPoint (roseRadius ψ) ψ) : θ = ψ := by
  have hp : roseRadius ψ ≠ 0 := by
    intro hp
    rw [hp, signedPolarPoint_zero_radius, signedPolarPoint_eq_zero_iff] at he
    exact hn he
  have hx := congrArg Complex.re he
  have hy := congrArg Complex.im he
  rw [signedPolarPoint_re, signedPolarPoint_re] at hx
  rw [signedPolarPoint_im, signedPolarPoint_im] at hy
  have ht : roseRadius θ * roseRadius ψ * Real.sin (θ - ψ) = 0 := by
    rw [Real.sin_sub]
    nlinarith [congrArg (fun q : ℝ ↦ q * roseRadius ψ * Real.cos ψ) hy,
      congrArg (fun q : ℝ ↦ q * roseRadius ψ * Real.sin ψ) hx]
  have hz : Real.sin (θ - ψ) = 0 :=
    (mul_eq_zero.mp ht).resolve_left (mul_ne_zero hn hp)
  have hdiff := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hθ.1, hψ.2])
    (by linarith [hθ.2, hψ.1])).mp hz
  linarith

theorem rose_x_axis (x : ℝ) : (⟨x, 0⟩ : ℂ) ∈ polarCurveImage roseRadius ↔ x = 0 := by
  rw [rose_mem_curve_image_iff]
  change (x ^ 2 + 0 ^ 2) ^ 2 = 0 * (3 * x ^ 2 - 0 ^ 2) ↔ _
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, zero_mul, sq_eq_zero_iff]

theorem rose_y_axis (y : ℝ) :
    (⟨0, y⟩ : ℂ) ∈ polarCurveImage roseRadius ↔ y = 0 ∨ y = -1 := by
  rw [rose_mem_curve_image_iff]
  change (0 ^ 2 + y ^ 2) ^ 2 = y * (3 * 0 ^ 2 - y ^ 2) ↔ _
  constructor
  · intro h
    have hp : y ^ 3 * (y + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (eq_zero_of_pow_eq_zero hp)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num


theorem rose_tangents_iff (θ : ℝ) :
    (HasHorizontalPolarTangent univ roseRadius θ ↔ roseDY θ = 0) ∧
      (HasVerticalPolarTangent univ roseRadius θ ↔ roseDX θ = 0) := by
  have hX := (rose_actual_derivatives θ).2.1
  have hY := (rose_actual_derivatives θ).2.2
  have hv := (rose_speed_sq_and_curvature_numerator θ).2.2.1
  constructor
  · constructor
    · exact fun h ↦ secant_zero_implies_deriv_zero hY hX h
    · intro hy
      apply source_horizontal_polar_tangent Filter.univ_mem (rose_actual_derivatives θ).1 hy
      change roseDX θ ≠ 0
      intro hx
      rw [hx, hy] at hv
      norm_num at hv
  · constructor
    · exact fun h ↦ secant_zero_implies_deriv_zero hX hY h
    · intro hx
      apply source_vertical_polar_tangent Filter.univ_mem (rose_actual_derivatives θ).1 hx
      change roseDY θ ≠ 0
      intro hy
      rw [hx, hy] at hv
      norm_num at hv


theorem rose_tangent_conditions (θ : ℝ) :
    (HasHorizontalPolarTangent univ roseRadius θ ↔
      Real.sin θ = 0 ∨ Real.cos θ = 0 ∨ Real.sin θ ^ 2 = 3 / 8) ∧
    (HasVerticalPolarTangent univ roseRadius θ ↔
      16 * Real.cos θ ^ 4 - 14 * Real.cos θ ^ 2 + 1 = 0) := by
  rw [(rose_tangents_iff θ).1, (rose_tangents_iff θ).2]
  have hY : roseDY θ = 2 * Real.sin θ * Real.cos θ * (3 - 8 * Real.sin θ ^ 2) := by
    dsimp only [roseDY, roseRadius]
    rw [Real.sin_three_mul, Real.cos_three_mul]
    nlinarith [congrArg (fun q : ℝ ↦ 12 * Real.sin θ * Real.cos θ * q) (Real.sin_sq_add_cos_sq θ)]
  have hX : roseDX θ = 16 * Real.cos θ ^ 4 - 14 * Real.cos θ ^ 2 + 1 := by
    dsimp only [roseDX, roseRadius]
    rw [Real.sin_three_mul, Real.cos_three_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ,
      congrArg (fun q : ℝ ↦ 4 * (Real.sin θ ^ 2 - Real.cos θ ^ 2) * q) (Real.sin_sq_add_cos_sq θ)]
  refine ⟨?_, by rw [hX]⟩
  rw [hY, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (((h2 | hs) | hc) | hp)
    · norm_num at h2
    · exact Or.inl hs
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (hs | hc | hp)
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr (by linarith)


theorem rose_pole_tangents {θ : ℝ} (hr : roseRadius θ = 0) :
    Real.cos θ ≠ 0 ∧
      ((Real.sin θ / Real.cos θ) ^ 2 = 0 ∨ (Real.sin θ / Real.cos θ) ^ 2 = 3) ∧
      DomainLimit (xSecantDomain univ roseRadius θ)
        (fun t ↦ (polarY roseRadius t - polarY roseRadius θ) /
          (polarX roseRadius t - polarX roseRadius θ)) θ (Real.sin θ / Real.cos θ) := by
  have hfac : Real.sin θ * (3 - 4 * Real.sin θ ^ 2) = 0 := by
    rw [roseRadius, Real.sin_three_mul] at hr
    nlinarith
  have hsq : Real.sin θ ^ 2 = 0 ∨ Real.sin θ ^ 2 = 3 / 4 := by
    rcases mul_eq_zero.mp hfac with hs | hs
    · exact Or.inl (by rw [hs]; norm_num)
    · exact Or.inr (by linarith)
  have hc : Real.cos θ ≠ 0 := by
    intro hc
    rcases hsq with hs | hs <;> nlinarith [Real.sin_sq_add_cos_sq θ]
  have hC : Real.cos (3 * θ) ≠ 0 := by
    intro hC
    have h := Real.sin_sq_add_cos_sq (3 * θ)
    change roseRadius θ ^ 2 + Real.cos (3 * θ) ^ 2 = 1 at h
    rw [hr, hC] at h
    norm_num at h
  have hx : 3 * Real.cos (3 * θ) * Real.cos θ - roseRadius θ * Real.sin θ ≠ 0 := by
    rw [hr, zero_mul, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hC) hc
  refine ⟨hc, ?_, ?_⟩
  · rcases hsq with hs | hs
    · exact Or.inl (by rw [div_pow, hs, zero_div])
    · right
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hc)).mpr
      nlinarith [Real.sin_sq_add_cos_sq θ]
  · have h := polar_secant_slope_limit Filter.univ_mem (rose_actual_derivatives θ).1 hx
    convert h using 1
    rw [hr]
    simp only [zero_mul, add_zero, sub_zero]
    field_simp [hC, hc]


theorem rose_coordinate_extrema (θ : ℝ) :
    ((IsLocalMinimumOn (polarX roseRadius) univ θ ↔ roseDX θ = 0 ∧ 0 < roseDDX θ) ∧
      (IsLocalMaximumOn (polarX roseRadius) univ θ ↔ roseDX θ = 0 ∧ roseDDX θ < 0)) ∧
    ((IsLocalMinimumOn (polarY roseRadius) univ θ ↔ roseDY θ = 0 ∧ 0 < roseDDY θ) ∧
      (IsLocalMaximumOn (polarY roseRadius) univ θ ↔ roseDY θ = 0 ∧ roseDDY θ < 0)) := by
  have hk : 0 < roseDX θ * roseDDY θ - roseDY θ * roseDDX θ :=
    lt_of_lt_of_le (by norm_num) (rose_speed_sq_and_curvature_numerator θ).2.2.2
  have hx : deriv (polarX roseRadius) θ = 0 → deriv (deriv (polarX roseRadius)) θ ≠ 0 := by
    rw [(rose_actual_derivatives θ).2.1.deriv, (rose_actual_second_derivatives θ).1.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hy : deriv (polarY roseRadius) θ = 0 → deriv (deriv (polarY roseRadius)) θ ≠ 0 := by
    rw [(rose_actual_derivatives θ).2.2.deriv, (rose_actual_second_derivatives θ).2.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hX := nondegenerate_extrema_iff (rose_actual_derivatives θ).2.1.differentiableAt hx
  have hY := nondegenerate_extrema_iff (rose_actual_derivatives θ).2.2.differentiableAt hy
  rw [(rose_actual_derivatives θ).2.1.deriv, (rose_actual_second_derivatives θ).1.deriv] at hX
  rw [(rose_actual_derivatives θ).2.2.deriv, (rose_actual_second_derivatives θ).2.deriv] at hY
  exact ⟨hX, hY⟩


theorem rose_pole_parameters (θ : ℝ) :
    signedPolarPoint (roseRadius θ) θ = 0 ↔ ∃ n : ℤ, θ = (n : ℝ) * Real.pi / 3 := by
  rw [signedPolarPoint_eq_zero_iff, roseRadius, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩


theorem rose_radius_second_derivative (θ : ℝ) :
    HasDerivAt (deriv roseRadius) (-9 * roseRadius θ) θ := by
  have h := (((hasDerivAt_id θ).const_mul 3).cos).const_mul 3
  have hc : HasDerivAt (fun t : ℝ ↦ 3 * Real.cos (3 * t)) (-9 * roseRadius θ) θ := by
    apply h.congr_deriv
    simp only [id_eq, mul_one, roseRadius]
    ring
  apply hc.congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (rose_actual_derivatives t).1.deriv

theorem rose_radius_extrema (θ : ℝ) :
    (IsLocalMinimumOn roseRadius univ θ ↔ roseRadius θ = -1) ∧
      (IsLocalMaximumOn roseRadius univ θ ↔ roseRadius θ = 1) := by
  have ht : roseRadius θ ^ 2 + Real.cos (3 * θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * θ)
  have hne : deriv roseRadius θ = 0 → deriv (deriv roseRadius) θ ≠ 0 := by
    rw [(rose_actual_derivatives θ).1.deriv, (rose_radius_second_derivative θ).deriv]
    intro hd hdd
    nlinarith
  have h := nondegenerate_extrema_iff (rose_actual_derivatives θ).1.differentiableAt hne
  rw [(rose_actual_derivatives θ).1.deriv, (rose_radius_second_derivative θ).deriv] at h
  constructor
  · rw [h.1]
    constructor
    · rintro ⟨hc, hp⟩
      have he : roseRadius θ ^ 2 = 1 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show roseRadius θ ^ 2 = (1 : ℝ) ^ 2 from by simpa only [one_pow] using he) with hr | hr
      · nlinarith
      · exact hr
    · intro hr
      have hc : Real.cos (3 * θ) = 0 := sq_eq_zero_iff.mp (by nlinarith)
      rw [hr, hc]
      norm_num
  · rw [h.2]
    constructor
    · rintro ⟨hc, hn⟩
      have he : roseRadius θ ^ 2 = 1 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show roseRadius θ ^ 2 = (1 : ℝ) ^ 2 from by simpa only [one_pow] using he) with hr | hr
      · exact hr
      · nlinarith
    · intro hr
      have hc : Real.cos (3 * θ) = 0 := sq_eq_zero_iff.mp (by nlinarith)
      rw [hr, hc]
      norm_num


theorem source_rose_complete_polar_curve_investigation :
    (∀ z : ℂ, z ∈ polarCurveImage roseRadius ↔
      (z.re ^ 2 + z.im ^ 2) ^ 2 = z.im * (3 * z.re ^ 2 - z.im ^ 2)) ∧
    (∀ θ : ℝ, signedPolarPoint (roseRadius θ) θ = 0 ↔ Real.sin (3 * θ) = 0) ∧
    (∀ θ : ℝ, HasDerivAt roseRadius (3 * Real.cos (3 * θ)) θ ∧
      HasDerivAt (polarX roseRadius) (roseDX θ) θ ∧
      HasDerivAt (polarY roseRadius) (roseDY θ) θ) ∧
    (∀ θ : ℝ, HasHorizontalPolarTangent univ roseRadius θ ↔ roseDY θ = 0) ∧
    (∀ θ : ℝ, HasVerticalPolarTangent univ roseRadius θ ↔ roseDX θ = 0) ∧
    (∀ θ : ℝ, signedPolarPoint (roseRadius (θ + Real.pi)) (θ + Real.pi) =
      signedPolarPoint (roseRadius θ) θ) ∧
    (∀ z : ℂ, z ∈ polarCurveImage roseRadius ↔ perpendicularAxisReflection z ∈ polarCurveImage roseRadius) :=
  ⟨rose_mem_curve_image_iff, fun θ ↦ signedPolarPoint_eq_zero_iff (roseRadius θ) θ,
    rose_actual_derivatives, fun θ ↦ (rose_tangents_iff θ).1,
    fun θ ↦ (rose_tangents_iff θ).2, rose_point_period, rose_perpendicular_symmetry⟩

end calculus.Chapter04.Section04ThreePetalRosePolarCurveInvestigation
