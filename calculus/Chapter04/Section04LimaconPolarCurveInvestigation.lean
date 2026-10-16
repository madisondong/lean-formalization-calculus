import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

/-!
# Bài 4.4.16(b): limaçon r=1+2cosφ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2794. Góc chạy trên ℝ; bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04LimaconPolarCurveInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

theorem limacon_source_formula (θ : ℝ) : cosineRadius 2 θ = 1 + 2 * Real.cos θ := rfl

theorem limacon_radius_bounds (θ : ℝ) : -1 ≤ cosineRadius 2 θ ∧ cosineRadius 2 θ ≤ 3 := by
  rw [limacon_source_formula]
  constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

theorem limacon_radius_signs (θ : ℝ) :
    (cosineRadius 2 θ < 0 ↔ Real.cos θ < -1 / 2) ∧
    (cosineRadius 2 θ ≤ 0 ↔ Real.cos θ ≤ -1 / 2) ∧
    (cosineRadius 2 θ = 0 ↔ Real.cos θ = -1 / 2) := by
  rw [limacon_source_formula]
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> constructor <;> intro h <;> linarith

theorem limacon_pole_iff (θ : ℝ) :
    signedPolarPoint (cosineRadius 2 θ) θ = 0 ↔ Real.cos θ = -1 / 2 := by
  rw [signedPolarPoint_eq_zero_iff]
  exact (limacon_radius_signs θ).2.2

theorem limacon_pole_exists : ∃ θ : ℝ, cosineRadius 2 θ = 0 := by
  refine ⟨Real.pi - Real.pi / 3, ?_⟩
  rw [limacon_source_formula, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num


theorem limacon_mem_curve_image_iff (z : ℂ) :
    z ∈ polarCurveImage (cosineRadius 2) ↔
      (z.re ^ 2 + z.im ^ 2 - 2 * z.re) ^ 2 = z.re ^ 2 + z.im ^ 2 :=
  cosine_mem_curve_image_iff 2 limacon_pole_exists z


theorem limacon_loops :
    cosineClosedBranch 2 false ∪ cosineClosedBranch 2 true = polarCurveImage (cosineRadius 2) ∧
      cosineClosedBranch 2 false ∩ cosineClosedBranch 2 true = {0} := by
  refine ⟨(cosine_branches_partition 2).1, subset_antisymm (cosine_branches_partition 2).2 ?_⟩
  intro z hz
  rw [mem_singleton_iff] at hz
  subst z
  obtain ⟨θ, hθ⟩ := limacon_pole_exists
  constructor
  · exact ⟨θ, by change 0 ≤ cosineRadius 2 θ; rw [hθ],
      by rw [hθ, signedPolarPoint_zero_radius]⟩
  · exact ⟨θ, by change cosineRadius 2 θ ≤ 0; rw [hθ],
      by rw [hθ, signedPolarPoint_zero_radius]⟩


theorem limacon_loop_distance (θ : ℝ) :
    (cosineRadius 2 θ ≤ 0 → ‖signedPolarPoint (cosineRadius 2 θ) θ‖ ≤ 1) ∧
      (0 ≤ cosineRadius 2 θ → ‖signedPolarPoint (cosineRadius 2 θ) θ‖ ≤ 3) := by
  rw [norm_signedPolarPoint]
  constructor
  · intro hn
    rw [abs_of_nonpos hn]
    linarith [(limacon_radius_bounds θ).1]
  · intro hp
    rw [abs_of_nonneg hp]
    exact (limacon_radius_bounds θ).2


theorem limacon_x_bounds (θ : ℝ) :
    -1 / 8 ≤ polarX (cosineRadius 2) θ ∧ polarX (cosineRadius 2) θ ≤ 3 ∧
      (polarX (cosineRadius 2) θ = -1 / 8 ↔ Real.cos θ = -1 / 4) ∧
      (polarX (cosineRadius 2) θ = 3 ↔ Real.cos θ = 1) := by
  have he : polarX (cosineRadius 2) θ = Real.cos θ + 2 * Real.cos θ ^ 2 := by
    dsimp only [polarX, cosineRadius]
    ring
  rw [he]
  have hc := Real.cos_le_one θ
  have hn := Real.neg_one_le_cos θ
  have hs := Real.sin_sq_add_cos_sq θ
  refine ⟨by nlinarith [sq_nonneg (Real.cos θ + 1 / 4)],
    by nlinarith [sq_nonneg (Real.sin θ)], ?_, ?_⟩
  · constructor
    · intro h
      have hz : (Real.cos θ + 1 / 4) ^ 2 = 0 := by nlinarith
      have hh := sq_eq_zero_iff.mp hz
      linarith
    · intro h
      rw [h]
      norm_num
  · constructor
    · intro h
      have hp : (Real.cos θ - 1) * (2 * Real.cos θ + 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with hp | hp <;> linarith
    · intro h
      rw [h]
      norm_num


theorem limacon_inner_x_bounds {θ : ℝ} (hr : cosineRadius 2 θ ≤ 0) :
    0 ≤ polarX (cosineRadius 2) θ ∧ polarX (cosineRadius 2) θ ≤ 1 ∧
      (polarX (cosineRadius 2) θ = 1 ↔ Real.cos θ = -1) := by
  have hc : Real.cos θ ≤ -1 / 2 := (limacon_radius_signs θ).2.1.mp hr
  have hn := Real.neg_one_le_cos θ
  have he : polarX (cosineRadius 2) θ = Real.cos θ + 2 * Real.cos θ ^ 2 := by
    dsimp only [polarX, cosineRadius]
    ring
  rw [he]
  have hp : 0 ≤ Real.cos θ * (1 + 2 * Real.cos θ) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hq : 0 ≤ (Real.cos θ + 1) * (1 - 2 * Real.cos θ) :=
    mul_nonneg (by linarith) (by linarith)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  constructor
  · intro h
    have hz : (Real.cos θ + 1) * (2 * Real.cos θ - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz <;> linarith
  · intro h
    rw [h]
    norm_num

theorem limacon_x_axis (x : ℝ) :
    (⟨x, 0⟩ : ℂ) ∈ polarCurveImage (cosineRadius 2) ↔ x = 0 ∨ x = 1 ∨ x = 3 := by
  rw [limacon_mem_curve_image_iff]
  change (x ^ 2 + 0 ^ 2 - 2 * x) ^ 2 = x ^ 2 + 0 ^ 2 ↔ _
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · have hh : x * (x - 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (by linarith))
    · have hh : x * (x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem limacon_y_axis (y : ℝ) :
    (⟨0, y⟩ : ℂ) ∈ polarCurveImage (cosineRadius 2) ↔ y = 0 ∨ y = 1 ∨ y = -1 := by
  rw [limacon_mem_curve_image_iff]
  change (0 ^ 2 + y ^ 2 - 2 * 0) ^ 2 = 0 ^ 2 + y ^ 2 ↔ _
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add, sub_zero]
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · have hh : y * (y - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (by linarith))
    · have hh : y * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num


theorem limacon_speed_sq_and_curvature_numerator_lower_bounds (θ : ℝ) :
    1 ≤ cosineXFirst 2 θ ^ 2 + cosineYFirst 2 θ ^ 2 ∧
      3 ≤ cosineXFirst 2 θ * cosineYSecond 2 θ - cosineYFirst 2 θ * cosineXSecond 2 θ := by
  rw [cosine_speed_square, cosine_curvature_numerator]
  constructor <;> nlinarith [Real.neg_one_le_cos θ]


theorem limacon_horizontal_iff (θ : ℝ) :
    HasHorizontalPolarTangent univ (cosineRadius 2) θ ↔
      4 * Real.cos θ ^ 2 + Real.cos θ - 2 = 0 := by
  have he : cosineYFirst 2 θ = 4 * Real.cos θ ^ 2 + Real.cos θ - 2 := by
    dsimp only [cosineYFirst]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  constructor
  · intro h
    rw [← he]
    exact cosine_horizontal_necessary h
  · intro hy
    apply cosine_horizontal_of (by rwa [he])
    intro hx
    have hs := (limacon_speed_sq_and_curvature_numerator_lower_bounds θ).1
    rw [hx, he, hy] at hs
    norm_num at hs


theorem limacon_horizontal_roots (θ : ℝ) :
    HasHorizontalPolarTangent univ (cosineRadius 2) θ ↔
      Real.cos θ = (-1 + Real.sqrt 33) / 8 ∨ Real.cos θ = (-1 - Real.sqrt 33) / 8 := by
  rw [limacon_horizontal_iff]
  have hs : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hp : (8 * Real.cos θ + 1 - Real.sqrt 33) *
        (8 * Real.cos θ + 1 + Real.sqrt 33) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> rw [h] <;> nlinarith


theorem limacon_vertical_iff (θ : ℝ) :
    HasVerticalPolarTangent univ (cosineRadius 2) θ ↔
      Real.cos θ = 1 ∨ Real.cos θ = -1 ∨ Real.cos θ = -1 / 4 := by
  have he : cosineXFirst 2 θ = 0 ↔
      Real.cos θ = 1 ∨ Real.cos θ = -1 ∨ Real.cos θ = -1 / 4 := by
    dsimp only [cosineXFirst]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with hs | hc
      · rcases Real.sin_eq_zero_iff_cos_eq.mp (neg_eq_zero.mp hs) with hc | hc
        · exact Or.inl hc
        · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (by linarith))
    · rintro (hc | hc | hc)
      · rw [Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hc)]
        simp only [neg_zero, zero_mul]
      · rw [Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)]
        simp only [neg_zero, zero_mul]
      · rw [hc]
        norm_num
  constructor
  · intro h
    exact he.mp (cosine_vertical_necessary h)
  · intro h
    have hx := he.mpr h
    apply cosine_vertical_of hx
    intro hy
    have hs := (limacon_speed_sq_and_curvature_numerator_lower_bounds θ).1
    rw [hx, hy] at hs
    norm_num at hs


theorem limacon_pole_tangent {θ : ℝ} (hc : Real.cos θ = -1 / 2) :
    cosineXFirst 2 θ = Real.sin θ ∧ cosineYFirst 2 θ = -3 / 2 ∧
      (-2 * Real.sin θ) ^ 2 = 3 ∧
      DomainLimit (xSecantDomain univ (cosineRadius 2) θ)
        (fun t ↦ (polarY (cosineRadius 2) t - polarY (cosineRadius 2) θ) /
          (polarX (cosineRadius 2) t - polarX (cosineRadius 2) θ)) θ (-2 * Real.sin θ) := by
  have hs : Real.sin θ ^ 2 = 3 / 4 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hn : Real.sin θ ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hr : cosineRadius 2 θ = 0 := (limacon_radius_signs θ).2.2.mpr hc
  have hx : -2 * Real.sin θ * Real.cos θ - cosineRadius 2 θ * Real.sin θ ≠ 0 := by
    rw [hc, hr]
    convert hn using 1
    ring
  refine ⟨?_, ?_, by nlinarith, ?_⟩
  · dsimp only [cosineXFirst]
    rw [hc]
    ring
  · dsimp only [cosineYFirst]
    nlinarith
  · have hl := polar_secant_slope_limit (D := univ) Filter.univ_mem
      (cosineRadius_hasDerivAt 2 θ) hx
    convert hl using 1
    rw [hc, hr]
    field_simp [hn]
    nlinarith


theorem limacon_coordinate_extrema (θ : ℝ) :
    ((IsLocalMinimumOn (polarX (cosineRadius 2)) univ θ ↔
      cosineXFirst 2 θ = 0 ∧ 0 < cosineXSecond 2 θ) ∧
    (IsLocalMaximumOn (polarX (cosineRadius 2)) univ θ ↔
      cosineXFirst 2 θ = 0 ∧ cosineXSecond 2 θ < 0)) ∧
    ((IsLocalMinimumOn (polarY (cosineRadius 2)) univ θ ↔
      cosineYFirst 2 θ = 0 ∧ 0 < cosineYSecond 2 θ) ∧
    (IsLocalMaximumOn (polarY (cosineRadius 2)) univ θ ↔
      cosineYFirst 2 θ = 0 ∧ cosineYSecond 2 θ < 0)) :=
  cosine_coordinate_extrema (lt_of_lt_of_le (by norm_num) (limacon_speed_sq_and_curvature_numerator_lower_bounds θ).2)


theorem source_limacon_complete_polar_curve_investigation :
    (∀ θ : ℝ, cosineRadius 2 θ = 1 + 2 * Real.cos θ ∧
      -1 ≤ cosineRadius 2 θ ∧ cosineRadius 2 θ ≤ 3) ∧
    (∀ z : ℂ, z ∈ polarCurveImage (cosineRadius 2) ↔
      (z.re ^ 2 + z.im ^ 2 - 2 * z.re) ^ 2 = z.re ^ 2 + z.im ^ 2) ∧
    (∀ θ : ℝ, signedPolarPoint (cosineRadius 2 θ) θ = 0 ↔ Real.cos θ = -1 / 2) ∧
    (cosineClosedBranch 2 false ∪ cosineClosedBranch 2 true = polarCurveImage (cosineRadius 2) ∧
      cosineClosedBranch 2 false ∩ cosineClosedBranch 2 true = {0}) ∧
    (∀ θ : ℝ, HasDerivAt (cosineRadius 2) (-2 * Real.sin θ) θ ∧
      HasDerivAt (polarX (cosineRadius 2)) (cosineXFirst 2 θ) θ ∧
      HasDerivAt (polarY (cosineRadius 2)) (cosineYFirst 2 θ) θ ∧
      HasDerivAt (deriv (polarX (cosineRadius 2))) (cosineXSecond 2 θ) θ ∧
      HasDerivAt (deriv (polarY (cosineRadius 2))) (cosineYSecond 2 θ) θ) ∧
    (∀ θ : ℝ, (IsLocalMinimumOn (cosineRadius 2) univ θ ↔ Real.cos θ = -1) ∧
      (IsLocalMaximumOn (cosineRadius 2) univ θ ↔ Real.cos θ = 1)) ∧
    (∀ θ : ℝ, HasHorizontalPolarTangent univ (cosineRadius 2) θ ↔
      Real.cos θ = (-1 + Real.sqrt 33) / 8 ∨ Real.cos θ = (-1 - Real.sqrt 33) / 8) ∧
    (∀ θ : ℝ, HasVerticalPolarTangent univ (cosineRadius 2) θ ↔
      Real.cos θ = 1 ∨ Real.cos θ = -1 ∨ Real.cos θ = -1 / 4) ∧
    (∀ z : ℂ, z ∈ polarCurveImage (cosineRadius 2) ↔
      polarAxisReflection z ∈ polarCurveImage (cosineRadius 2)) ∧
    (∀ θ : ℝ, signedPolarPoint (cosineRadius 2 (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
      signedPolarPoint (cosineRadius 2 θ) θ) ∧
    (∀ θ ψ : ℝ, θ ∈ Ico 0 (2 * Real.pi) → ψ ∈ Ico 0 (2 * Real.pi) →
      cosineRadius 2 θ ≠ 0 →
      signedPolarPoint (cosineRadius 2 θ) θ = signedPolarPoint (cosineRadius 2 ψ) ψ → θ = ψ) := by
  refine ⟨fun θ ↦ ⟨limacon_source_formula θ, limacon_radius_bounds θ⟩,
    limacon_mem_curve_image_iff, limacon_pole_iff, limacon_loops, ?_,
    fun θ ↦ cosine_radius_extrema 2 θ (by norm_num), limacon_horizontal_roots,
    limacon_vertical_iff, cosine_axis_symmetry 2, cosine_point_periodic 2,
    fun _ _ hθ hψ hn he ↦ cosine_point_injective_off_pole hθ hψ hn he⟩
  intro θ
  exact ⟨cosineRadius_hasDerivAt 2 θ, cosineX_hasDerivAt 2 θ, cosineY_hasDerivAt 2 θ,
    cosineX_second_hasDerivAt 2 θ, cosineY_second_hasDerivAt 2 θ⟩

end calculus.Chapter04.Section04LimaconPolarCurveInvestigation
