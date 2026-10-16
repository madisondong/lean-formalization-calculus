import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Họ đường cong cực dạng cos

Nguồn: `C04-S04-exercise-016.p08`, `source/Ch4_hamsokhavi.tex`, dòng 2791–2804. Xét `a, n, m ∈ ℝ`, `m ≠ 0`, mọi góc thực và bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04CosineFamilyPolarCurveInvestigation

open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

def familyRadius (a k φ : ℝ) : ℝ := a * Real.cos (k * φ)
def familyRadiusFirst (a k φ : ℝ) : ℝ := -a * k * Real.sin (k * φ)
def familyRadiusSecond (a k φ : ℝ) : ℝ := -a * k ^ 2 * Real.cos (k * φ)
def familyPoint (a k φ : ℝ) : ℂ := signedPolarPoint (familyRadius a k φ) φ
def familyXFirst (a k φ : ℝ) : ℝ :=
  familyRadiusFirst a k φ * Real.cos φ - familyRadius a k φ * Real.sin φ
def familyYFirst (a k φ : ℝ) : ℝ :=
  familyRadiusFirst a k φ * Real.sin φ + familyRadius a k φ * Real.cos φ
def familyXSecond (a k φ : ℝ) : ℝ :=
  -a * (1 + k ^ 2) * Real.cos (k * φ) * Real.cos φ +
    2 * a * k * Real.sin (k * φ) * Real.sin φ
def familyYSecond (a k φ : ℝ) : ℝ :=
  -a * (1 + k ^ 2) * Real.cos (k * φ) * Real.sin φ -
    2 * a * k * Real.sin (k * φ) * Real.cos φ


theorem source_parameter_radius (a n m φ : ℝ) (_hm : m ≠ 0) :
    familyRadius a (n / m) φ = a * Real.cos ((n / m) * φ) := rfl

theorem family_actual_derivatives (a k φ : ℝ) :
    HasDerivAt (familyRadius a k) (familyRadiusFirst a k φ) φ ∧
      HasDerivAt (polarX (familyRadius a k)) (familyXFirst a k φ) φ ∧
      HasDerivAt (polarY (familyRadius a k)) (familyYFirst a k φ) φ := by
  have hr : HasDerivAt (familyRadius a k) (familyRadiusFirst a k φ) φ := by
    have h := (((hasDerivAt_id φ).const_mul k).cos).const_mul a
    apply h.congr_deriv
    simp only [familyRadiusFirst, id_eq, mul_one]
    ring
  exact ⟨hr, polarX_hasDerivAt hr, polarY_hasDerivAt hr⟩

theorem family_radius_first_hasDerivAt (a k φ : ℝ) :
    HasDerivAt (familyRadiusFirst a k) (familyRadiusSecond a k φ) φ := by
  have h := (((hasDerivAt_id φ).const_mul k).sin).const_mul (-a * k)
  apply h.congr_deriv
  simp only [familyRadiusSecond, id_eq, mul_one]
  ring

theorem family_radius_second_derivative (a k φ : ℝ) :
    HasDerivAt (deriv (familyRadius a k)) (familyRadiusSecond a k φ) φ := by
  apply (family_radius_first_hasDerivAt a k φ).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (family_actual_derivatives a k t).1.deriv

theorem family_first_coordinate_derivatives (a k φ : ℝ) :
    HasDerivAt (familyXFirst a k) (familyXSecond a k φ) φ ∧
      HasDerivAt (familyYFirst a k) (familyYSecond a k φ) φ := by
  have hr := (family_actual_derivatives a k φ).1
  have hdr := family_radius_first_hasDerivAt a k φ
  constructor
  · have h := (hdr.mul (Real.hasDerivAt_cos φ)).sub (hr.mul (Real.hasDerivAt_sin φ))
    apply h.congr_deriv
    simp only [familyRadius, familyRadiusFirst, familyRadiusSecond, familyXSecond]
    ring
  · have h := (hdr.mul (Real.hasDerivAt_sin φ)).add (hr.mul (Real.hasDerivAt_cos φ))
    apply h.congr_deriv
    simp only [familyRadius, familyRadiusFirst, familyRadiusSecond, familyYSecond]
    ring

theorem family_actual_second_derivatives (a k φ : ℝ) :
    HasDerivAt (deriv (polarX (familyRadius a k))) (familyXSecond a k φ) φ ∧
      HasDerivAt (deriv (polarY (familyRadius a k))) (familyYSecond a k φ) φ := by
  constructor
  · apply (family_first_coordinate_derivatives a k φ).1.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (family_actual_derivatives a k t).2.1.deriv
  · apply (family_first_coordinate_derivatives a k φ).2.congr_of_eventuallyEq
    exact Eventually.of_forall fun t ↦ (family_actual_derivatives a k t).2.2.deriv


theorem family_speed_sq_and_curvature_numerator (a k φ : ℝ) :
    familyXFirst a k φ ^ 2 + familyYFirst a k φ ^ 2 =
      a ^ 2 * (k ^ 2 * Real.sin (k * φ) ^ 2 + Real.cos (k * φ) ^ 2) ∧
      familyXFirst a k φ * familyYSecond a k φ -
        familyYFirst a k φ * familyXSecond a k φ =
      a ^ 2 * ((1 + k ^ 2) * Real.cos (k * φ) ^ 2 +
        2 * k ^ 2 * Real.sin (k * φ) ^ 2) := by
  constructor
  · dsimp only [familyXFirst, familyYFirst, familyRadiusFirst, familyRadius]
    calc
      _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) *
        (a ^ 2 * (k ^ 2 * Real.sin (k * φ) ^ 2 + Real.cos (k * φ) ^ 2)) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · dsimp only [familyXFirst, familyYFirst, familyRadiusFirst, familyRadius,
      familyXSecond, familyYSecond]
    calc
      _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) *
        (a ^ 2 * ((1 + k ^ 2) * Real.cos (k * φ) ^ 2 +
          2 * k ^ 2 * Real.sin (k * φ) ^ 2)) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem family_regular_and_positive_curvature_numerator (a k φ : ℝ) (ha : a ≠ 0) :
    0 < familyXFirst a k φ ^ 2 + familyYFirst a k φ ^ 2 ∧
      0 < familyXFirst a k φ * familyYSecond a k φ -
        familyYFirst a k φ * familyXSecond a k φ := by
  rw [(family_speed_sq_and_curvature_numerator a k φ).1, (family_speed_sq_and_curvature_numerator a k φ).2]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  by_cases hk : k = 0
  · subst k
    simpa using (And.intro ha2 ha2)
  · have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
    have htrig := Real.sin_sq_add_cos_sq (k * φ)
    by_cases hc : Real.cos (k * φ) = 0
    · have hs : Real.sin (k * φ) ^ 2 = 1 := by rw [hc] at htrig; nlinarith
      rw [hc, hs]
      constructor <;> positivity
    · have hc2 : 0 < Real.cos (k * φ) ^ 2 := sq_pos_of_ne_zero hc
      have hi : 0 < k ^ 2 * Real.sin (k * φ) ^ 2 + Real.cos (k * φ) ^ 2 := by
        nlinarith [mul_nonneg hk2.le (sq_nonneg (Real.sin (k * φ)))]
      have hj : 0 < (1 + k ^ 2) * Real.cos (k * φ) ^ 2 +
          2 * k ^ 2 * Real.sin (k * φ) ^ 2 := by
        have hp : 0 < (1 + k ^ 2) * Real.cos (k * φ) ^ 2 := mul_pos (by positivity) hc2
        nlinarith [mul_nonneg (show 0 ≤ 2 * k ^ 2 by positivity)
          (sq_nonneg (Real.sin (k * φ)))]
      exact ⟨mul_pos ha2 hi, mul_pos ha2 hj⟩


theorem family_singular_iff (a k φ : ℝ) :
    (familyXFirst a k φ = 0 ∧ familyYFirst a k φ = 0) ↔ a = 0 := by
  constructor
  · rintro ⟨hx, hy⟩
    by_contra ha
    have h := (family_regular_and_positive_curvature_numerator a k φ ha).1
    rw [hx, hy] at h
    norm_num at h
  · rintro rfl
    simp [familyXFirst, familyYFirst, familyRadiusFirst, familyRadius]


theorem family_tangents_iff (a k φ : ℝ) (ha : a ≠ 0) :
    (HasHorizontalPolarTangent univ (familyRadius a k) φ ↔ familyYFirst a k φ = 0) ∧
      (HasVerticalPolarTangent univ (familyRadius a k) φ ↔ familyXFirst a k φ = 0) := by
  have hreg := (family_regular_and_positive_curvature_numerator a k φ ha).1
  constructor
  · constructor
    · intro h
      exact secant_zero_implies_deriv_zero (family_actual_derivatives a k φ).2.2
        (family_actual_derivatives a k φ).2.1 h
    · intro hy
      have hx : familyXFirst a k φ ≠ 0 := by
        intro hx
        rw [hx, hy] at hreg
        norm_num at hreg
      exact (horizontal_polar_tangent_iff (show univ ∈ 𝓝 φ from Filter.univ_mem)
        (family_actual_derivatives a k φ).1 hx).mpr hy
  · constructor
    · intro h
      exact secant_zero_implies_deriv_zero (family_actual_derivatives a k φ).2.1
        (family_actual_derivatives a k φ).2.2 h
    · intro hx
      have hy : familyYFirst a k φ ≠ 0 := by
        intro hy
        rw [hx, hy] at hreg
        norm_num at hreg
      exact (vertical_polar_tangent_iff (show univ ∈ 𝓝 φ from Filter.univ_mem)
        (family_actual_derivatives a k φ).1 hy).mpr hx

theorem family_actual_secant_slope (a k φ : ℝ) (hx : familyXFirst a k φ ≠ 0) :
    DomainLimit (xSecantDomain univ (familyRadius a k) φ)
      (fun t ↦ (polarY (familyRadius a k) t - polarY (familyRadius a k) φ) /
        (polarX (familyRadius a k) t - polarX (familyRadius a k) φ)) φ
      (familyYFirst a k φ / familyXFirst a k φ) :=
  polar_secant_slope_limit (show univ ∈ 𝓝 φ from Filter.univ_mem)
    (family_actual_derivatives a k φ).1 hx

theorem family_coordinate_extrema (a k φ : ℝ) (ha : a ≠ 0) :
    ((IsLocalMinimumOn (polarX (familyRadius a k)) univ φ ↔
       familyXFirst a k φ = 0 ∧ 0 < familyXSecond a k φ) ∧
     (IsLocalMaximumOn (polarX (familyRadius a k)) univ φ ↔
       familyXFirst a k φ = 0 ∧ familyXSecond a k φ < 0)) ∧
    ((IsLocalMinimumOn (polarY (familyRadius a k)) univ φ ↔
       familyYFirst a k φ = 0 ∧ 0 < familyYSecond a k φ) ∧
     (IsLocalMaximumOn (polarY (familyRadius a k)) univ φ ↔
       familyYFirst a k φ = 0 ∧ familyYSecond a k φ < 0)) := by
  have hd := (family_regular_and_positive_curvature_numerator a k φ ha).2
  have hx : deriv (polarX (familyRadius a k)) φ = 0 →
      deriv (deriv (polarX (familyRadius a k))) φ ≠ 0 := by
    rw [(family_actual_derivatives a k φ).2.1.deriv,
      (family_actual_second_derivatives a k φ).1.deriv]
    intro h1 h2
    rw [h1, h2] at hd
    norm_num at hd
  have hy : deriv (polarY (familyRadius a k)) φ = 0 →
      deriv (deriv (polarY (familyRadius a k))) φ ≠ 0 := by
    rw [(family_actual_derivatives a k φ).2.2.deriv,
      (family_actual_second_derivatives a k φ).2.deriv]
    intro h1 h2
    rw [h1, h2] at hd
    norm_num at hd
  have hX := nondegenerate_extrema_iff (family_actual_derivatives a k φ).2.1.differentiableAt hx
  have hY := nondegenerate_extrema_iff (family_actual_derivatives a k φ).2.2.differentiableAt hy
  rw [(family_actual_derivatives a k φ).2.1.deriv,
    (family_actual_second_derivatives a k φ).1.deriv] at hX
  rw [(family_actual_derivatives a k φ).2.2.deriv,
    (family_actual_second_derivatives a k φ).2.deriv] at hY
  exact ⟨hX, hY⟩

theorem family_radius_extrema (a k φ : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) :
    (IsLocalMinimumOn (familyRadius a k) univ φ ↔
      familyRadiusFirst a k φ = 0 ∧ 0 < familyRadiusSecond a k φ) ∧
    (IsLocalMaximumOn (familyRadius a k) univ φ ↔
      familyRadiusFirst a k φ = 0 ∧ familyRadiusSecond a k φ < 0) := by
  have hne : deriv (familyRadius a k) φ = 0 → deriv (deriv (familyRadius a k)) φ ≠ 0 := by
    rw [(family_actual_derivatives a k φ).1.deriv, (family_radius_second_derivative a k φ).deriv]
    intro hf hs
    have hsin : Real.sin (k * φ) = 0 := by
      exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (neg_ne_zero.mpr ha) hk)
    have hcos : Real.cos (k * φ) = 0 := by
      exact (mul_eq_zero.mp hs).resolve_left (mul_ne_zero (neg_ne_zero.mpr ha) (pow_ne_zero 2 hk))
    have htrig := Real.sin_sq_add_cos_sq (k * φ)
    rw [hsin, hcos] at htrig
    norm_num at htrig
  have h := nondegenerate_extrema_iff (family_actual_derivatives a k φ).1.differentiableAt hne
  rwa [(family_actual_derivatives a k φ).1.deriv, (family_radius_second_derivative a k φ).deriv] at h

theorem family_norm_bound (a k φ : ℝ) : ‖familyPoint a k φ‖ ≤ |a| := by
  rw [familyPoint, norm_signedPolarPoint, familyRadius, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (k * φ)) (abs_nonneg a)


theorem family_no_norm_escape (a k : ℝ) (F : Filter ℝ) [NeBot F] :
    ¬ Tendsto (fun φ ↦ ‖familyPoint a k φ‖) F atTop := by
  intro h
  obtain ⟨φ, hφ⟩ := (tendsto_atTop.mp h (|a| + 1)).exists
  linarith [family_norm_bound a k φ]

theorem family_axis_symmetry (a k : ℝ) :
    ∀ z : ℂ, z ∈ polarCurveImage (familyRadius a k) ↔
      polarAxisReflection z ∈ polarCurveImage (familyRadius a k) := by
  apply source_polar_axis_symmetry
  intro r φ
  simp only [familyRadius, mul_neg, Real.cos_neg]

theorem family_zero_amplitude (k φ : ℝ) : familyPoint 0 k φ = 0 := by
  simp [familyPoint, familyRadius, signedPolarPoint_zero_radius]

theorem family_zero_amplitude_image (k : ℝ) :
    polarCurveImage (familyRadius 0 k) = {0} := by
  ext z
  rw [source_polar_explicit_membership, mem_singleton_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    simpa only [familyRadius, zero_mul, signedPolarPoint_zero_radius] using hφ.symm
  · rintro rfl
    exact ⟨0, by simp [familyRadius, signedPolarPoint_zero_radius]⟩


theorem family_zero_amplitude_no_tangents (k φ : ℝ) :
    ¬ HasHorizontalPolarTangent univ (familyRadius 0 k) φ ∧
      ¬ HasVerticalPolarTangent univ (familyRadius 0 k) φ := by
  constructor
  · intro h
    obtain ⟨t, ht, _⟩ := h.1 1 (by norm_num)
    simp [xSecantDomain, polarX, familyRadius] at ht
  · intro h
    obtain ⟨t, ht, _⟩ := h.1 1 (by norm_num)
    simp [ySecantDomain, polarY, familyRadius] at ht

theorem constant_source_extrema (c φ : ℝ) :
    IsLocalMinimumOn (fun _ : ℝ ↦ c) univ φ ∧
      IsLocalMaximumOn (fun _ : ℝ ↦ c) univ φ :=
  ⟨⟨mem_univ φ, 1, zero_lt_one, fun _ _ ↦ le_rfl⟩,
    ⟨mem_univ φ, 1, zero_lt_one, fun _ _ ↦ le_rfl⟩⟩

theorem family_constant_radius_extrema (a k φ : ℝ) (h : a = 0 ∨ k = 0) :
    IsLocalMinimumOn (familyRadius a k) univ φ ∧
      IsLocalMaximumOn (familyRadius a k) univ φ := by
  have he : familyRadius a k = (fun _ : ℝ ↦ familyRadius a k φ) := by
    funext t
    rcases h with ha | hk
    · simp [familyRadius, ha]
    · simp [familyRadius, hk]
  rw [he]
  exact constant_source_extrema _ φ

theorem family_zero_amplitude_coordinate_extrema (k φ : ℝ) :
    (IsLocalMinimumOn (polarX (familyRadius 0 k)) univ φ ∧
      IsLocalMaximumOn (polarX (familyRadius 0 k)) univ φ) ∧
    (IsLocalMinimumOn (polarY (familyRadius 0 k)) univ φ ∧
      IsLocalMaximumOn (polarY (familyRadius 0 k)) univ φ) := by
  have hx : polarX (familyRadius 0 k) = (fun _ : ℝ ↦ 0) := by
    funext t
    simp [polarX, familyRadius]
  have hy : polarY (familyRadius 0 k) = (fun _ : ℝ ↦ 0) := by
    funext t
    simp [polarY, familyRadius]
  rw [hx, hy]
  exact ⟨constant_source_extrema 0 φ, constant_source_extrema 0 φ⟩

theorem family_origin_iff (a k : ℝ) :
    (0 : ℂ) ∈ polarCurveImage (familyRadius a k) ↔ a = 0 ∨ k ≠ 0 := by
  rw [source_polar_explicit_membership]
  constructor
  · rintro ⟨φ, hφ⟩
    have hz := (signedPolarPoint_eq_zero_iff (familyRadius a k φ) φ).mp hφ
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      intro hk
      rw [familyRadius, hk, zero_mul, Real.cos_zero, mul_one] at hz
      exact ha hz
  · rintro (ha | hk)
    · subst a
      exact ⟨0, by simp [familyRadius, signedPolarPoint_zero_radius]⟩
    · refine ⟨(Real.pi / 2) / k, ?_⟩
      rw [familyRadius, mul_div_cancel₀ _ hk, Real.cos_pi_div_two, mul_zero,
        signedPolarPoint_zero_radius]

theorem family_radius_range (a k : ℝ) (hk : k ≠ 0) :
    range (familyRadius a k) = Icc (-|a|) |a| := by
  ext r
  constructor
  · rintro ⟨φ, rfl⟩
    apply abs_le.mp
    rw [familyRadius, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (k * φ)) (abs_nonneg a)
  · intro hr
    have hbound : |r| ≤ |a| := abs_le.mpr hr
    by_cases ha : a = 0
    · have hr0 : r = 0 := by simpa [ha] using hbound
      subst a
      subst r
      exact ⟨0, by simp [familyRadius]⟩
    · have hquot : |r / a| ≤ 1 := by
        rw [abs_div]
        exact (div_le_one (abs_pos.mpr ha)).mpr hbound
      have hq := abs_le.mp hquot
      refine ⟨Real.arccos (r / a) / k, ?_⟩
      rw [familyRadius, mul_div_cancel₀ _ hk, Real.cos_arccos hq.1 hq.2,
        mul_div_cancel₀ _ ha]

theorem family_norm_range (a k : ℝ) (hk : k ≠ 0) :
    range (fun φ ↦ ‖familyPoint a k φ‖) = Icc 0 |a| := by
  ext d
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨norm_nonneg _, family_norm_bound a k φ⟩
  · rintro ⟨hd, hda⟩
    have hr : d ∈ range (familyRadius a k) := by
      rw [family_radius_range a k hk]
      exact ⟨by linarith [abs_nonneg a], hda⟩
    obtain ⟨φ, hφ⟩ := hr
    refine ⟨φ, ?_⟩
    change ‖signedPolarPoint (familyRadius a k φ) φ‖ = d
    rw [norm_signedPolarPoint, hφ, abs_of_nonneg hd]


theorem fixed_radius_angle_winding (r φ ψ : ℝ) (hr : r ≠ 0) :
    signedPolarPoint r φ = signedPolarPoint r ψ ↔
      ∃ j : ℤ, φ = ψ + (j : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    have hc : Circle.exp φ = Circle.exp ψ := by
      apply Circle.ext
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr) h
    exact Circle.exp_eq_exp.mp hc
  · intro h
    have hc := Circle.exp_eq_exp.mpr h
    simp only [signedPolarPoint, hc]


theorem family_nonzero_image_iff (a k : ℝ) (z : ℂ) (hz : z ≠ 0) :
    z ∈ polarCurveImage (familyRadius a k) ↔
      (∃ j : ℤ, ‖z‖ = a * Real.cos (k *
        (nonnegativePolarAngle z + (j : ℝ) * (2 * Real.pi)))) ∨
      (∃ j : ℤ, -‖z‖ = a * Real.cos (k *
        (nonnegativePolarAngle z - Real.pi + (j : ℝ) * (2 * Real.pi)))) := by
  have hn : ‖z‖ ≠ 0 := (norm_pos_iff.mpr hz).ne'
  rw [source_polar_explicit_membership]
  constructor
  · rintro ⟨φ, hφ⟩
    have hnorm : |familyRadius a k φ| = ‖z‖ := by
      simpa only [norm_signedPolarPoint] using congrArg (fun w : ℂ ↦ ‖w‖) hφ
    by_cases hr : 0 ≤ familyRadius a k φ
    · have he : familyRadius a k φ = ‖z‖ := by rwa [abs_of_nonneg hr] at hnorm
      have hp : signedPolarPoint ‖z‖ φ = z := by simpa only [he] using hφ
      obtain ⟨j, hj⟩ := (fixed_radius_angle_winding ‖z‖ φ (nonnegativePolarAngle z) hn).mp
        (hp.trans (signedPolarPoint_norm_nonnegativePolarAngle z).symm)
      left
      exact ⟨j, by rw [← hj]; exact he.symm⟩
    · have he : familyRadius a k φ = -‖z‖ := by
        rw [abs_of_neg (lt_of_not_ge hr)] at hnorm
        linarith
      have hp : signedPolarPoint ‖z‖ (φ + Real.pi) = z := by
        rw [he, signedPolarPoint_neg_radius_eq_add_pi] at hφ
        exact hφ
      obtain ⟨j, hj⟩ := (fixed_radius_angle_winding ‖z‖ (φ + Real.pi) (nonnegativePolarAngle z) hn).mp
        (hp.trans (signedPolarPoint_norm_nonnegativePolarAngle z).symm)
      right
      have hangle : nonnegativePolarAngle z - Real.pi + (j : ℝ) * (2 * Real.pi) = φ := by linarith
      exact ⟨j, by rw [hangle]; exact he.symm⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · refine ⟨nonnegativePolarAngle z + (j : ℝ) * (2 * Real.pi), ?_⟩
      change signedPolarPoint (a * Real.cos (k * _)) _ = z
      rw [← hj]
      exact ((fixed_radius_angle_winding ‖z‖ _ (nonnegativePolarAngle z) hn).mpr ⟨j, rfl⟩).trans
        (signedPolarPoint_norm_nonnegativePolarAngle z)
    · refine ⟨nonnegativePolarAngle z - Real.pi + (j : ℝ) * (2 * Real.pi), ?_⟩
      change signedPolarPoint (a * Real.cos (k * _)) _ = z
      rw [← hj, signedPolarPoint_neg_radius_eq_add_pi]
      exact ((fixed_radius_angle_winding ‖z‖ _ (nonnegativePolarAngle z) hn).mpr
        ⟨j, by ring⟩).trans (signedPolarPoint_norm_nonnegativePolarAngle z)

theorem family_complete_image_iff (a k : ℝ) (z : ℂ) :
    z ∈ polarCurveImage (familyRadius a k) ↔
      (z = 0 ∧ (a = 0 ∨ k ≠ 0)) ∨
      (z ≠ 0 ∧ ((∃ j : ℤ, ‖z‖ = a * Real.cos (k *
         (nonnegativePolarAngle z + (j : ℝ) * (2 * Real.pi)))) ∨
       (∃ j : ℤ, -‖z‖ = a * Real.cos (k *
         (nonnegativePolarAngle z - Real.pi + (j : ℝ) * (2 * Real.pi)))))) := by
  by_cases hz : z = 0
  · subst z
    simp only [family_origin_iff, true_and, ne_eq, not_true_eq_false, false_and, or_false]
  · simp only [ne_eq, hz, not_false_eq_true, false_and, false_or, true_and]
    exact family_nonzero_image_iff a k z hz

theorem family_curve_image_norm_bound (a k : ℝ) (z : ℂ)
    (hz : z ∈ polarCurveImage (familyRadius a k)) : ‖z‖ ≤ |a| := by
  obtain ⟨φ, rfl⟩ := (source_polar_explicit_membership _ _).mp hz
  exact family_norm_bound a k φ


theorem family_zero_frequency_image (a : ℝ) (z : ℂ) :
    z ∈ polarCurveImage (familyRadius a 0) ↔ ‖z‖ = |a| := by
  rw [source_polar_explicit_membership]
  constructor
  · rintro ⟨φ, rfl⟩
    simp [familyRadius, norm_signedPolarPoint]
  · intro hz
    by_cases ha : 0 ≤ a
    · refine ⟨nonnegativePolarAngle z, ?_⟩
      have he : ‖z‖ = a := by rwa [abs_of_nonneg ha] at hz
      simpa only [familyRadius, zero_mul, Real.cos_zero, mul_one, he] using
        signedPolarPoint_norm_nonnegativePolarAngle z
    · refine ⟨nonnegativePolarAngle z + Real.pi, ?_⟩
      have he : a = -‖z‖ := by rw [abs_of_neg (lt_of_not_ge ha)] at hz; linarith
      simp only [familyRadius, zero_mul, Real.cos_zero, mul_one]
      rw [he, signedPolarPoint_neg_radius_eq_add_pi,
        show nonnegativePolarAngle z + Real.pi + Real.pi = nonnegativePolarAngle z + 2 * Real.pi by ring,
        signedPolarPoint_add_two_pi, signedPolarPoint_norm_nonnegativePolarAngle]


theorem family_periodic_iff (a k T : ℝ) (ha : a ≠ 0) :
    Function.Periodic (familyPoint a k) T ↔
      Real.sin T = 0 ∧ Real.sin (k * T) = 0 ∧
        Real.cos T * Real.cos (k * T) = 1 := by
  constructor
  · intro h
    have hx := congrArg Complex.re (h 0)
    simp only [zero_add, familyPoint, signedPolarPoint_re, familyRadius, mul_zero,
      Real.cos_zero, mul_one] at hx
    have hprod : Real.cos T * Real.cos (k * T) = 1 := by
      apply mul_left_cancel₀ ha
      nlinarith [hx]
    have ht := Real.sin_sq_add_cos_sq T
    have hkt := Real.sin_sq_add_cos_sq (k * T)
    have hC : Real.cos T ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.sin T)]
    have hD : Real.cos (k * T) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.sin (k * T))]
    have hdiff := sq_nonneg (Real.cos T - Real.cos (k * T))
    have hst : Real.sin T = 0 := sq_eq_zero_iff.mp (by nlinarith)
    have hsk : Real.sin (k * T) = 0 := sq_eq_zero_iff.mp (by nlinarith)
    exact ⟨hst, hsk, hprod⟩
  · rintro ⟨hT, hkT, hc⟩ φ
    apply Complex.ext
    · simp only [familyPoint, signedPolarPoint_re, familyRadius, mul_add, Real.cos_add,
        hT, hkT, mul_zero, sub_zero]
      calc
        _ = (a * Real.cos (k * φ) * Real.cos φ) *
          (Real.cos T * Real.cos (k * T)) := by ring
        _ = _ := by rw [hc, mul_one]
    · simp only [familyPoint, signedPolarPoint_im, familyRadius, mul_add, Real.cos_add,
        Real.sin_add, hT, hkT, mul_zero, sub_zero, add_zero]
      calc
        _ = (a * Real.cos (k * φ) * Real.sin φ) *
          (Real.cos T * Real.cos (k * T)) := by ring
        _ = _ := by rw [hc, mul_one]


theorem family_positive_period_iff_rational (a k : ℝ) (ha : a ≠ 0) :
    (∃ T : ℝ, 0 < T ∧ Function.Periodic (familyPoint a k) T) ↔
      ∃ p q : ℤ, 0 < q ∧ k = (p : ℝ) / (q : ℝ) := by
  constructor
  · rintro ⟨T, hT, hp⟩
    obtain ⟨hsT, hskT, _⟩ := (family_periodic_iff a k T ha).mp hp
    obtain ⟨q, hq⟩ := Real.sin_eq_zero_iff.mp hsT
    obtain ⟨p, hpp⟩ := Real.sin_eq_zero_iff.mp hskT
    have hqpos : 0 < (q : ℝ) := by nlinarith [Real.pi_pos]
    have hqint : (0 : ℤ) < q := by exact_mod_cast hqpos
    refine ⟨p, q, hqint, (eq_div_iff hqpos.ne').mpr ?_⟩
    apply mul_right_cancel₀ Real.pi_ne_zero
    calc
      k * (q : ℝ) * Real.pi = k * ((q : ℝ) * Real.pi) := by ring
      _ = k * T := by rw [hq]
      _ = (p : ℝ) * Real.pi := hpp.symm
  · rintro ⟨p, q, hq, hk⟩
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
    let T : ℝ := (q : ℝ) * (2 * Real.pi)
    have hT : 0 < T := mul_pos hqpos (by positivity)
    have hphase : k * T = (p : ℝ) * (2 * Real.pi) := by
      dsimp [T]
      calc
        _ = (k * (q : ℝ)) * (2 * Real.pi) := by ring
        _ = _ := by rw [hk, div_mul_cancel₀ _ hqpos.ne']
    have hs (j : ℤ) : Real.sin ((j : ℝ) * (2 * Real.pi)) = 0 := by
      rw [show (j : ℝ) * (2 * Real.pi) = ((2 * j : ℤ) : ℝ) * Real.pi by push_cast; ring,
        Real.sin_int_mul_pi]
    refine ⟨T, hT, (family_periodic_iff a k T ha).mpr ?_⟩
    exact ⟨hs q, by rw [hphase]; exact hs p,
      by rw [hphase]; simp only [T, Real.cos_int_mul_two_pi, one_mul]⟩

theorem family_point_continuous (a k : ℝ) : Continuous (familyPoint a k) := by
  have hr : Continuous (fun φ : ℝ ↦ ((a * Real.cos (k * φ) : ℝ) : ℂ)) := by
    fun_prop
  have hc : Continuous (fun φ : ℝ ↦ (Circle.exp φ : ℂ)) :=
    continuous_subtype_val.comp Circle.exp.continuous
  exact hr.mul hc

theorem family_zero_amplitude_periodic (k T : ℝ) :
    Function.Periodic (familyPoint 0 k) T := by
  intro φ
  rw [family_zero_amplitude, family_zero_amplitude]


theorem family_rational_image_compact (a k : ℝ)
    (hk : ∃ p q : ℤ, 0 < q ∧ k = (p : ℝ) / (q : ℝ)) :
    IsCompact (polarCurveImage (familyRadius a k)) := by
  by_cases ha : a = 0
  · subst a
    rw [family_zero_amplitude_image]
    exact isCompact_singleton
  · obtain ⟨T, hT, hp⟩ := (family_positive_period_iff_rational a k ha).mpr hk
    have he : polarCurveImage (familyRadius a k) = range (familyPoint a k) := by
      ext z
      rw [source_polar_explicit_membership]
      rfl
    rw [he]
    exact hp.compact_of_continuous hT.ne' (family_point_continuous a k)


theorem family_rational_image_closed (a k : ℝ)
    (hk : ∃ p q : ℤ, 0 < q ∧ k = (p : ℝ) / (q : ℝ)) :
    IsClosed (polarCurveImage (familyRadius a k)) :=
  (family_rational_image_compact a k hk).isClosed

end calculus.Chapter04.Section04CosineFamilyPolarCurveInvestigation
