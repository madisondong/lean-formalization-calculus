import calculus.Chapter04.Section04PolarEquations
import calculus.Chapter04.Section04PolarTangents
import calculus.Chapter04.Section04ConchoidPolarCurveInvestigation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 16(i): r=2/√(3cosφ)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2801. Xét `cos φ > 0`, với bán kính dương; phương trình Descartes giữ `x > 0` sau bình phương.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04RadicalPolarCurveInvestigation
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04ConchoidPolarCurveInvestigation

def radicalPolarDomain : Set ℝ := {t | 0 < Real.cos t}
def radicalPolarRadius (t : ℝ) : ℝ := 2/Real.sqrt (3*Real.cos t)
def radicalPolarPoint (t : ℝ) : ℂ := signedPolarPoint (radicalPolarRadius t) t
def radicalPolarCurve : Set ℂ := {z | ∃ t ∈ radicalPolarDomain, radicalPolarPoint t=z}
def radicalPolarX (t : ℝ) : ℝ := radicalPolarRadius t*Real.cos t
def radicalPolarY (t : ℝ) : ℝ := radicalPolarRadius t*Real.sin t
def radicalPolarDX (t : ℝ) : ℝ := -Real.sin t/Real.sqrt (3*Real.cos t)
def radicalPolarDY (t : ℝ) : ℝ := (1+(Real.cos t)^2)/(Real.cos t*Real.sqrt (3*Real.cos t))
def radicalPolarDDX (t : ℝ) : ℝ := -(1+(Real.cos t)^2)/(2*Real.cos t*Real.sqrt (3*Real.cos t))
def radicalPolarDDY (t : ℝ) : ℝ := Real.sin t*(3-(Real.cos t)^2)/(2*(Real.cos t)^2*Real.sqrt (3*Real.cos t))
def radicalPolarSignedCurvatureNumerator (t : ℝ) : ℝ := (3*(Real.cos t)^2-1)/(3*(Real.cos t)^3)

theorem radical_polar_domain_mem_nhds {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    radicalPolarDomain ∈ 𝓝 t := Real.continuous_cos.continuousAt.eventually (eventually_gt_nhds ht)

theorem radical_polar_radius_positive {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    0 < radicalPolarRadius t := div_pos (by norm_num) (Real.sqrt_pos_of_pos (mul_pos (by norm_num) ht))

theorem radical_polar_radius_square {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    (radicalPolarRadius t)^2=4/(3*Real.cos t) := by
  change 0 < Real.cos t at ht
  unfold radicalPolarRadius
  rw [div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3*Real.cos t)]
  norm_num


theorem radical_polar_complete_norm_image (z : ℂ) :
    z ∈ radicalPolarCurve ↔ 0 < z.re ∧ ‖z‖*z.re=4/3 := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    change 0 < Real.cos t at ht
    have hr := radical_polar_radius_positive ht
    rw [radicalPolarPoint,signedPolarPoint_re,norm_signedPolarPoint,abs_of_pos hr]
    refine ⟨mul_pos hr ht,?_⟩
    have hs := radical_polar_radius_square ht
    have hc : Real.cos t ≠ 0 := ht.ne'
    have hh : (radicalPolarRadius t)^2*(3*Real.cos t)=4 :=
      ((eq_div_iff (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hc)).mp hs)
    nlinarith [hh]
  · rintro ⟨hx,he⟩
    have hz : z ≠ 0 := by intro h; rw [h,Complex.zero_re] at hx; exact lt_irrefl _ hx
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let θ := nonnegativePolarAngle z
    have hc : ‖z‖*Real.cos θ=z.re := by
      simpa only [θ,signedPolarPoint_re] using congrArg Complex.re (signedPolarPoint_norm_nonnegativePolarAngle z)
    have ht : 0 < Real.cos θ := (mul_pos_iff_of_pos_left hn).mp (hc ▸ hx)
    have hs : (Real.sqrt (3*Real.cos θ))^2=3*Real.cos θ := Real.sq_sqrt (by positivity)
    have hp : 0 < Real.sqrt (3*Real.cos θ) := Real.sqrt_pos_of_pos (by positivity)
    have hprod : ‖z‖*Real.sqrt (3*Real.cos θ)=2 := by
      have heq : ‖z‖^2*(3*Real.cos θ)=4 := by
        nlinarith [he,congrArg (fun q : ℝ ↦ 3*‖z‖*q) hc]
      have hmul : (‖z‖*Real.sqrt (3*Real.cos θ))^2=4 := by
        rw [mul_pow,hs]
        exact heq
      nlinarith [hmul,mul_pos hn hp]
    have hr : radicalPolarRadius θ=‖z‖ := by
      unfold radicalPolarRadius
      apply (div_eq_iff hp.ne').mpr
      exact hprod.symm
    exact ⟨θ,ht,by rw [radicalPolarPoint,hr]; exact signedPolarPoint_norm_nonnegativePolarAngle z⟩


theorem radical_polar_complete_cartesian_image (z : ℂ) :
    z ∈ radicalPolarCurve ↔ 0 < z.re ∧ z.re^2*(z.re^2+z.im^2)=16/9 := by
  rw [radical_polar_complete_norm_image]
  constructor
  · rintro ⟨hx,he⟩
    refine ⟨hx,?_⟩
    have hnorm : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    nlinarith [congrArg (fun q : ℝ ↦ q^2) he,congrArg (fun q : ℝ ↦ z.re^2*q) hnorm]
  · rintro ⟨hx,he⟩
    refine ⟨hx,?_⟩
    have hnorm : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    nlinarith [he,congrArg (fun q : ℝ ↦ z.re^2*q) hnorm,mul_nonneg (norm_nonneg z) hx.le]

theorem radical_polar_sqrt_hasDerivAt {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    HasDerivAt (fun u : ℝ ↦ Real.sqrt (3*Real.cos u))
      (-3*Real.sin t/(2*Real.sqrt (3*Real.cos t))) t := by
  change 0 < Real.cos t at ht
  have h := (Real.hasDerivAt_sqrt (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) ht.ne')).comp t
    ((Real.hasDerivAt_cos t).const_mul 3)
  apply h.congr_deriv
  ring

theorem radical_polar_radius_hasDerivAt {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    HasDerivAt radicalPolarRadius
      (Real.sin t/(Real.cos t*Real.sqrt (3*Real.cos t))) t := by
  change 0 < Real.cos t at ht
  have hc := ht.ne'
  have hd : 0 < 3*Real.cos t := by positivity
  have hs := Real.sq_sqrt hd.le
  have hr := (Real.sqrt_pos_of_pos hd).ne'
  have h := (hasDerivAt_const t (2 : ℝ)).fun_div (radical_polar_sqrt_hasDerivAt ht) hr
  apply h.congr_deriv
  generalize Real.cos t = c at *
  generalize Real.sin t = s at *
  generalize Real.sqrt (3*c) = r at *
  field_simp [hc,hr]
  rw [hs]
  ring

theorem radical_polar_actual_first_derivatives {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    HasDerivAt radicalPolarX (radicalPolarDX t) t ∧
      HasDerivAt radicalPolarY (radicalPolarDY t) t := by
  change 0 < Real.cos t at ht
  have hr := radical_polar_radius_hasDerivAt ht
  have hs := Real.sin_sq_add_cos_sq t
  have hd := (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 3*Real.cos t)).ne'
  constructor
  · have h := hr.fun_mul (Real.hasDerivAt_cos t)
    apply h.congr_deriv
    unfold radicalPolarRadius radicalPolarDX
    field_simp [ht.ne',hd]
    ring
  · have h := hr.fun_mul (Real.hasDerivAt_sin t)
    apply h.congr_deriv
    unfold radicalPolarRadius radicalPolarDY
    field_simp [ht.ne',hd]
    nlinarith [hs]

theorem radical_polar_first_derivative_values {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    deriv radicalPolarX t=radicalPolarDX t ∧ deriv radicalPolarY t=radicalPolarDY t :=
  ⟨(radical_polar_actual_first_derivatives ht).1.deriv,(radical_polar_actual_first_derivatives ht).2.deriv⟩

theorem radical_polar_actual_second_derivatives {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    HasDerivAt (deriv radicalPolarX) (radicalPolarDDX t) t ∧
      HasDerivAt (deriv radicalPolarY) (radicalPolarDDY t) t := by
  change 0 < Real.cos t at ht
  have hc := ht.ne'
  have hd : 0 < 3*Real.cos t := by positivity
  have hs := Real.sq_sqrt hd.le
  have hr := (Real.sqrt_pos_of_pos hd).ne'
  have hD := radical_polar_domain_mem_nhds ht
  constructor
  · have h := ((Real.hasDerivAt_sin t).neg).fun_div (radical_polar_sqrt_hasDerivAt ht) hr
    have h' : HasDerivAt radicalPolarDX (radicalPolarDDX t) t := by
      apply h.congr_deriv
      unfold radicalPolarDDX
      have htrig := Real.sin_sq_add_cos_sq t
      simp only [Pi.neg_apply]
      generalize Real.cos t = c at *
      generalize Real.sin t = s at *
      generalize Real.sqrt (3*c) = r at *
      field_simp [hc,hr]
      rw [hs]
      nlinarith [congrArg (fun q : ℝ ↦ 3*c*q) htrig]
    apply h'.congr_of_eventuallyEq
    filter_upwards [hD] with u hu
    exact (radical_polar_first_derivative_values hu).1
  · have h := (((Real.hasDerivAt_cos t).fun_pow 2).const_add 1).fun_div
      ((Real.hasDerivAt_cos t).fun_mul (radical_polar_sqrt_hasDerivAt ht)) (mul_ne_zero hc hr)
    have h' : HasDerivAt radicalPolarDY (radicalPolarDDY t) t := by
      apply h.congr_deriv
      unfold radicalPolarDDY
      generalize Real.cos t = c at *
      generalize Real.sin t = s at *
      generalize Real.sqrt (3*c) = r at *
      norm_num
      field_simp [hc,hr]
      rw [hs]
      ring
    apply h'.congr_of_eventuallyEq
    filter_upwards [hD] with u hu
    exact (radical_polar_first_derivative_values hu).2


theorem radical_polar_vertical_velocity_positive {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    0 < deriv radicalPolarY t := by
  change 0 < Real.cos t at ht
  rw [(radical_polar_first_derivative_values ht).2]
  exact div_pos (by nlinarith [sq_nonneg (Real.cos t)])
    (mul_pos ht (Real.sqrt_pos_of_pos (by positivity)))

theorem radical_polar_curvature_numerator {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    deriv radicalPolarX t*deriv (deriv radicalPolarY) t-
      deriv (deriv radicalPolarX) t*deriv radicalPolarY t=radicalPolarSignedCurvatureNumerator t := by
  change 0 < Real.cos t at ht
  rw [(radical_polar_first_derivative_values ht).1,(radical_polar_first_derivative_values ht).2,
    (radical_polar_actual_second_derivatives ht).1.deriv,(radical_polar_actual_second_derivatives ht).2.deriv]
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3*Real.cos t)
  have hc := ht.ne'
  have hr := (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 3*Real.cos t)).ne'
  unfold radicalPolarDX radicalPolarDY radicalPolarDDX radicalPolarDDY radicalPolarSignedCurvatureNumerator
  field_simp [hc,hr]
  nlinarith [congrArg (fun q : ℝ ↦ (Real.cos t)^2*q) hs,
    congrArg (fun q : ℝ ↦ q*((Real.cos t)^2)^2) (Real.sin_sq_add_cos_sq t),Real.sin_sq_add_cos_sq t]

theorem radical_polar_signed_curvature_numerator_signs {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    (0 < radicalPolarSignedCurvatureNumerator t ↔ 1/3 < (Real.cos t)^2) ∧
      (radicalPolarSignedCurvatureNumerator t < 0 ↔ (Real.cos t)^2 < 1/3) ∧
      (radicalPolarSignedCurvatureNumerator t=0 ↔ (Real.cos t)^2=1/3) := by
  change 0 < Real.cos t at ht
  have hd : 0 < 3*(Real.cos t)^3 := by positivity
  unfold radicalPolarSignedCurvatureNumerator
  refine ⟨?_,?_,?_⟩
  · rw [div_pos_iff_of_pos_right hd]; constructor <;> intro h <;> linarith
  · rw [div_lt_iff₀ hd]; constructor <;> intro h <;> linarith
  · rw [div_eq_zero_iff,or_iff_left hd.ne']; constructor <;> intro h <;> linarith

theorem radical_polar_signed_curvature_numerator_hasDerivAt {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    HasDerivAt radicalPolarSignedCurvatureNumerator
      (Real.sin t*((Real.cos t)^2-1)/(Real.cos t)^4) t := by
  change 0 < Real.cos t at ht
  have h := ((((Real.hasDerivAt_cos t).fun_pow 2).const_mul 3).sub_const 1).fun_div
    (((Real.hasDerivAt_cos t).fun_pow 3).const_mul 3) (by positivity : 3*(Real.cos t)^3 ≠ 0)
  apply h.congr_deriv
  norm_num at *
  field_simp [ht.ne']
  ring

theorem radical_polar_signed_curvature_numerator_zeros_simple {t : ℝ} (ht : t ∈ radicalPolarDomain)
    (hz : radicalPolarSignedCurvatureNumerator t=0) :
    Real.sin t*((Real.cos t)^2-1)/(Real.cos t)^4 ≠ 0 := by
  change 0 < Real.cos t at ht
  have hc := (radical_polar_signed_curvature_numerator_signs ht).2.2.mp hz
  have hs : Real.sin t ≠ 0 := by intro hs; nlinarith [Real.sin_sq_add_cos_sq t]
  exact div_ne_zero (mul_ne_zero hs (by intro h; linarith)) (pow_ne_zero 4 ht.ne')

theorem radical_polar_inflection_sign_change {t : ℝ} (ht : t ∈ radicalPolarDomain)
    (hz : radicalPolarSignedCurvatureNumerator t=0) :
    ((∀ᶠ s : ℝ in 𝓝[<] t, radicalPolarSignedCurvatureNumerator s < 0) ∧
      (∀ᶠ s : ℝ in 𝓝[>] t, 0 < radicalPolarSignedCurvatureNumerator s)) ∨
    ((∀ᶠ s : ℝ in 𝓝[<] t, 0 < radicalPolarSignedCurvatureNumerator s) ∧
      (∀ᶠ s : ℝ in 𝓝[>] t, radicalPolarSignedCurvatureNumerator s < 0)) := by
  change 0 < Real.cos t at ht
  have hd := radical_polar_signed_curvature_numerator_zeros_simple ht hz
  have hc := differentiable_simple_zero_sign_change (radical_polar_signed_curvature_numerator_hasDerivAt ht) hz
  rcases lt_or_gt_of_ne hd with h | h
  · exact Or.inr (hc.2 h)
  · exact Or.inl (hc.1 h)

theorem radical_polar_x_sqrt {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    radicalPolarX t=(2/3)*Real.sqrt (3*Real.cos t) := by
  change 0 < Real.cos t at ht
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3*Real.cos t)
  have hn := (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 3*Real.cos t)).ne'
  unfold radicalPolarX radicalPolarRadius
  field_simp [hn]
  nlinarith [hs]

theorem radical_polar_coordinate_bounds {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    0 < radicalPolarX t ∧ radicalPolarX t ≤ 2/Real.sqrt 3 := by
  change 0 < Real.cos t at ht
  refine ⟨mul_pos (radical_polar_radius_positive ht) ht,?_⟩
  have h0 : (0 : ℝ) ∈ radicalPolarDomain := by simp [radicalPolarDomain]
  have h : radicalPolarX t ≤ radicalPolarX 0 := by
    rw [radical_polar_x_sqrt ht,radical_polar_x_sqrt h0,Real.cos_zero,mul_one]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (show 3*Real.cos t ≤ 3 by nlinarith [Real.cos_le_one t])) (by norm_num : (0 : ℝ) ≤ 2/3)
  simpa [radicalPolarX,radicalPolarRadius] using h

theorem radical_polar_reflection_period (t : ℝ) :
    radicalPolarX (-t)=radicalPolarX t ∧ radicalPolarY (-t)= -radicalPolarY t ∧
      radicalPolarPoint (t+2*Real.pi)=radicalPolarPoint t ∧
      (t+2*Real.pi ∈ radicalPolarDomain ↔ t ∈ radicalPolarDomain) := by
  refine ⟨by simp [radicalPolarX,radicalPolarRadius],by simp [radicalPolarY,radicalPolarRadius],?_,?_⟩
  · apply Complex.ext <;> simp [radicalPolarPoint,radicalPolarRadius,signedPolarPoint_re,
      signedPolarPoint_im,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · simp [radicalPolarDomain,Real.cos_add_two_pi]

theorem radical_polar_complete_tangents {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    (HasVerticalPolarTangent radicalPolarDomain radicalPolarRadius t ↔ Real.sin t=0) ∧
      (radicalPolarDX t ≠ 0 → ¬ HasHorizontalPolarTangent radicalPolarDomain radicalPolarRadius t) := by
  change 0 < Real.cos t at ht
  have hr := radical_polar_radius_hasDerivAt ht
  have hX := (polarX_hasDerivAt hr).unique (radical_polar_actual_first_derivatives ht).1
  have hY := (polarY_hasDerivAt hr).unique (radical_polar_actual_first_derivatives ht).2
  have hy : radicalPolarDY t ≠ 0 := by
    rw [← (radical_polar_first_derivative_values ht).2]
    exact (radical_polar_vertical_velocity_positive ht).ne'
  have hvel : Real.sin t/(Real.cos t*Real.sqrt (3*Real.cos t))*Real.sin t+
      radicalPolarRadius t*Real.cos t ≠ 0 := by rw [hY]; exact hy
  constructor
  · rw [vertical_polar_tangent_iff (radical_polar_domain_mem_nhds ht) hr hvel,hX]
    have hn := (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 3*Real.cos t)).ne'
    change -Real.sin t/Real.sqrt (3*Real.cos t)=0 ↔ Real.sin t=0
    rw [div_eq_zero_iff,or_iff_left hn,neg_eq_zero]
  · intro hx
    have hx' : Real.sin t/(Real.cos t*Real.sqrt (3*Real.cos t))*Real.cos t-
        radicalPolarRadius t*Real.sin t ≠ 0 := by rw [hX]; exact hx
    rw [horizontal_polar_tangent_iff (radical_polar_domain_mem_nhds ht) hr hx',hY]
    exact hy

theorem radical_polar_central_strict_variation :
    StrictMonoOn radicalPolarY (Ioo (-(Real.pi/2)) (Real.pi/2)) ∧
      StrictMonoOn radicalPolarX (Ioc (-(Real.pi/2)) 0) ∧
      StrictAntiOn radicalPolarX (Ico 0 (Real.pi/2)) := by
  have hD : ∀ t ∈ Ioo (-(Real.pi/2)) (Real.pi/2), t ∈ radicalPolarDomain :=
    fun _ ht ↦ Real.cos_pos_of_mem_Ioo ht
  have hc : ContinuousOn radicalPolarX (Ioo (-(Real.pi/2)) (Real.pi/2)) :=
    fun _ ht ↦ (radical_polar_actual_first_derivatives (hD _ ht)).1.continuousAt.continuousWithinAt
  have hcY : ContinuousOn radicalPolarY (Ioo (-(Real.pi/2)) (Real.pi/2)) :=
    fun _ ht ↦ (radical_polar_actual_first_derivatives (hD _ ht)).2.continuousAt.continuousWithinAt
  refine ⟨strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcY (fun t ht ↦
    radical_polar_vertical_velocity_positive (hD t (interior_subset ht))),?_,?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
      (hc.mono (by intro t ht; exact ⟨ht.1,lt_of_le_of_lt ht.2 Real.pi_div_two_pos⟩))
    intro t ht
    rw [interior_Ioc] at ht
    have hdt := hD t ⟨ht.1,lt_trans ht.2 Real.pi_div_two_pos⟩
    have hcp : 0 < Real.cos t := hdt
    rw [(radical_polar_first_derivative_values hdt).1]
    exact div_pos (neg_pos.mpr (Real.sin_neg_of_neg_of_neg_pi_lt ht.2 (by linarith [ht.1,Real.pi_pos])))
      (Real.sqrt_pos_of_pos (by positivity))
  · apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
      (hc.mono (by intro t ht; exact ⟨lt_of_lt_of_le (neg_neg_of_pos Real.pi_div_two_pos) ht.1,ht.2⟩))
    intro t ht
    rw [interior_Ico] at ht
    have hdt := hD t ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
    have hcp : 0 < Real.cos t := hdt
    rw [(radical_polar_first_derivative_values hdt).1]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2,Real.pi_pos]))) (Real.sqrt_pos_of_pos (by positivity))


theorem radical_polar_every_height_unique (y : ℝ) :
    ∃! x : ℝ, (⟨x,y⟩ : ℂ) ∈ radicalPolarCurve := by
  let f : ℝ → ℝ := fun x ↦ x^2*(x^2+y^2)
  have hc : ContinuousOn f (Icc 0 2) := by unfold f; fun_prop
  have hh : (16/9 : ℝ) ∈ Icc (f 0) (f 2) := by
    constructor <;> dsimp [f] <;> nlinarith [sq_nonneg y]
  rcases intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hc hh with ⟨x,hx,he⟩
  have hxpos : 0 < x := by
    by_contra h; have hz : x=0 := le_antisymm (le_of_not_gt h) hx.1
    subst x; norm_num [f] at he
  refine ⟨x,(radical_polar_complete_cartesian_image _).mpr ⟨hxpos,he⟩,?_⟩
  intro s hs
  rcases (radical_polar_complete_cartesian_image _).mp hs with ⟨hspos,hse⟩
  have hmono : StrictMonoOn f (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi (𝕜 := ℝ) 0)
    · unfold f; fun_prop
    · intro u hu
      have hp : 0 < u := interior_subset hu
      have hd : HasDerivAt f (2*u*(2*u^2+y^2)) u := by
        have h := ((hasDerivAt_id u).fun_pow 2).fun_mul
          (((hasDerivAt_id u).fun_pow 2).add_const (y^2))
        exact h.congr_deriv (by simp only [id_eq]; ring)
      rw [hd.deriv]
      exact mul_pos (mul_pos (by norm_num) hp) (by nlinarith [sq_pos_of_pos hp,sq_nonneg y])
  exact hmono.injOn hspos hxpos (hse.trans he.symm)

theorem radical_polar_critical_cartesian_points {t : ℝ} (ht : t ∈ radicalPolarDomain)
    (hz : radicalPolarSignedCurvatureNumerator t=0) :
    (radicalPolarX t)^2=4*Real.sqrt 3/9 ∧
      (radicalPolarY t)^2=8*Real.sqrt 3/9 := by
  change 0 < Real.cos t at ht
  have hc := (radical_polar_signed_curvature_numerator_signs ht).2.2.mp hz
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hr3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hcos : Real.cos t=Real.sqrt 3/3 := by
    apply (sq_eq_sq₀ ht.le (div_pos hr3 (by norm_num)).le).mp
    rw [div_pow,h3]
    nlinarith [hc]
  have hr := radical_polar_radius_square ht
  have hs := Real.sin_sq_add_cos_sq t
  unfold radicalPolarX radicalPolarY
  rw [mul_pow,mul_pow,hr]
  constructor <;> field_simp [ht.ne'] <;>
    nlinarith [congrArg (fun q : ℝ ↦ Real.sqrt 3*q) hc,congrArg (fun q : ℝ ↦ Real.sqrt 3*q) hs,h3]

theorem radical_polar_pole_limits {l : Filter ℝ} {q : ℝ}
    (hq : Tendsto (fun t : ℝ ↦ t) l (𝓝 q)) (hc : Real.cos q=0)
    (hD : ∀ᶠ t : ℝ in l, t ∈ radicalPolarDomain) :
    Tendsto radicalPolarX l (𝓝 0) ∧ Tendsto radicalPolarRadius l atTop := by
  have hcos := Real.continuous_cos.continuousAt.tendsto.comp hq
  have hs : Tendsto (fun t : ℝ ↦ Real.sqrt (3*Real.cos t)) l (𝓝 0) := by
    simpa only [Function.comp_def,hc,mul_zero,Real.sqrt_zero] using (hcos.const_mul 3).sqrt
  have hp : ∀ᶠ t : ℝ in l, 0 < Real.sqrt (3*Real.cos t) :=
    hD.mono (fun t ht ↦ Real.sqrt_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3) (show 0 < Real.cos t from ht)))
  have hi := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs hp)
  constructor
  · have hx : Tendsto (fun t : ℝ ↦ (2/3)*Real.sqrt (3*Real.cos t)) l (𝓝 0) := by
      simpa only [mul_zero] using hs.const_mul (2/3)
    apply hx.congr'
    exact hD.mono (fun _ ht ↦ (radical_polar_x_sqrt ht).symm)
  · simpa only [radicalPolarRadius,Function.comp_def,div_eq_mul_inv] using! hi.const_mul_atTop (by norm_num : (0 : ℝ) < 2)

theorem radical_polar_actual_two_end_limits :
    Tendsto radicalPolarX (𝓝[<] (Real.pi/2)) (𝓝 0) ∧
      Tendsto radicalPolarY (𝓝[<] (Real.pi/2)) atTop ∧
      Tendsto radicalPolarX (𝓝[>] (-(Real.pi/2))) (𝓝 0) ∧
      Tendsto radicalPolarY (𝓝[>] (-(Real.pi/2))) atBot := by
  have hL : ∀ᶠ t : ℝ in 𝓝[<] (Real.pi/2), t ∈ radicalPolarDomain := by
    filter_upwards [self_mem_nhdsWithin,Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by linarith [Real.pi_pos] : -(Real.pi/2) < Real.pi/2))] with t ht hb
    exact Real.cos_pos_of_mem_Ioo ⟨hb,ht⟩
  have hR : ∀ᶠ t : ℝ in 𝓝[>] (-(Real.pi/2)), t ∈ radicalPolarDomain := by
    filter_upwards [self_mem_nhdsWithin,Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by linarith [Real.pi_pos] : -(Real.pi/2) < Real.pi/2))] with t ht hb
    exact Real.cos_pos_of_mem_Ioo ⟨ht,hb⟩
  have hl := radical_polar_pole_limits (tendsto_id.mono_left nhdsWithin_le_nhds) Real.cos_pi_div_two hL
  have hr := radical_polar_pole_limits (tendsto_id.mono_left nhdsWithin_le_nhds)
    (by rw [Real.cos_neg,Real.cos_pi_div_two]) hR
  have hsL : Tendsto Real.sin (𝓝[<] (Real.pi/2)) (𝓝 1) := by
    simpa only [Real.sin_pi_div_two] using (Real.continuous_sin.continuousAt (x := Real.pi/2)).tendsto.mono_left nhdsWithin_le_nhds
  have hsR : Tendsto Real.sin (𝓝[>] (-(Real.pi/2))) (𝓝 (-1)) := by
    simpa only [Real.sin_neg,Real.sin_pi_div_two] using (Real.continuous_sin.continuousAt (x := -(Real.pi/2))).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨hl.1,hl.2.atTop_mul_pos (by norm_num) hsL,hr.1,hr.2.atTop_mul_neg (by norm_num) hsR⟩

theorem radical_polar_unique_affine_asymptote (u v w : ℝ) :
    Tendsto (fun t : ℝ ↦ u*radicalPolarX t+v*radicalPolarY t+w)
      (𝓝[<] (Real.pi/2)) (𝓝 0) ↔ v=0 ∧ w=0 := by
  have hx := radical_polar_actual_two_end_limits.1
  have hy := radical_polar_actual_two_end_limits.2.1
  have hi := hy.inv_tendsto_atTop
  have hn : ∀ᶠ t : ℝ in 𝓝[<] (Real.pi/2), radicalPolarY t ≠ 0 :=
    (hy.eventually (eventually_gt_atTop (0 : ℝ))).mono (fun _ ht ↦ ht.ne')
  constructor
  · intro h
    have hh : Tendsto (fun t : ℝ ↦
        (u*radicalPolarX t+v*radicalPolarY t+w)*(radicalPolarY t)⁻¹-
        (u*radicalPolarX t+w)*(radicalPolarY t)⁻¹) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
      simpa only [mul_zero,sub_zero] using! (h.mul hi).sub (((hx.const_mul u).add_const w).mul hi)
    have hv : v=0 := by
      have hc : Tendsto (fun _ : ℝ ↦ v) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
        apply hh.congr'
        filter_upwards [hn] with t ht
        field_simp [ht]
        ring
      exact tendsto_nhds_unique tendsto_const_nhds hc
    have hw : Tendsto (fun t : ℝ ↦ u*radicalPolarX t+v*radicalPolarY t+w)
        (𝓝[<] (Real.pi/2)) (𝓝 w) := by
      simpa only [hv,zero_mul,add_zero,mul_zero,zero_add] using! (hx.const_mul u).add_const w
    exact ⟨hv,tendsto_nhds_unique hw h⟩
  · rintro ⟨rfl,rfl⟩
    simpa only [zero_mul,add_zero,mul_zero] using hx.const_mul u

theorem radical_polar_vertex_and_axis {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    (radicalPolarPoint t).re > 0 ∧
      ((radicalPolarPoint t).im=0 ↔ Real.sin t=0) ∧
      (Real.sin t=0 → radicalPolarPoint t=⟨2/Real.sqrt 3,0⟩) ∧
      HasVerticalPolarTangent radicalPolarDomain radicalPolarRadius 0 := by
  change 0 < Real.cos t at ht
  have hr := radical_polar_radius_positive ht
  have h0 : (0 : ℝ) ∈ radicalPolarDomain := by simp [radicalPolarDomain]
  refine ⟨?_,?_,?_,(radical_polar_complete_tangents h0).1.mpr (by simp)⟩
  · simpa only [radicalPolarPoint,signedPolarPoint_re] using mul_pos hr ht
  · simp only [radicalPolarPoint,signedPolarPoint_im,mul_eq_zero,hr.ne',false_or]
  · intro hs
    have hc : Real.cos t=1 := by
      apply (sq_eq_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 1)).mp
      nlinarith [Real.sin_sq_add_cos_sq t]
    apply Complex.ext <;> simp [radicalPolarPoint,radicalPolarRadius,signedPolarPoint_re,
      signedPolarPoint_im,hc,hs]

theorem source_radical_polar_curve_investigation :
    (∀ z : ℂ, z ∈ radicalPolarCurve ↔ 0 < z.re ∧ z.re^2*(z.re^2+z.im^2)=16/9) ∧
      (∀ y : ℝ, ∃! x : ℝ, (⟨x,y⟩ : ℂ) ∈ radicalPolarCurve) ∧
      (∀ t ∈ radicalPolarDomain, HasDerivAt radicalPolarX (radicalPolarDX t) t ∧
        HasDerivAt radicalPolarY (radicalPolarDY t) t) ∧
      (∀ t ∈ radicalPolarDomain, 0 < deriv radicalPolarY t) ∧
      (∀ t ∈ radicalPolarDomain, radicalPolarSignedCurvatureNumerator t=0 ↔ (Real.cos t)^2=1/3) ∧
      (∀ u v w : ℝ, Tendsto (fun t : ℝ ↦ u*radicalPolarX t+v*radicalPolarY t+w)
        (𝓝[<] (Real.pi/2)) (𝓝 0) ↔ v=0 ∧ w=0) := by
  exact ⟨radical_polar_complete_cartesian_image,radical_polar_every_height_unique,
    fun _ ht ↦ radical_polar_actual_first_derivatives ht,
    fun _ ht ↦ radical_polar_vertical_velocity_positive ht,
    fun _ ht ↦ (radical_polar_signed_curvature_numerator_signs ht).2.2,radical_polar_unique_affine_asymptote⟩


theorem radical_polar_horizontal_implies_vertical_velocity_zero {t : ℝ}
    (ht : t ∈ radicalPolarDomain)
    (hH : HasHorizontalPolarTangent radicalPolarDomain radicalPolarRadius t) :
    radicalPolarDY t = 0 := by
  change 0 < Real.cos t at ht
  let F : Filter ℝ := 𝓝[(xSecantDomain radicalPolarDomain radicalPolarRadius t) \ {t}] t
  let : NeBot F := calculus.Chapter03.Section02.accumulationPointOf_iff_neBot.mp hH.1
  have hle : F ≤ 𝓝[≠] t := nhdsWithin_mono t (by
    intro s hs
    exact hs.2)
  have hX : HasDerivAt (polarX radicalPolarRadius) (radicalPolarDX t) t :=
    (radical_polar_actual_first_derivatives ht).1
  have hY : HasDerivAt (polarY radicalPolarRadius) (radicalPolarDY t) t :=
    (radical_polar_actual_first_derivatives ht).2
  have hxs : Tendsto (fun s ↦ (polarX radicalPolarRadius s - polarX radicalPolarRadius t) / (s - t))
      F (𝓝 (radicalPolarDX t)) := by
    simpa only [slope_fun_def_field] using hX.tendsto_slope.mono_left hle
  have hys : Tendsto (fun s ↦ (polarY radicalPolarRadius s - polarY radicalPolarRadius t) / (s - t))
      F (𝓝 (radicalPolarDY t)) := by
    simpa only [slope_fun_def_field] using hY.tendsto_slope.mono_left hle
  have hratio : Tendsto (fun s ↦
      (polarY radicalPolarRadius s - polarY radicalPolarRadius t) /
        (polarX radicalPolarRadius s - polarX radicalPolarRadius t)) F (𝓝 0) :=
    (calculus.Chapter03.Section02.domainLimit_iff_tendsto hH.1).mp hH
  have hzero : Tendsto (fun s ↦
      (polarY radicalPolarRadius s - polarY radicalPolarRadius t) / (s - t)) F (𝓝 0) := by
    have hm := hratio.mul hxs
    simp only [zero_mul] at hm
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hden : polarX radicalPolarRadius s - polarX radicalPolarRadius t ≠ 0 := hs.1.2
    have hst : s - t ≠ 0 := sub_ne_zero.mpr (by
      simpa only [mem_singleton_iff] using hs.2)
    field_simp [hden, hst]
  exact tendsto_nhds_unique hys hzero


theorem radical_polar_no_horizontal_tangent {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    ¬ HasHorizontalPolarTangent radicalPolarDomain radicalPolarRadius t := by
  change 0 < Real.cos t at ht
  intro hH
  have hy := radical_polar_horizontal_implies_vertical_velocity_zero ht hH
  have hp := radical_polar_vertical_velocity_positive ht
  rw [(radical_polar_first_derivative_values ht).2, hy] at hp
  exact lt_irrefl 0 hp


theorem radical_polar_complete_tangents_unconditional {t : ℝ} (ht : t ∈ radicalPolarDomain) :
    (HasVerticalPolarTangent radicalPolarDomain radicalPolarRadius t ↔ Real.sin t = 0) ∧
      ¬ HasHorizontalPolarTangent radicalPolarDomain radicalPolarRadius t :=
  ⟨(radical_polar_complete_tangents ht).1, radical_polar_no_horizontal_tangent ht⟩

end calculus.Chapter04.Section04RadicalPolarCurveInvestigation
