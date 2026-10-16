import calculus.Chapter04.Section04PolarEquations
import calculus.Chapter04.Section04PolarTangents
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 16(g): conchoid r=a+b secφ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2799. Xét `cos φ ≠ 0`, kể cả khi `b = 0`; bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04ConchoidPolarCurveInvestigation
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarTangents

def conchoidDomain : Set ℝ := {t | Real.cos t ≠ 0}
def conchoidRadius (a b t : ℝ) : ℝ := a+b/Real.cos t
def conchoidPoint (a b t : ℝ) : ℂ := signedPolarPoint (conchoidRadius a b t) t
def conchoidCurve (a b : ℝ) : Set ℂ :=
  {z | ∃ t ∈ conchoidDomain, conchoidPoint a b t=z}
def conchoidX (a b t : ℝ) : ℝ := a*Real.cos t+b
def conchoidY (a b t : ℝ) : ℝ := a*Real.sin t+b*Real.tan t
def conchoidDX (a t : ℝ) : ℝ := -a*Real.sin t
def conchoidDY (a b t : ℝ) : ℝ := a*Real.cos t+b/(Real.cos t)^2
def conchoidDDX (a t : ℝ) : ℝ := -a*Real.cos t
def conchoidDDY (a b t : ℝ) : ℝ := -a*Real.sin t+2*b*Real.sin t/(Real.cos t)^3
def conchoidDDDX (a t : ℝ) : ℝ := a*Real.sin t
def conchoidDDDY (a b t : ℝ) : ℝ :=
  -a*Real.cos t+2*b/(Real.cos t)^2+6*b*(Real.sin t)^2/(Real.cos t)^4
def conchoidSignedCurvatureNumerator (a b t : ℝ) : ℝ :=
  a^2+a*b*((3*(Real.cos t)^2-2)/(Real.cos t)^3)

theorem conchoid_actual_coordinates {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    (conchoidPoint a b t).re=conchoidX a b t ∧
      (conchoidPoint a b t).im=conchoidY a b t := by
  change Real.cos t ≠ 0 at ht
  simp only [conchoidPoint,signedPolarPoint_re,signedPolarPoint_im]
  unfold conchoidRadius conchoidX conchoidY
  rw [Real.tan_eq_sin_div_cos]
  constructor <;> field_simp [ht]

theorem conchoid_complete_coordinate_image (a b : ℝ) (z : ℂ) :
    z ∈ conchoidCurve a b ↔ ∃ t : ℝ, Real.cos t ≠ 0 ∧
      z.re=a*Real.cos t+b ∧ z.im=a*Real.sin t+b*Real.tan t := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨t,ht,(conchoid_actual_coordinates ht).1,(conchoid_actual_coordinates ht).2⟩
  · rintro ⟨t,ht,hx,hy⟩
    exact ⟨t,ht,Complex.ext ((conchoid_actual_coordinates ht).1.trans hx.symm)
      ((conchoid_actual_coordinates ht).2.trans hy.symm)⟩


theorem conchoid_complete_nonzero_cartesian_image (a b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    z ∈ conchoidCurve a b ↔ z.re ≠ 0 ∧
      (z.re-b)^2*(z.re^2+z.im^2)=a^2*z.re^2 := by
  constructor
  · rintro ⟨t,ht,hp⟩
    change Real.cos t ≠ 0 at ht
    have hr : conchoidRadius a b t ≠ 0 := by
      intro h; apply hz; rw [← hp,conchoidPoint,h,signedPolarPoint_zero_radius]
    have hx := (conchoid_actual_coordinates (a := a) (b := b) ht).1
    have hs := signed_polar_square_sum (conchoidRadius a b t) t
    have hX : (conchoidPoint a b t).re=conchoidRadius a b t*Real.cos t :=
      signedPolarPoint_re _ _
    change (conchoidPoint a b t).re^2+(conchoidPoint a b t).im^2=(conchoidRadius a b t)^2 at hs
    rw [hp] at hx hs hX
    refine ⟨by rw [hX]; exact mul_ne_zero hr ht,?_⟩
    have hxb : z.re-b=a*Real.cos t := by unfold conchoidX at hx; linarith
    rw [hxb,hs,hX]
    ring
  · rintro ⟨hx,he⟩
    let θ := nonnegativePolarAngle z
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hc : ‖z‖*Real.cos θ=z.re := by
      simpa only [θ,signedPolarPoint_re] using congrArg Complex.re (signedPolarPoint_norm_nonnegativePolarAngle z)
    have hcn : Real.cos θ ≠ 0 := by intro h; rw [h,mul_zero] at hc; exact hx hc.symm
    have hnorm : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    have hsq : ((z.re-b)*‖z‖)^2=(a*z.re)^2 := by rw [mul_pow,hnorm]; nlinarith [he]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · have hcoef : z.re-b=a*Real.cos θ := by
        have hh : ‖z‖*(z.re-b-a*Real.cos θ)=0 := by nlinarith [h,congrArg (fun q : ℝ ↦ a*q) hc]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn.ne')
      have hrad : conchoidRadius a b θ=‖z‖ := by
        unfold conchoidRadius
        field_simp [hcn]
        nlinarith [hcoef,hc]
      exact ⟨θ,hcn,by rw [conchoidPoint,hrad]; exact signedPolarPoint_norm_nonnegativePolarAngle z⟩
    · have hcoef : z.re-b= -a*Real.cos θ := by
        have hh : ‖z‖*(z.re-b+a*Real.cos θ)=0 := by nlinarith [h,congrArg (fun q : ℝ ↦ a*q) hc]
        linarith [(mul_eq_zero.mp hh).resolve_left hn.ne']
      have hrad : conchoidRadius a b (θ+Real.pi)= -‖z‖ := by
        unfold conchoidRadius
        rw [Real.cos_add_pi]
        field_simp [hcn]
        nlinarith [hcoef,hc]
      refine ⟨θ+Real.pi,by change Real.cos (θ+Real.pi) ≠ 0; simpa only [Real.cos_add_pi,neg_ne_zero] using hcn,?_⟩
      rw [conchoidPoint,hrad,signedPolarPoint_neg_radius_eq_add_pi,
        show θ+Real.pi+Real.pi=θ+2*Real.pi by ring,signedPolarPoint_add_two_pi]
      exact signedPolarPoint_norm_nonnegativePolarAngle z


theorem conchoid_origin_cosine_criterion (a b : ℝ) :
    (0 : ℂ) ∈ conchoidCurve a b ↔
      ∃ c : ℝ, c ≠ 0 ∧ -1 ≤ c ∧ c ≤ 1 ∧ a*c+b=0 := by
  constructor
  · rintro ⟨t,ht,hp⟩
    change Real.cos t ≠ 0 at ht
    have hr : conchoidRadius a b t=0 := (signedPolarPoint_eq_zero_iff _ _).mp hp
    refine ⟨Real.cos t,ht,Real.neg_one_le_cos t,Real.cos_le_one t,?_⟩
    unfold conchoidRadius at hr
    have hh := congrArg (fun q : ℝ ↦ q*Real.cos t) hr
    field_simp [ht] at hh
    nlinarith [hh]
  · rintro ⟨c,hc,hL,hR,he⟩
    have hcos := Real.cos_arccos hL hR
    refine ⟨Real.arccos c,by change Real.cos (Real.arccos c) ≠ 0; rw [hcos]; exact hc,?_⟩
    rw [conchoidPoint,signedPolarPoint_eq_zero_iff]
    unfold conchoidRadius
    rw [hcos]
    field_simp [hc]
    nlinarith

theorem conchoid_origin_iff (a b : ℝ) :
    (0 : ℂ) ∈ conchoidCurve a b ↔
      (a=0 ∧ b=0) ∨ (a ≠ 0 ∧ b ≠ 0 ∧ |b| ≤ |a|) := by
  rw [conchoid_origin_cosine_criterion]
  constructor
  · rintro ⟨c,hc,hL,hR,he⟩
    by_cases ha : a=0
    · exact Or.inl ⟨ha,by simpa [ha] using he⟩
    · have hb : b ≠ 0 := by intro h; rw [h,add_zero] at he; exact (mul_ne_zero ha hc) he
      refine Or.inr ⟨ha,hb,?_⟩
      have heq : b= -a*c := by linarith
      rw [heq,abs_mul,abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg a) (abs_le.mpr ⟨hL,hR⟩)
  · rintro (⟨rfl,rfl⟩ | ⟨ha,hb,hab⟩)
    · exact ⟨1,one_ne_zero,by norm_num,le_rfl,by ring⟩
    · have hca : |(-b)/a| ≤ 1 := by
        rw [abs_div,abs_neg,div_le_iff₀ (abs_pos.mpr ha),one_mul]
        exact hab
      refine ⟨-b/a,div_ne_zero (neg_ne_zero.mpr hb) ha,(abs_le.mp hca).1,(abs_le.mp hca).2,?_⟩
      field_simp [ha]
      ring

theorem conchoid_actual_first_derivatives {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    HasDerivAt (conchoidX a b) (conchoidDX a t) t ∧
      HasDerivAt (conchoidY a b) (conchoidDY a b t) t := by
  change Real.cos t ≠ 0 at ht
  constructor
  · simpa only [conchoidX,conchoidDX,mul_neg,neg_mul] using!
      ((Real.hasDerivAt_cos t).const_mul a).add_const b
  · have h := ((Real.hasDerivAt_sin t).const_mul a).fun_add
      ((Real.hasDerivAt_tan ht).const_mul b)
    apply h.congr_deriv
    unfold conchoidDY
    ring

theorem conchoid_first_derivative_values {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    deriv (conchoidX a b) t=conchoidDX a t ∧
      deriv (conchoidY a b) t=conchoidDY a b t :=
  ⟨(conchoid_actual_first_derivatives ht).1.deriv,(conchoid_actual_first_derivatives ht).2.deriv⟩

theorem conchoid_actual_second_derivatives {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    HasDerivAt (deriv (conchoidX a b)) (conchoidDDX a t) t ∧
      HasDerivAt (deriv (conchoidY a b)) (conchoidDDY a b t) t := by
  change Real.cos t ≠ 0 at ht
  have hX : deriv (conchoidX a b)=conchoidDX a := by
    funext u
    exact (by simpa only [conchoidX,conchoidDX,mul_neg,neg_mul] using!
      (((Real.hasDerivAt_cos u).const_mul a).add_const b).deriv)
  rw [hX]
  constructor
  · simpa only [conchoidDX,conchoidDDX] using! (Real.hasDerivAt_sin t).const_mul (-a)
  · have hn : HasDerivAt (conchoidDY a b) (conchoidDDY a b t) t := by
      have h := ((Real.hasDerivAt_cos t).const_mul a).fun_add
        ((hasDerivAt_const t b).fun_div ((Real.hasDerivAt_cos t).fun_pow 2) (pow_ne_zero 2 ht))
      apply h.congr_deriv
      unfold conchoidDDY
      norm_num at *
      field_simp [ht]
    apply hn.congr_of_eventuallyEq
    have hD : ∀ᶠ u : ℝ in 𝓝 t, u ∈ conchoidDomain :=
      Real.continuous_cos.continuousAt.eventually_ne ht
    filter_upwards [hD] with u hu
    exact (conchoid_first_derivative_values (a := a) (b := b) hu).2

theorem conchoid_actual_third_derivatives {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    HasDerivAt (deriv (deriv (conchoidX a b))) (conchoidDDDX a t) t ∧
      HasDerivAt (deriv (deriv (conchoidY a b))) (conchoidDDDY a b t) t := by
  change Real.cos t ≠ 0 at ht
  have hD : ∀ᶠ u : ℝ in 𝓝 t, u ∈ conchoidDomain :=
    Real.continuous_cos.continuousAt.eventually_ne ht
  have hx : HasDerivAt (conchoidDDX a) (conchoidDDDX a t) t := by
    change HasDerivAt (fun u : ℝ ↦ -a*Real.cos u) (a*Real.sin t) t
    simpa only [mul_neg,neg_mul,neg_neg] using!
      (Real.hasDerivAt_cos t).const_mul (-a)
  have hy : HasDerivAt (conchoidDDY a b) (conchoidDDDY a b t) t := by
    have h := ((Real.hasDerivAt_sin t).const_mul (-a)).fun_add
      (((Real.hasDerivAt_sin t).const_mul (2*b)).fun_div
        ((Real.hasDerivAt_cos t).fun_pow 3) (pow_ne_zero 3 ht))
    apply h.congr_deriv
    unfold conchoidDDDY
    norm_num at *
    field_simp [ht]
    ring
  constructor
  · apply hx.congr_of_eventuallyEq
    filter_upwards [hD] with u hu
    exact (conchoid_actual_second_derivatives (a := a) (b := b) hu).1.deriv
  · apply hy.congr_of_eventuallyEq
    filter_upwards [hD] with u hu
    exact (conchoid_actual_second_derivatives (a := a) (b := b) hu).2.deriv


theorem conchoid_regular_iff {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    conchoidDX a t ≠ 0 ∨ conchoidDY a b t ≠ 0 ↔
      (a ≠ 0 ∨ b ≠ 0) ∧ ¬(Real.sin t=0 ∧ a*Real.cos t+b=0) := by
  change Real.cos t ≠ 0 at ht
  have hs := Real.sin_sq_add_cos_sq t
  unfold conchoidDX conchoidDY
  constructor
  · intro hr
    refine ⟨?_,?_⟩
    · by_contra hconst
      push Not at hconst
      rcases hr with h | h <;> apply h <;> simp [hconst.1,hconst.2]
    · rintro ⟨hz,he⟩
      have hc : (Real.cos t)^2=1 := by nlinarith [hs]
      rcases hr with h | h
      · apply h; rw [hz,mul_zero]
      · apply h; rw [hc,div_one]; exact he
  · rintro ⟨hn,hr⟩
    by_contra h
    push Not at h
    by_cases ha : a=0
    · have hb : b=0 := by
        have hh : b/(Real.cos t)^2=0 := by simpa only [ha,zero_mul,zero_add] using h.2
        exact (div_eq_zero_iff.mp hh).resolve_right (pow_ne_zero 2 ht)
      exact hn.elim (fun q ↦ q ha) (fun q ↦ q hb)
    · have hz : Real.sin t=0 := (mul_eq_zero.mp h.1).resolve_left (neg_ne_zero.mpr ha)
      have hc : (Real.cos t)^2=1 := by nlinarith [hs]
      apply hr
      refine ⟨hz,?_⟩
      simpa only [hc,div_one] using h.2

theorem conchoid_curvature_numerator {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    deriv (conchoidX a b) t*deriv (deriv (conchoidY a b)) t-
      deriv (deriv (conchoidX a b)) t*deriv (conchoidY a b) t=conchoidSignedCurvatureNumerator a b t := by
  change Real.cos t ≠ 0 at ht
  rw [(conchoid_first_derivative_values ht).1,(conchoid_first_derivative_values ht).2,
    (conchoid_actual_second_derivatives ht).1.deriv,(conchoid_actual_second_derivatives ht).2.deriv]
  unfold conchoidDX conchoidDY conchoidDDX conchoidDDY conchoidSignedCurvatureNumerator
  field_simp [ht]
  nlinarith [congrArg (fun q : ℝ ↦ a^2*(Real.cos t)^3*q) (Real.sin_sq_add_cos_sq t),
    congrArg (fun q : ℝ ↦ a*b*q) (Real.sin_sq_add_cos_sq t)]

theorem conchoid_signed_curvature_numerator_signs {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    (conchoidSignedCurvatureNumerator a b t=0 ↔ a=0 ∨ a*(Real.cos t)^3+3*b*(Real.cos t)^2-2*b=0) ∧
    (0 < conchoidSignedCurvatureNumerator a b t ↔
      0 < a*(a*(Real.cos t)^3+3*b*(Real.cos t)^2-2*b)*(Real.cos t)) ∧
    (conchoidSignedCurvatureNumerator a b t < 0 ↔
      a*(a*(Real.cos t)^3+3*b*(Real.cos t)^2-2*b)*(Real.cos t) < 0) := by
  change Real.cos t ≠ 0 at ht
  have h : conchoidSignedCurvatureNumerator a b t=
      a*(a*(Real.cos t)^3+3*b*(Real.cos t)^2-2*b)/(Real.cos t)^3 := by
    unfold conchoidSignedCurvatureNumerator
    field_simp [ht]
    ring
  have hsign : conchoidSignedCurvatureNumerator a b t*(Real.cos t)^4=
      a*(a*(Real.cos t)^3+3*b*(Real.cos t)^2-2*b)*(Real.cos t) := by
    rw [h]
    field_simp [ht]
  have h4 : 0 < (Real.cos t)^4 := by
    nlinarith [sq_pos_of_ne_zero (pow_ne_zero 2 ht)]
  refine ⟨by rw [h,div_eq_zero_iff,mul_eq_zero]; simp only [pow_ne_zero 3 ht,or_false],?_,?_⟩
  · rw [← hsign,mul_pos_iff_of_pos_right h4]
  · rw [← hsign]
    simpa only [zero_mul] using (mul_lt_mul_iff_left₀ h4 :
      conchoidSignedCurvatureNumerator a b t*(Real.cos t)^4 < 0*(Real.cos t)^4 ↔ conchoidSignedCurvatureNumerator a b t < 0).symm


theorem conchoid_reflection_and_period (a b t : ℝ) :
    conchoidX a b (-t)=conchoidX a b t ∧ conchoidY a b (-t)= -conchoidY a b t ∧
      conchoidX a b (t+2*Real.pi)=conchoidX a b t ∧
      conchoidY a b (t+2*Real.pi)=conchoidY a b t := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [conchoidX,Real.cos_neg]
  · simp only [conchoidY,Real.sin_neg,Real.tan_neg]
    ring
  · simp only [conchoidX,Real.cos_add_two_pi]
  · unfold conchoidY
    rw [Real.sin_add_two_pi,show t+2*Real.pi=(t+Real.pi)+Real.pi by ring,
      Real.tan_add_pi,Real.tan_add_pi]

theorem conchoid_axis_intersections {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    ((conchoidPoint a b t).re=0 ↔ conchoidRadius a b t=0) ∧
    ((conchoidPoint a b t).im=0 ↔ conchoidRadius a b t=0 ∨ Real.sin t=0) := by
  change Real.cos t ≠ 0 at ht
  simp only [conchoidPoint,signedPolarPoint_re,signedPolarPoint_im,mul_eq_zero,ht,or_false]
  trivial

theorem conchoid_coordinate_variation {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    (conchoidDX a t > 0 ↔ a*Real.sin t < 0) ∧
      (conchoidDX a t < 0 ↔ 0 < a*Real.sin t) ∧
      (conchoidDY a b t > 0 ↔ 0 < a*(Real.cos t)^3+b) ∧
      (conchoidDY a b t < 0 ↔ a*(Real.cos t)^3+b < 0) := by
  change Real.cos t ≠ 0 at ht
  constructor
  · unfold conchoidDX; constructor <;> intro h <;> linarith
  · constructor
    · unfold conchoidDX; constructor <;> intro h <;> linarith
    · have hq : conchoidDY a b t*(Real.cos t)^2=a*(Real.cos t)^3+b := by
        unfold conchoidDY
        field_simp [ht]
      rw [← hq]
      exact ⟨by rw [mul_pos_iff_of_pos_right (sq_pos_of_ne_zero ht)],
        by simpa only [zero_mul] using (mul_lt_mul_iff_left₀ (sq_pos_of_ne_zero ht) :
          conchoidDY a b t*(Real.cos t)^2 < 0*(Real.cos t)^2 ↔ conchoidDY a b t < 0).symm⟩


theorem conchoid_zero_offset_line {b : ℝ} (hb : b ≠ 0) (z : ℂ) :
    z ∈ conchoidCurve 0 b ↔ z.re=b := by
  rw [conchoid_complete_coordinate_image]
  constructor
  · rintro ⟨t,_,hx,_⟩
    simpa only [zero_mul,zero_add] using hx
  · intro hx
    refine ⟨Real.arctan (z.im/b), (Real.cos_arctan_pos _).ne',?_,?_⟩
    · simpa only [zero_mul,zero_add] using hx
    · simp only [zero_mul,zero_add,Real.tan_arctan]
      field_simp [hb]


theorem conchoid_zero_secant_circle {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    z ∈ conchoidCurve a 0 ↔ z.re ≠ 0 ∧ ‖z‖=|a| := by
  by_cases hz : z=0
  · subst z
    simp [conchoid_origin_iff,ha]
  · rw [conchoid_complete_nonzero_cartesian_image a 0 hz]
    constructor
    · rintro ⟨hx,he⟩
      have hn : ‖z‖^2=a^2 := by
        rw [sub_zero] at he
        have heq : z.re^2*((z.re^2+z.im^2)-a^2)=0 := by nlinarith [he]
        have hs := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (pow_ne_zero 2 hx))
        rw [Complex.sq_norm,Complex.normSq_apply]
        simpa only [pow_two] using hs
      refine ⟨hx,?_⟩
      nlinarith [sq_abs a,norm_nonneg z,abs_nonneg a]
    · rintro ⟨hx,hn⟩
      refine ⟨hx,?_⟩
      have hs : z.re^2+z.im^2=a^2 := by
        calc
          z.re^2+z.im^2 = ‖z‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
          _ = a^2 := by rw [hn,sq_abs]
      rw [sub_zero,hs]
      ring


theorem conchoid_signed_curvature_numerator_hasDerivAt {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    HasDerivAt (conchoidSignedCurvatureNumerator a b)
      (3*a*b*Real.sin t*((Real.cos t)^2-2)/(Real.cos t)^4) t := by
  change Real.cos t ≠ 0 at ht
  have h := ((((Real.hasDerivAt_cos t).fun_pow 2).const_mul 3).sub_const 2).fun_div
    ((Real.hasDerivAt_cos t).fun_pow 3) (pow_ne_zero 3 ht)
  have hh := (h.const_mul (a*b)).const_add (a^2)
  apply hh.congr_deriv
  norm_num at *
  field_simp [ht]
  ring


theorem conchoid_regular_signed_curvature_numerator_zero_simple {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hr : conchoidDX a t ≠ 0 ∨ conchoidDY a b t ≠ 0)
    (hz : conchoidSignedCurvatureNumerator a b t=0) :
    3*a*b*Real.sin t*((Real.cos t)^2-2)/(Real.cos t)^4 ≠ 0 := by
  change Real.cos t ≠ 0 at ht
  have hc2 : (Real.cos t)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.sin t)]
  have hb : b ≠ 0 := by
    intro hb
    have hN : a^2=0 := by simpa [conchoidSignedCurvatureNumerator,hb] using hz
    exact (pow_ne_zero 2 ha) hN
  have hs : Real.sin t ≠ 0 := by
    intro hs
    have hc : (Real.cos t)^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
    have he : a*Real.cos t+b=0 := by
      have hp := ((conchoid_signed_curvature_numerator_signs ht).1.mp hz).resolve_left ha
      have h3 : (Real.cos t)^3=Real.cos t := by rw [pow_succ,hc,one_mul]
      rw [h3,hc] at hp
      linarith
    exact ((conchoid_regular_iff ht).mp hr).2 ⟨hs,he⟩
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) hs)
    (by intro h; nlinarith)) (pow_ne_zero 4 ht)


theorem differentiable_simple_zero_sign_change {f : ℝ → ℝ} {t d : ℝ}
    (hf : HasDerivAt f d t) (hzero : f t=0) :
    (0 < d → (∀ᶠ s : ℝ in 𝓝[<] t, f s < 0) ∧ (∀ᶠ s : ℝ in 𝓝[>] t, 0 < f s)) ∧
    (d < 0 → (∀ᶠ s : ℝ in 𝓝[<] t, 0 < f s) ∧ (∀ᶠ s : ℝ in 𝓝[>] t, f s < 0)) := by
  have he (s : ℝ) (hs : s ≠ t) : f s=slope f t s*(s-t) := by
    rw [slope_def_field,hzero,sub_zero]
    field_simp [sub_ne_zero.mpr hs]
  constructor
  · intro hd
    have hp := hf.tendsto_slope.eventually (eventually_gt_nhds hd)
    constructor
    · filter_upwards [Filter.Eventually.filter_mono (nhdsLT_le_nhdsNE t) hp,self_mem_nhdsWithin] with s hs (hst : s < t)
      rw [he s hst.ne]
      exact mul_neg_of_pos_of_neg hs (sub_neg.mpr hst)
    · filter_upwards [Filter.Eventually.filter_mono (nhdsGT_le_nhdsNE t) hp,self_mem_nhdsWithin] with s hs (hst : t < s)
      rw [he s hst.ne']
      exact mul_pos hs (sub_pos.mpr hst)
  · intro hd
    have hp := hf.tendsto_slope.eventually (eventually_lt_nhds hd)
    constructor
    · filter_upwards [Filter.Eventually.filter_mono (nhdsLT_le_nhdsNE t) hp,self_mem_nhdsWithin] with s hs (hst : s < t)
      rw [he s hst.ne]
      exact mul_pos_of_neg_of_neg hs (sub_neg.mpr hst)
    · filter_upwards [Filter.Eventually.filter_mono (nhdsGT_le_nhdsNE t) hp,self_mem_nhdsWithin] with s hs (hst : t < s)
      rw [he s hst.ne']
      exact mul_neg_of_neg_of_pos hs (sub_pos.mpr hst)


theorem conchoid_regular_inflection_sign_change {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hr : conchoidDX a t ≠ 0 ∨ conchoidDY a b t ≠ 0)
    (hz : conchoidSignedCurvatureNumerator a b t=0) :
    ((∀ᶠ s : ℝ in 𝓝[<] t, conchoidSignedCurvatureNumerator a b s < 0) ∧
      (∀ᶠ s : ℝ in 𝓝[>] t, 0 < conchoidSignedCurvatureNumerator a b s)) ∨
    ((∀ᶠ s : ℝ in 𝓝[<] t, 0 < conchoidSignedCurvatureNumerator a b s) ∧
      (∀ᶠ s : ℝ in 𝓝[>] t, conchoidSignedCurvatureNumerator a b s < 0)) := by
  change Real.cos t ≠ 0 at ht
  have hd := conchoid_regular_signed_curvature_numerator_zero_simple ht ha hr hz
  have hc := differentiable_simple_zero_sign_change (conchoid_signed_curvature_numerator_hasDerivAt ht) hz
  rcases lt_or_gt_of_ne hd with h | h
  · exact Or.inr (hc.2 h)
  · exact Or.inl (hc.1 h)


theorem conchoid_vertical_asymptote_residual (a b : ℝ) :
    Tendsto (fun t : ℝ ↦ conchoidX a b t-b) (𝓝[<] (Real.pi/2)) (𝓝 0) ∧
      Tendsto (fun t : ℝ ↦ conchoidX a b t-b) (𝓝[>] (-(Real.pi/2))) (𝓝 0) := by
  have h : ∀ q : ℝ, Real.cos q=0 → Tendsto (fun t : ℝ ↦ conchoidX a b t-b) (𝓝 q) (𝓝 0) := by
    intro q hq
    simpa only [conchoidX,add_sub_cancel_right,hq,mul_zero] using!
      (Real.continuous_cos.continuousAt (x := q)).tendsto.const_mul a
  exact ⟨(h _ Real.cos_pi_div_two).mono_left nhdsWithin_le_nhds,
    (h _ (by rw [Real.cos_neg,Real.cos_pi_div_two])).mono_left nhdsWithin_le_nhds⟩

theorem conchoid_actual_infinite_pole_limits {a b : ℝ} :
    (0 < b → Tendsto (conchoidY a b) (𝓝[<] (Real.pi/2)) atTop ∧
      Tendsto (conchoidY a b) (𝓝[>] (-(Real.pi/2))) atBot) ∧
    (b < 0 → Tendsto (conchoidY a b) (𝓝[<] (Real.pi/2)) atBot ∧
      Tendsto (conchoidY a b) (𝓝[>] (-(Real.pi/2))) atTop) := by
  have hs (q : ℝ) : Tendsto (fun t : ℝ ↦ a*Real.sin t) (𝓝 q) (𝓝 (a*Real.sin q)) :=
    Real.continuous_sin.continuousAt.tendsto.const_mul a
  constructor
  · intro hb
    exact ⟨((Real.tendsto_tan_pi_div_two.const_mul_atTop hb).atTop_add
        ((hs _).mono_left nhdsWithin_le_nhds)).congr (fun t ↦ by unfold conchoidY; ring),
      ((Real.tendsto_tan_neg_pi_div_two.const_mul_atBot hb).atBot_add
        ((hs _).mono_left nhdsWithin_le_nhds)).congr (fun t ↦ by unfold conchoidY; ring)⟩
  · intro hb
    exact ⟨((Real.tendsto_tan_pi_div_two.const_mul_atTop_of_neg hb).atBot_add
        ((hs _).mono_left nhdsWithin_le_nhds)).congr (fun t ↦ by unfold conchoidY; ring),
      ((Real.tendsto_tan_neg_pi_div_two.const_mul_atBot_of_neg hb).atTop_add
        ((hs _).mono_left nhdsWithin_le_nhds)).congr (fun t ↦ by unfold conchoidY; ring)⟩


theorem conchoid_pole_affine_asymptote_unique {a b : ℝ} (hb : b ≠ 0)
    (u v w : ℝ) :
    Tendsto (fun t : ℝ ↦ u*conchoidX a b t+v*conchoidY a b t+w)
      (𝓝[<] (Real.pi/2)) (𝓝 0) ↔ v=0 ∧ u*b+w=0 := by
  have hX : Tendsto (conchoidX a b) (𝓝[<] (Real.pi/2)) (𝓝 b) := by
    simpa only [conchoidX,Real.cos_pi_div_two,mul_zero,zero_add] using!
      (((Real.continuous_cos.continuousAt (x := Real.pi/2)).tendsto.const_mul a).add_const b).mono_left nhdsWithin_le_nhds
  have hi : Tendsto (fun t : ℝ ↦ (conchoidY a b t)⁻¹) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact ((conchoid_actual_infinite_pole_limits (a := a)).2 h).1.inv_tendsto_atBot
    · exact ((conchoid_actual_infinite_pole_limits (a := a)).1 h).1.inv_tendsto_atTop
  have hn : ∀ᶠ t : ℝ in 𝓝[<] (Real.pi/2), conchoidY a b t ≠ 0 := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact (((conchoid_actual_infinite_pole_limits (a := a)).2 h).1.eventually
        (eventually_lt_atBot (0 : ℝ))).mono (fun _ ht ↦ ht.ne)
    · exact (((conchoid_actual_infinite_pole_limits (a := a)).1 h).1.eventually
        (eventually_gt_atTop (0 : ℝ))).mono (fun _ ht ↦ ht.ne')
  constructor
  · intro h
    have hcoef : Tendsto (fun t : ℝ ↦ (u*conchoidX a b t+v*conchoidY a b t+w)*(conchoidY a b t)⁻¹-
      (u*conchoidX a b t+w)*(conchoidY a b t)⁻¹) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
      simpa only [mul_zero,sub_zero] using! (h.mul hi).sub ((((hX.const_mul u).add_const w).mul hi))
    have hv : v=0 := by
      have hc : Tendsto (fun _ : ℝ ↦ v) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
        apply hcoef.congr'
        filter_upwards [hn] with t ht
        field_simp [ht]
        ring
      exact tendsto_nhds_unique tendsto_const_nhds hc
    refine ⟨hv,?_⟩
    have hc : Tendsto (fun t : ℝ ↦ u*conchoidX a b t+v*conchoidY a b t+w)
        (𝓝[<] (Real.pi/2)) (𝓝 (u*b+w)) := by
      simpa only [hv,zero_mul,add_zero] using! (hX.const_mul u).add_const w
    exact tendsto_nhds_unique hc h
  · rintro ⟨rfl,hw⟩
    simpa only [zero_mul,add_zero,hw] using! (hX.const_mul u).add_const w

/-- Bài 16(g): khảo sát `r = a + b sec φ` trên `cos φ ≠ 0`, với `a, b ∈ ℝ`. -/
theorem source_conchoid_polar_curve_investigation (a b : ℝ) :
    (∀ z : ℂ, z ∈ conchoidCurve a b ↔ ∃ t : ℝ, Real.cos t ≠ 0 ∧
      z.re=a*Real.cos t+b ∧ z.im=a*Real.sin t+b*Real.tan t) ∧
    (∀ z : ℂ, z ≠ 0 → (z ∈ conchoidCurve a b ↔ z.re ≠ 0 ∧
      (z.re-b)^2*(z.re^2+z.im^2)=a^2*z.re^2)) ∧
    ((0 : ℂ) ∈ conchoidCurve a b ↔ (a=0 ∧ b=0) ∨ (a ≠ 0 ∧ b ≠ 0 ∧ |b| ≤ |a|)) ∧
    (∀ t ∈ conchoidDomain, HasDerivAt (conchoidX a b) (conchoidDX a t) t ∧
      HasDerivAt (conchoidY a b) (conchoidDY a b t) t) ∧
    (∀ t ∈ conchoidDomain, conchoidDX a t ≠ 0 ∨ conchoidDY a b t ≠ 0 ↔
      (a ≠ 0 ∨ b ≠ 0) ∧ ¬(Real.sin t=0 ∧ a*Real.cos t+b=0)) ∧
    (b ≠ 0 → ∀ u v w : ℝ, Tendsto (fun t : ℝ ↦ u*conchoidX a b t+v*conchoidY a b t+w)
      (𝓝[<] (Real.pi/2)) (𝓝 0) ↔ v=0 ∧ u*b+w=0) := by
  exact ⟨conchoid_complete_coordinate_image a b,fun z hz ↦ conchoid_complete_nonzero_cartesian_image a b hz,
    conchoid_origin_iff a b,fun _ ht ↦ conchoid_actual_first_derivatives ht,
    fun _ ht ↦ conchoid_regular_iff ht,fun hb ↦ conchoid_pole_affine_asymptote_unique hb⟩


theorem conchoid_radius_hasDerivAt {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    HasDerivAt (conchoidRadius a b) (b*Real.sin t/(Real.cos t)^2) t := by
  change Real.cos t ≠ 0 at ht
  have h := ((hasDerivAt_const t b).fun_div (Real.hasDerivAt_cos t) ht).const_add a
  apply h.congr_deriv
  ring

theorem conchoid_domain_mem_nhds {t : ℝ} (ht : t ∈ conchoidDomain) :
    conchoidDomain ∈ 𝓝 t := Real.continuous_cos.continuousAt.eventually_ne ht

theorem conchoid_polar_velocity_identities {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    (b*Real.sin t/(Real.cos t)^2)*Real.cos t-conchoidRadius a b t*Real.sin t=conchoidDX a t ∧
      (b*Real.sin t/(Real.cos t)^2)*Real.sin t+conchoidRadius a b t*Real.cos t=conchoidDY a b t := by
  change Real.cos t ≠ 0 at ht
  unfold conchoidRadius conchoidDX conchoidDY
  constructor
  · field_simp [ht]
    ring
  · field_simp [ht]
    nlinarith [congrArg (fun q : ℝ ↦ b*q) (Real.sin_sq_add_cos_sq t)]

theorem conchoid_horizontal_tangent_iff {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (hx : conchoidDX a t ≠ 0) :
    HasHorizontalPolarTangent conchoidDomain (conchoidRadius a b) t ↔
      a*(Real.cos t)^3+b=0 := by
  change Real.cos t ≠ 0 at ht
  have hvel := conchoid_polar_velocity_identities (a := a) (b := b) ht
  have hx' : (b*Real.sin t/(Real.cos t)^2)*Real.cos t-conchoidRadius a b t*Real.sin t ≠ 0 := by
    rw [hvel.1]; exact hx
  rw [horizontal_polar_tangent_iff (conchoid_domain_mem_nhds ht) (conchoid_radius_hasDerivAt ht) hx',hvel.2]
  have he : conchoidDY a b t*(Real.cos t)^2=a*(Real.cos t)^3+b := by
    unfold conchoidDY
    field_simp [ht]
  rw [← he,mul_eq_zero,or_iff_left (pow_ne_zero 2 ht)]

theorem conchoid_vertical_tangent_iff {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hy : conchoidDY a b t ≠ 0) :
    HasVerticalPolarTangent conchoidDomain (conchoidRadius a b) t ↔ Real.sin t=0 := by
  change Real.cos t ≠ 0 at ht
  have hvel := conchoid_polar_velocity_identities (a := a) (b := b) ht
  have hy' : (b*Real.sin t/(Real.cos t)^2)*Real.sin t+conchoidRadius a b t*Real.cos t ≠ 0 := by
    rw [hvel.2]; exact hy
  rw [vertical_polar_tangent_iff (conchoid_domain_mem_nhds ht) (conchoid_radius_hasDerivAt ht) hy',hvel.1]
  simp only [conchoidDX,mul_eq_zero,neg_ne_zero.mpr ha,false_or]


theorem conchoid_origin_parameter_classification {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hp : conchoidPoint a b t=0) :
    (conchoidDX a t ≠ 0 ∨ conchoidDY a b t ≠ 0 ↔ Real.sin t ≠ 0) ∧
      (Real.sin t=0 ↔ |b|=|a|) := by
  change Real.cos t ≠ 0 at ht
  have hr : conchoidRadius a b t=0 := (signedPolarPoint_eq_zero_iff _ _).mp hp
  have he : a*Real.cos t+b=0 := by
    unfold conchoidRadius at hr
    have hh := congrArg (fun q : ℝ ↦ q*Real.cos t) hr
    field_simp [ht] at hh
    nlinarith [hh]
  constructor
  · rw [conchoid_regular_iff ht]
    simp [ha,he]
  · have hsq : b^2=a^2*(Real.cos t)^2 := by nlinarith [congrArg (fun q : ℝ ↦ q^2) he]
    constructor
    · intro hs
      have hc : (Real.cos t)^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
      nlinarith [hsq,sq_abs a,sq_abs b,abs_nonneg a,abs_nonneg b]
    · intro hab
      have hs : a^2*(Real.sin t)^2=0 := by
        nlinarith [hsq,congrArg (fun q : ℝ ↦ q^2) hab,sq_abs a,sq_abs b,
          congrArg (fun q : ℝ ↦ a^2*q) (Real.sin_sq_add_cos_sq t)]
      exact (sq_eq_zero_iff.mp ((mul_eq_zero.mp hs).resolve_left (pow_ne_zero 2 ha)))


theorem conchoid_cusp_actual_jets {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hp : conchoidPoint a b t=0) (hs : Real.sin t=0) :
    deriv (conchoidX a b) t=0 ∧ deriv (conchoidY a b) t=0 ∧
      deriv (deriv (conchoidX a b)) t=b ∧ deriv (deriv (conchoidY a b)) t=0 ∧ b ≠ 0 := by
  change Real.cos t ≠ 0 at ht
  have hc : (Real.cos t)^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  have hr : conchoidRadius a b t=0 := (signedPolarPoint_eq_zero_iff _ _).mp hp
  have he : a*Real.cos t+b=0 := by
    unfold conchoidRadius at hr
    have hh := congrArg (fun q : ℝ ↦ q*Real.cos t) hr
    field_simp [ht] at hh
    nlinarith [hh]
  have hb : b ≠ 0 := by intro hb; rw [hb,add_zero] at he; exact (mul_ne_zero ha ht) he
  rw [(conchoid_first_derivative_values ht).1,(conchoid_first_derivative_values ht).2,
    (conchoid_actual_second_derivatives ht).1.deriv,(conchoid_actual_second_derivatives ht).2.deriv]
  refine ⟨by simp [conchoidDX,hs],by simp only [conchoidDY,hc,div_one]; exact he,
    by unfold conchoidDDX; linarith,by simp [conchoidDDY,hs],hb⟩


theorem conchoid_cusp_independent_actual_jets {a b t : ℝ} (ht : t ∈ conchoidDomain)
    (ha : a ≠ 0) (hp : conchoidPoint a b t=0) (hs : Real.sin t=0) :
    deriv (deriv (deriv (conchoidX a b))) t=0 ∧
      deriv (deriv (deriv (conchoidY a b))) t=3*b ∧
      deriv (deriv (conchoidX a b)) t*deriv (deriv (deriv (conchoidY a b))) t-
        deriv (deriv (conchoidY a b)) t*deriv (deriv (deriv (conchoidX a b))) t=3*b^2 ∧
      3*b^2 ≠ 0 := by
  change Real.cos t ≠ 0 at ht
  rcases conchoid_cusp_actual_jets ht ha hp hs with ⟨_,_,hxx,hyy,hb⟩
  have hc : (Real.cos t)^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  have he : -a*Real.cos t=b := by
    rw [(conchoid_actual_second_derivatives ht).1.deriv] at hxx
    exact hxx
  have hxxx : deriv (deriv (deriv (conchoidX a b))) t=0 := by
    rw [(conchoid_actual_third_derivatives ht).1.deriv]
    simp [conchoidDDDX,hs]
  have hyyy : deriv (deriv (deriv (conchoidY a b))) t=3*b := by
    rw [(conchoid_actual_third_derivatives ht).2.deriv]
    simp only [conchoidDDDY,hs,zero_pow (by decide : 2 ≠ 0),mul_zero,
      zero_div,add_zero,hc,div_one,he]
    ring
  refine ⟨hxxx,hyyy,?_,mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)⟩
  rw [hxx,hyy,hxxx,hyyy]
  ring

theorem conchoid_zero_constants : conchoidCurve 0 0={0} := by
  ext z
  constructor
  · rintro ⟨t,_,rfl⟩
    simp [conchoidPoint,conchoidRadius,signedPolarPoint_zero_radius]
  · rintro (rfl : z=0)
    exact ⟨0,by simp [conchoidDomain],by simp [conchoidPoint,conchoidRadius,signedPolarPoint_zero_radius]⟩




theorem conchoid_pi_shift_domain_and_coordinates (a b t : ℝ) :
    (t+Real.pi ∈ conchoidDomain ↔ t ∈ conchoidDomain) ∧
      conchoidX a b (t+Real.pi)=conchoidX (-a) b t ∧
      conchoidY a b (t+Real.pi)=conchoidY (-a) b t := by
  constructor
  · simp only [conchoidDomain,mem_ofPred_eq,Real.cos_add_pi,neg_ne_zero]
  · unfold conchoidX conchoidY
    rw [Real.cos_add_pi,Real.sin_add_pi,Real.tan_add_pi]
    constructor <;> ring

theorem conchoid_pi_shift_radius (a b t : ℝ) :
    conchoidRadius a b (t+Real.pi)= -conchoidRadius (-a) b t := by
  unfold conchoidRadius
  rw [Real.cos_add_pi,div_neg]
  ring


theorem conchoid_pi_shift_point {a b t : ℝ} (ht : t ∈ conchoidDomain) :
    conchoidPoint a b (t+Real.pi)=conchoidPoint (-a) b t := by
  change Real.cos t ≠ 0 at ht
  have hs := conchoid_pi_shift_domain_and_coordinates a b t
  have ht' := hs.1.mpr ht
  apply Complex.ext
  · exact (conchoid_actual_coordinates ht').1.trans
      (hs.2.1.trans (conchoid_actual_coordinates ht).1.symm)
  · exact (conchoid_actual_coordinates ht').2.trans
      (hs.2.2.trans (conchoid_actual_coordinates ht).2.symm)


def conchoidPole (n : ℤ) : ℝ := Real.pi/2+n*Real.pi

theorem conchoid_pole_cosine_zero (n : ℤ) : Real.cos (conchoidPole n)=0 := by
  simp only [conchoidPole,Real.cos_add_int_mul_pi,Real.cos_pi_div_two,mul_zero]


theorem conchoid_tendsto_sub_const_one_sided (q d : ℝ) :
    Tendsto (fun t : ℝ ↦ t-d) (𝓝[<] q) (𝓝[<] (q-d)) ∧
      Tendsto (fun t : ℝ ↦ t-d) (𝓝[>] q) (𝓝[>] (q-d)) := by
  constructor
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < q)
      change t-d < q-d
      exact sub_lt_sub_right ht d
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : q < t)
      change q-d < t-d
      exact sub_lt_sub_right ht d


theorem conchoid_tan_pi_div_two_right :
    Tendsto Real.tan (𝓝[>] (Real.pi/2)) atBot := by
  have ht := (conchoid_tendsto_sub_const_one_sided (Real.pi/2) Real.pi).2
  have he : Real.pi/2-Real.pi= -(Real.pi/2) := by ring
  rw [he] at ht
  simpa only [Function.comp_def,Real.tan_sub_pi] using!
    Real.tendsto_tan_neg_pi_div_two.comp ht


theorem conchoid_tan_all_poles (n : ℤ) :
    Tendsto Real.tan (𝓝[<] (conchoidPole n)) atTop ∧
      Tendsto Real.tan (𝓝[>] (conchoidPole n)) atBot := by
  have ht := conchoid_tendsto_sub_const_one_sided (conchoidPole n) (n*Real.pi)
  have he : conchoidPole n-n*Real.pi=Real.pi/2 := by unfold conchoidPole; ring
  rw [he] at ht
  exact ⟨by simpa only [Function.comp_def,Real.tan_sub_int_mul_pi] using!
      Real.tendsto_tan_pi_div_two.comp ht.1,
    by simpa only [Function.comp_def,Real.tan_sub_int_mul_pi] using!
      conchoid_tan_pi_div_two_right.comp ht.2⟩


theorem conchoid_all_pole_domain_eventually (n : ℤ) :
    (∀ᶠ t : ℝ in 𝓝[<] (conchoidPole n), t ∈ conchoidDomain) ∧
      (∀ᶠ t : ℝ in 𝓝[>] (conchoidPole n), t ∈ conchoidDomain) := by
  have h := conchoid_tan_all_poles n
  constructor
  · filter_upwards [h.1.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    change Real.cos t ≠ 0
    intro hc
    rw [Real.tan_eq_sin_div_cos,hc,div_zero] at ht
    exact (lt_irrefl (0 : ℝ)) ht
  · filter_upwards [h.2.eventually (eventually_lt_atBot (0 : ℝ))] with t ht
    change Real.cos t ≠ 0
    intro hc
    rw [Real.tan_eq_sin_div_cos,hc,div_zero] at ht
    exact (lt_irrefl (0 : ℝ)) ht


theorem conchoid_all_pole_x_limits (a b : ℝ) (n : ℤ) :
    Tendsto (conchoidX a b) (𝓝[<] (conchoidPole n)) (𝓝 b) ∧
      Tendsto (conchoidX a b) (𝓝[>] (conchoidPole n)) (𝓝 b) := by
  have h : Tendsto (conchoidX a b) (𝓝 (conchoidPole n)) (𝓝 b) := by
    simpa only [conchoidX,conchoid_pole_cosine_zero,mul_zero,zero_add] using!
      ((Real.continuous_cos.continuousAt (x := conchoidPole n)).tendsto.const_mul a).add_const b
  exact ⟨h.mono_left nhdsWithin_le_nhds,h.mono_left nhdsWithin_le_nhds⟩


theorem conchoid_all_pole_y_limits (a b : ℝ) (n : ℤ) :
    (0 < b → Tendsto (conchoidY a b) (𝓝[<] (conchoidPole n)) atTop ∧
      Tendsto (conchoidY a b) (𝓝[>] (conchoidPole n)) atBot) ∧
    (b < 0 → Tendsto (conchoidY a b) (𝓝[<] (conchoidPole n)) atBot ∧
      Tendsto (conchoidY a b) (𝓝[>] (conchoidPole n)) atTop) := by
  have ht := conchoid_tan_all_poles n
  have hs : Tendsto (fun t : ℝ ↦ a*Real.sin t) (𝓝 (conchoidPole n))
      (𝓝 (a*Real.sin (conchoidPole n))) := Real.continuous_sin.continuousAt.tendsto.const_mul a
  constructor
  · intro hb
    exact ⟨((ht.1.const_mul_atTop hb).atTop_add (hs.mono_left nhdsWithin_le_nhds)).congr
      (fun t ↦ by unfold conchoidY; ring),
      ((ht.2.const_mul_atBot hb).atBot_add (hs.mono_left nhdsWithin_le_nhds)).congr
        (fun t ↦ by unfold conchoidY; ring)⟩
  · intro hb
    exact ⟨((ht.1.const_mul_atTop_of_neg hb).atBot_add (hs.mono_left nhdsWithin_le_nhds)).congr
      (fun t ↦ by unfold conchoidY; ring),
      ((ht.2.const_mul_atBot_of_neg hb).atTop_add (hs.mono_left nhdsWithin_le_nhds)).congr
        (fun t ↦ by unfold conchoidY; ring)⟩


theorem conchoid_affine_unique_of_limits {F : Filter ℝ} [F.NeBot]
    {f g : ℝ → ℝ} {b : ℝ} (hx : Tendsto f F (𝓝 b))
    (hi : Tendsto (fun t : ℝ ↦ (g t)⁻¹) F (𝓝 0))
    (hn : ∀ᶠ t : ℝ in F, g t ≠ 0) (u v w : ℝ) :
    Tendsto (fun t : ℝ ↦ u*f t+v*g t+w) F (𝓝 0) ↔ v=0 ∧ u*b+w=0 := by
  constructor
  · intro h
    have hcoef : Tendsto (fun t : ℝ ↦ (u*f t+v*g t+w)*(g t)⁻¹-
        (u*f t+w)*(g t)⁻¹) F (𝓝 0) := by
      simpa only [mul_zero,sub_zero] using! (h.mul hi).sub (((hx.const_mul u).add_const w).mul hi)
    have hv : v=0 := by
      have hc : Tendsto (fun _ : ℝ ↦ v) F (𝓝 0) := by
        apply hcoef.congr'
        filter_upwards [hn] with t ht
        field_simp [ht]
        ring
      exact tendsto_nhds_unique tendsto_const_nhds hc
    refine ⟨hv,?_⟩
    have hc : Tendsto (fun t : ℝ ↦ u*f t+v*g t+w) F (𝓝 (u*b+w)) := by
      simpa only [hv,zero_mul,add_zero] using! (hx.const_mul u).add_const w
    exact tendsto_nhds_unique hc h
  · rintro ⟨rfl,hw⟩
    simpa only [zero_mul,add_zero,hw] using! (hx.const_mul u).add_const w


theorem conchoid_all_pole_affine_asymptote_unique {a b : ℝ} (hb : b ≠ 0)
    (n : ℤ) (u v w : ℝ) :
    (Tendsto (fun t : ℝ ↦ u*conchoidX a b t+v*conchoidY a b t+w)
      (𝓝[<] (conchoidPole n)) (𝓝 0) ↔ v=0 ∧ u*b+w=0) ∧
    (Tendsto (fun t : ℝ ↦ u*conchoidX a b t+v*conchoidY a b t+w)
      (𝓝[>] (conchoidPole n)) (𝓝 0) ↔ v=0 ∧ u*b+w=0) := by
  have hx := conchoid_all_pole_x_limits a b n
  have hy := conchoid_all_pole_y_limits a b n
  rcases lt_or_gt_of_ne hb with h | h
  · have hl := (hy.2 h).1
    have hr := (hy.2 h).2
    exact ⟨conchoid_affine_unique_of_limits hx.1 hl.inv_tendsto_atBot
        ((hl.eventually (eventually_lt_atBot (0 : ℝ))).mono (fun _ ht ↦ ht.ne)) u v w,
      conchoid_affine_unique_of_limits hx.2 hr.inv_tendsto_atTop
        ((hr.eventually (eventually_gt_atTop (0 : ℝ))).mono (fun _ ht ↦ ht.ne')) u v w⟩
  · have hl := (hy.1 h).1
    have hr := (hy.1 h).2
    exact ⟨conchoid_affine_unique_of_limits hx.1 hl.inv_tendsto_atTop
        ((hl.eventually (eventually_gt_atTop (0 : ℝ))).mono (fun _ ht ↦ ht.ne')) u v w,
      conchoid_affine_unique_of_limits hx.2 hr.inv_tendsto_atBot
        ((hr.eventually (eventually_lt_atBot (0 : ℝ))).mono (fun _ ht ↦ ht.ne)) u v w⟩

end calculus.Chapter04.Section04ConchoidPolarCurveInvestigation
