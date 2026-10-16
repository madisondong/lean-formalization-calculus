import calculus.Chapter04.Section01Parametric
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(h): astroid và bốn đỉnh nhọn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2783, `x=a cos³t`, `y=a sin³t`, `0 ≤ t ≤ 2π`, `a > 0`. Phương trình ẩn dùng căn bậc ba thực có dấu.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04AstroidParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric
open calculus.Chapter03.Section03Exercises

def astroidX (a t : ℝ) : ℝ := a * Real.cos t ^ 3
def astroidY (a t : ℝ) : ℝ := a * Real.sin t ^ 3
def astroidDomain : Set ℝ := Icc 0 (2 * Real.pi)
def astroidCurve (a : ℝ) : Set (ℝ × ℝ) :=
  parametricCurve (astroidX a) (astroidY a) astroidDomain
def astroidImplicit (a : ℝ) : Set (ℝ × ℝ) :=
  {p | realNthRoot 3 (p.1 / a) ^ 2 + realNthRoot 3 (p.2 / a) ^ 2 = 1}
def astroidCuspPoints (a : ℝ) : Set (ℝ × ℝ) :=
  {(a, 0), (0, a), (-a, 0), (0, -a)}
def astroidTangent (a t : ℝ) : Set (ℝ × ℝ) :=
  {p | deriv (astroidY a) t * (p.1 - astroidX a t) =
    deriv (astroidX a) t * (p.2 - astroidY a t)}

theorem astroid_signed_root_cube (x : ℝ) : realNthRoot 3 x ^ 3 = x :=
  realNthRoot_pow (by norm_num) (show x ∈ nthRootDomain 3 from Or.inl (by decide))

theorem astroid_signed_root_of_cube (x : ℝ) : realNthRoot 3 (x ^ 3) = x := by
  exact (show Odd 3 from by decide).pow_injective (astroid_signed_root_cube (x ^ 3))

theorem astroid_complete_implicit_image {a : ℝ} (ha : 0 < a) :
    astroidCurve a = astroidImplicit a := by
  ext p
  constructor
  · rintro ⟨t, _, rfl⟩
    change realNthRoot 3 ((a * Real.cos t ^ 3) / a) ^ 2 +
      realNthRoot 3 ((a * Real.sin t ^ 3) / a) ^ 2 = 1
    rw [mul_div_cancel_left₀ _ ha.ne', mul_div_cancel_left₀ _ ha.ne',
      astroid_signed_root_of_cube, astroid_signed_root_of_cube]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · intro hp
    change realNthRoot 3 (p.1 / a) ^ 2 + realNthRoot 3 (p.2 / a) ^ 2 = 1 at hp
    obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hp
    refine ⟨t, ht, ?_⟩
    apply Prod.ext
    · change a * Real.cos t ^ 3 = p.1
      rw [hc, astroid_signed_root_cube, mul_div_cancel₀ _ ha.ne']
    · change a * Real.sin t ^ 3 = p.2
      rw [hs, astroid_signed_root_cube, mul_div_cancel₀ _ ha.ne']

theorem astroid_classical_polynomial_equation (a t : ℝ) :
    (astroidX a t ^ 2 + astroidY a t ^ 2 - a ^ 2) ^ 3 +
      27 * a ^ 2 * astroidX a t ^ 2 * astroidY a t ^ 2 = 0 := by
  have hunit : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h6 : Real.cos t ^ 6 + Real.sin t ^ 6 - 1 =
      -3 * Real.cos t ^ 2 * Real.sin t ^ 2 := by
    calc
      _ = (Real.cos t ^ 2 + Real.sin t ^ 2) ^ 3 -
        3 * Real.cos t ^ 2 * Real.sin t ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) - 1 := by ring
      _ = _ := by rw [hunit]; ring
  have hb : astroidX a t ^ 2 + astroidY a t ^ 2 - a ^ 2 =
      -3 * a ^ 2 * Real.cos t ^ 2 * Real.sin t ^ 2 := by
    calc
      _ = a ^ 2 * (Real.cos t ^ 6 + Real.sin t ^ 6 - 1) := by unfold astroidX astroidY; ring
      _ = _ := by rw [h6]; ring
  rw [hb]
  unfold astroidX astroidY
  ring

theorem astroid_actual_coordinate_derivatives (a t : ℝ) :
    HasDerivAt (astroidX a) (-3 * a * Real.cos t ^ 2 * Real.sin t) t ∧
      HasDerivAt (astroidY a) (3 * a * Real.sin t ^ 2 * Real.cos t) t := by
  constructor
  · unfold astroidX
    convert! ((Real.hasDerivAt_cos t).pow 3).const_mul a using 1
    ring
  · unfold astroidY
    convert! ((Real.hasDerivAt_sin t).pow 3).const_mul a using 1
    ring

theorem astroid_actual_derivative_values (a t : ℝ) :
    deriv (astroidX a) t = -3 * a * Real.cos t ^ 2 * Real.sin t ∧
      deriv (astroidY a) t = 3 * a * Real.sin t ^ 2 * Real.cos t :=
  ⟨(astroid_actual_coordinate_derivatives a t).1.deriv,
    (astroid_actual_coordinate_derivatives a t).2.deriv⟩

theorem astroid_actual_second_derivatives (a t : ℝ) :
    HasDerivAt (deriv (astroidX a))
      (6 * a * Real.cos t * Real.sin t ^ 2 - 3 * a * Real.cos t ^ 3) t ∧
    HasDerivAt (deriv (astroidY a))
      (6 * a * Real.sin t * Real.cos t ^ 2 - 3 * a * Real.sin t ^ 3) t := by
  have hx : deriv (astroidX a) = (fun u : ℝ ↦ -3 * a * Real.cos u ^ 2 * Real.sin u) :=
    funext (fun u ↦ (astroid_actual_derivative_values a u).1)
  have hy : deriv (astroidY a) = (fun u : ℝ ↦ 3 * a * Real.sin u ^ 2 * Real.cos u) :=
    funext (fun u ↦ (astroid_actual_derivative_values a u).2)
  rw [hx, hy]
  constructor
  · convert! (((Real.hasDerivAt_cos t).fun_pow 2).fun_mul (Real.hasDerivAt_sin t)).const_mul (-3 * a) using 1
    all_goals (norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  · convert! (((Real.hasDerivAt_sin t).fun_pow 2).fun_mul (Real.hasDerivAt_cos t)).const_mul (3 * a) using 1
    all_goals (norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)

theorem astroid_actual_third_derivatives (a t : ℝ) :
    HasDerivAt (deriv (deriv (astroidX a)))
      (21 * a * Real.cos t ^ 2 * Real.sin t - 6 * a * Real.sin t ^ 3) t ∧
    HasDerivAt (deriv (deriv (astroidY a)))
      (6 * a * Real.cos t ^ 3 - 21 * a * Real.sin t ^ 2 * Real.cos t) t := by
  have hx : deriv (deriv (astroidX a)) =
      (fun u : ℝ ↦ 6 * a * Real.cos u * Real.sin u ^ 2 - 3 * a * Real.cos u ^ 3) :=
    funext (fun u ↦ (astroid_actual_second_derivatives a u).1.deriv)
  have hy : deriv (deriv (astroidY a)) =
      (fun u : ℝ ↦ 6 * a * Real.sin u * Real.cos u ^ 2 - 3 * a * Real.sin u ^ 3) :=
    funext (fun u ↦ (astroid_actual_second_derivatives a u).2.deriv)
  rw [hx, hy]
  constructor
  · convert! (((Real.hasDerivAt_cos t).fun_mul ((Real.hasDerivAt_sin t).fun_pow 2)).const_mul (6 * a)).fun_sub
      (((Real.hasDerivAt_cos t).fun_pow 3).const_mul (3 * a)) using 1
    all_goals (norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  · convert! (((Real.hasDerivAt_sin t).fun_mul ((Real.hasDerivAt_cos t).fun_pow 2)).const_mul (6 * a)).fun_sub
      (((Real.hasDerivAt_sin t).fun_pow 3).const_mul (3 * a)) using 1
    all_goals (norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)

theorem astroid_continuous_compact (a : ℝ) :
    Continuous (astroidX a) ∧ Continuous (astroidY a) ∧ IsCompact (astroidCurve a) := by
  have hx : Continuous (astroidX a) := (Real.continuous_cos.pow 3).const_mul a
  have hy : Continuous (astroidY a) := (Real.continuous_sin.pow 3).const_mul a
  exact ⟨hx, hy, isCompact_Icc.image (hx.prodMk hy)⟩

theorem astroid_coordinate_bounds {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |astroidX a t| ≤ a ∧ |astroidY a t| ≤ a := by
  have hpow := (show Odd 3 from by decide).strictMono_pow (R := ℝ)
  have hc1 := mul_le_mul_of_nonneg_left (hpow.monotone (Real.neg_one_le_cos t)) ha.le
  have hc2 := mul_le_mul_of_nonneg_left (hpow.monotone (Real.cos_le_one t)) ha.le
  have hs1 := mul_le_mul_of_nonneg_left (hpow.monotone (Real.neg_one_le_sin t)) ha.le
  have hs2 := mul_le_mul_of_nonneg_left (hpow.monotone (Real.sin_le_one t)) ha.le
  norm_num at hc1 hc2 hs1 hs2
  exact ⟨abs_le.mpr ⟨hc1, hc2⟩, abs_le.mpr ⟨hs1, hs2⟩⟩

theorem astroid_quadrant_reflections (a t : ℝ) :
    parametricPoint (astroidX a) (astroidY a) (-t) = (astroidX a t, -astroidY a t) ∧
    parametricPoint (astroidX a) (astroidY a) (Real.pi - t) = (-astroidX a t, astroidY a t) ∧
    parametricPoint (astroidX a) (astroidY a) (t + Real.pi) = (-astroidX a t, -astroidY a t) := by
  simp only [parametricPoint, astroidX, astroidY, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_add_pi, Real.sin_add_pi,
    (show ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) from fun x ↦ by ring), mul_neg, and_self]

theorem astroid_named_cusps (a : ℝ) :
    parametricPoint (astroidX a) (astroidY a) 0 = (a, 0) ∧
    parametricPoint (astroidX a) (astroidY a) (Real.pi / 2) = (0, a) ∧
    parametricPoint (astroidX a) (astroidY a) Real.pi = (-a, 0) ∧
    parametricPoint (astroidX a) (astroidY a) (3 * Real.pi / 2) = (0, -a) ∧
    parametricPoint (astroidX a) (astroidY a) (2 * Real.pi) = (a, 0) := by
  have h3 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  simp only [parametricPoint, astroidX, astroidY, h3, Real.cos_add, Real.sin_add,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi,
    Real.sin_pi, Real.cos_two_pi, Real.sin_two_pi]
  norm_num

theorem astroid_regular_parameter_iff {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (deriv (astroidX a) t ≠ 0 ∨ deriv (astroidY a) t ≠ 0) ↔
      Real.cos t ≠ 0 ∧ Real.sin t ≠ 0 := by
  rw [(astroid_actual_derivative_values a t).1, (astroid_actual_derivative_values a t).2]
  simp only [mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  have hneg : (-3 : ℝ) ≠ 0 := by norm_num
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hane : a ≠ 0 := ha.ne'
  tauto


theorem astroid_singular_iff_cusp_point {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (deriv (astroidX a) t = 0 ∧ deriv (astroidY a) t = 0) ↔
      parametricPoint (astroidX a) (astroidY a) t ∈ astroidCuspPoints a := by
  constructor
  · intro h
    have hc : Real.cos t = 0 ∨ Real.sin t = 0 := by
      by_contra hn
      have hr := (astroid_regular_parameter_iff ha t).mpr
        ⟨fun hc ↦ hn (Or.inl hc), fun hs ↦ hn (Or.inr hs)⟩
      rcases hr with hr | hr
      · exact hr h.1
      · exact hr h.2
    rcases hc with hc | hs
    · rcases (Real.cos_eq_zero_iff_sin_eq.mp hc) with hs | hs
      · simp only [parametricPoint, astroidX, astroidY, hc, hs, astroidCuspPoints]
        norm_num
      · simp only [parametricPoint, astroidX, astroidY, hc, hs, astroidCuspPoints]
        norm_num
    · rcases (Real.sin_eq_zero_iff_cos_eq.mp hs) with hc | hc
      · simp only [parametricPoint, astroidX, astroidY, hc, hs, astroidCuspPoints]
        norm_num
      · simp only [parametricPoint, astroidX, astroidY, hc, hs, astroidCuspPoints]
        norm_num
  · intro hp
    have hzero : Real.cos t = 0 ∨ Real.sin t = 0 := by
      simp only [astroidCuspPoints, mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with hp | hp | hp | hp
      · right
        have h := congrArg Prod.snd hp
        change a * Real.sin t ^ 3 = 0 at h
        exact (eq_zero_of_pow_eq_zero (mul_eq_zero.mp h |>.resolve_left ha.ne'))
      · left
        have h := congrArg Prod.fst hp
        change a * Real.cos t ^ 3 = 0 at h
        exact (eq_zero_of_pow_eq_zero (mul_eq_zero.mp h |>.resolve_left ha.ne'))
      · right
        have h := congrArg Prod.snd hp
        change a * Real.sin t ^ 3 = 0 at h
        exact (eq_zero_of_pow_eq_zero (mul_eq_zero.mp h |>.resolve_left ha.ne'))
      · left
        have h := congrArg Prod.fst hp
        change a * Real.cos t ^ 3 = 0 at h
        exact (eq_zero_of_pow_eq_zero (mul_eq_zero.mp h |>.resolve_left ha.ne'))
    rw [(astroid_actual_derivative_values a t).1, (astroid_actual_derivative_values a t).2]
    rcases hzero with hc | hs
    · simp only [hc, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, and_self]
    · simp only [hs, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, and_self]

theorem astroid_half_open_parameter_injective {a : ℝ} (ha : 0 < a) :
    InjOn (parametricPoint (astroidX a) (astroidY a)) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change a * Real.cos s ^ 3 = a * Real.cos t ^ 3 at hx
  change a * Real.sin s ^ 3 = a * Real.sin t ^ 3 at hy
  have hc := (show Odd 3 from by decide).pow_injective (mul_left_cancel₀ ha.ne' hx)
  have hsin := (show Odd 3 from by decide).pow_injective (mul_left_cancel₀ ha.ne' hy)
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  have hangle := Real.Angle.cos_sin_inj hc hsin
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (0 : ℝ)) (p := 2 * Real.pi)
    (by simpa only [zero_add] using hs) (by simpa only [zero_add] using ht)).mp hangle

theorem astroid_singular_parameters_on_original_interval {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ astroidDomain) :
    (deriv (astroidX a) t = 0 ∧ deriv (astroidY a) t = 0) ↔
      t = 0 ∨ t = Real.pi / 2 ∨ t = Real.pi ∨
        t = 3 * Real.pi / 2 ∨ t = 2 * Real.pi := by
  have hn := astroid_named_cusps a
  have hinj := astroid_half_open_parameter_injective ha
  constructor
  · intro h
    by_cases h2 : t = 2 * Real.pi
    · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))
    have ht' : t ∈ Ico 0 (2 * Real.pi) := ⟨ht.1, lt_of_le_of_ne ht.2 h2⟩
    have hp := (astroid_singular_iff_cusp_point ha t).mp h
    simp only [astroidCuspPoints, mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with hp | hp | hp | hp
    · exact Or.inl (hinj ht' ⟨le_rfl, by linarith [Real.pi_pos]⟩ (hp.trans hn.1.symm))
    · exact Or.inr (Or.inl (hinj ht' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        (hp.trans hn.2.1.symm)))
    · exact Or.inr (Or.inr (Or.inl (hinj ht' ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
        (hp.trans hn.2.2.1.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj ht'
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (hp.trans hn.2.2.2.1.symm)))))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · apply (astroid_singular_iff_cusp_point ha 0).mpr
      rw [hn.1]; simp only [astroidCuspPoints, mem_insert_iff, true_or]
    · apply (astroid_singular_iff_cusp_point ha (Real.pi / 2)).mpr
      rw [hn.2.1]; simp only [astroidCuspPoints, mem_insert_iff, true_or, or_true]
    · apply (astroid_singular_iff_cusp_point ha Real.pi).mpr
      rw [hn.2.2.1]; simp only [astroidCuspPoints, mem_insert_iff, true_or, or_true]
    · apply (astroid_singular_iff_cusp_point ha (3 * Real.pi / 2)).mpr
      rw [hn.2.2.2.1]; simp only [astroidCuspPoints, mem_insert_iff, mem_singleton_iff, or_true]
    · apply (astroid_singular_iff_cusp_point ha (2 * Real.pi)).mpr
      rw [hn.2.2.2.2]; simp only [astroidCuspPoints, mem_insert_iff, true_or]

theorem astroid_only_endpoint_parameter_repetition {a : ℝ} (ha : 0 < a)
    {s t : ℝ} (hs : s ∈ astroidDomain) (ht : t ∈ astroidDomain) :
    parametricPoint (astroidX a) (astroidY a) s = parametricPoint (astroidX a) (astroidY a) t ↔
      s = t ∨ (s = 0 ∧ t = 2 * Real.pi) ∨ (s = 2 * Real.pi ∧ t = 0) := by
  have hn := astroid_named_cusps a
  have hclose := hn.1.trans hn.2.2.2.2.symm
  have hinj := astroid_half_open_parameter_injective ha
  constructor
  · intro he
    by_cases hs2 : s = 2 * Real.pi
    · by_cases ht2 : t = 2 * Real.pi
      · exact Or.inl (hs2.trans ht2.symm)
      · have ht' : t ∈ Ico 0 (2 * Real.pi) := ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
        have h0t : parametricPoint (astroidX a) (astroidY a) 0 =
            parametricPoint (astroidX a) (astroidY a) t := by rw [hclose, ← hs2]; exact he
        exact Or.inr (Or.inr ⟨hs2, (hinj ⟨le_rfl, by linarith [Real.pi_pos]⟩ ht' h0t).symm⟩)
    · by_cases ht2 : t = 2 * Real.pi
      · have hs' : s ∈ Ico 0 (2 * Real.pi) := ⟨hs.1, lt_of_le_of_ne hs.2 hs2⟩
        have hs0 : parametricPoint (astroidX a) (astroidY a) s =
            parametricPoint (astroidX a) (astroidY a) 0 := by rw [hclose, ← ht2]; exact he
        exact Or.inr (Or.inl ⟨hinj hs' ⟨le_rfl, by linarith [Real.pi_pos]⟩ hs0, ht2⟩)
      · exact Or.inl (hinj ⟨hs.1, lt_of_le_of_ne hs.2 hs2⟩
          ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩ he)
  · rintro (he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [he]
    · exact hclose
    · exact hclose.symm

theorem astroid_coordinate_monotonic_branches {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (astroidX a) (Icc 0 Real.pi) ∧
    StrictMonoOn (astroidX a) (Icc Real.pi (2 * Real.pi)) ∧
    StrictMonoOn (astroidY a) (Icc 0 (Real.pi / 2)) ∧
    StrictAntiOn (astroidY a) (Icc (Real.pi / 2) (3 * Real.pi / 2)) ∧
    StrictMonoOn (astroidY a) (Icc (3 * Real.pi / 2) (2 * Real.pi)) := by
  have hpow := (show Odd 3 from by decide).strictMono_pow (R := ℝ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact mul_lt_mul_of_pos_left (hpow (Real.strictAntiOn_cos hs ht hst)) ha
  · intro s hs t ht hst
    have h := Real.strictAntiOn_cos (show 2 * Real.pi - t ∈ Icc 0 Real.pi from
      ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      (show 2 * Real.pi - s ∈ Icc 0 Real.pi from
      ⟨by linarith [hs.2], by linarith [hs.1]⟩) (by linarith : 2 * Real.pi - t < 2 * Real.pi - s)
    rw [Real.cos_two_pi_sub, Real.cos_two_pi_sub] at h
    exact mul_lt_mul_of_pos_left (hpow h) ha
  · intro s hs t ht hst
    have h := Real.strictMonoOn_sin
      (show s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
      (show t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩) hst
    exact mul_lt_mul_of_pos_left (hpow h) ha
  · intro s hs t ht hst
    have h := Real.strictAntiOn_cos
      (show s - Real.pi / 2 ∈ Icc 0 Real.pi from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show t - Real.pi / 2 ∈ Icc 0 Real.pi from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (by linarith : s - Real.pi / 2 < t - Real.pi / 2)
    rw [Real.cos_sub_pi_div_two, Real.cos_sub_pi_div_two] at h
    exact mul_lt_mul_of_pos_left (hpow h) ha
  · intro s hs t ht hst
    have h := Real.strictMonoOn_sin
      (show 2 * Real.pi - t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [ht.2, Real.pi_pos], by linarith [ht.1]⟩)
      (show 2 * Real.pi - s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [hs.2, Real.pi_pos], by linarith [hs.1]⟩)
      (by linarith : 2 * Real.pi - t < 2 * Real.pi - s)
    rw [Real.sin_two_pi_sub, Real.sin_two_pi_sub] at h
    exact mul_lt_mul_of_pos_left (hpow (show Real.sin s < Real.sin t from by linarith)) ha

theorem astroid_signed_curvature_numerator (a t : ℝ) :
    deriv (astroidX a) t * deriv (deriv (astroidY a)) t -
      deriv (astroidY a) t * deriv (deriv (astroidX a)) t =
        -9 * a ^ 2 * Real.cos t ^ 2 * Real.sin t ^ 2 := by
  rw [(astroid_actual_derivative_values a t).1, (astroid_actual_derivative_values a t).2,
    (astroid_actual_second_derivatives a t).1.deriv, (astroid_actual_second_derivatives a t).2.deriv]
  nlinarith [congrArg (fun z : ℝ ↦ 9 * a ^ 2 * Real.cos t ^ 2 * Real.sin t ^ 2 * z)
    (Real.sin_sq_add_cos_sq t)]

theorem astroid_no_regular_inflection {a t : ℝ} (ha : 0 < a)
    (hr : deriv (astroidX a) t ≠ 0 ∨ deriv (astroidY a) t ≠ 0) :
    deriv (astroidX a) t * deriv (deriv (astroidY a)) t -
      deriv (astroidY a) t * deriv (deriv (astroidX a)) t < 0 := by
  obtain ⟨hc, hs⟩ := (astroid_regular_parameter_iff ha t).mp hr
  rw [astroid_signed_curvature_numerator]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num : (-9 : ℝ) < 0)
      (sq_pos_of_pos ha)) (sq_pos_of_ne_zero hc)) (sq_pos_of_ne_zero hs)

theorem astroid_cusp_jets (a t : ℝ) :
    (Real.sin t = 0 →
      deriv (astroidX a) t = 0 ∧ deriv (astroidY a) t = 0 ∧
      deriv (deriv (astroidX a)) t = -3 * a * Real.cos t ^ 3 ∧
      deriv (deriv (astroidY a)) t = 0 ∧
      deriv (deriv (deriv (astroidX a))) t = 0 ∧
      deriv (deriv (deriv (astroidY a))) t = 6 * a * Real.cos t ^ 3) ∧
    (Real.cos t = 0 →
      deriv (astroidX a) t = 0 ∧ deriv (astroidY a) t = 0 ∧
      deriv (deriv (astroidX a)) t = 0 ∧
      deriv (deriv (astroidY a)) t = -3 * a * Real.sin t ^ 3 ∧
      deriv (deriv (deriv (astroidX a))) t = -6 * a * Real.sin t ^ 3 ∧
      deriv (deriv (deriv (astroidY a))) t = 0) := by
  rw [(astroid_actual_derivative_values a t).1, (astroid_actual_derivative_values a t).2,
    (astroid_actual_second_derivatives a t).1.deriv, (astroid_actual_second_derivatives a t).2.deriv,
    (astroid_actual_third_derivatives a t).1.deriv, (astroid_actual_third_derivatives a t).2.deriv]
  constructor <;> intro h <;> simp [h]

theorem astroid_actual_regular_tangent {a t : ℝ} (ha : 0 < a)
    (hr : deriv (astroidX a) t ≠ 0 ∨ deriv (astroidY a) t ≠ 0) (p : ℝ × ℝ) :
    p ∈ astroidTangent a t ↔
      p.2 = astroidY a t - Real.tan t * (p.1 - astroidX a t) := by
  obtain ⟨hc, hs⟩ := (astroid_regular_parameter_iff ha t).mp hr
  have hx : deriv (astroidX a) t ≠ 0 := by
    rw [(astroid_actual_derivative_values a t).1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero 2 hc)) hs
  have hquot : deriv (astroidY a) t / deriv (astroidX a) t = -Real.tan t := by
    rw [(astroid_actual_derivative_values a t).1, (astroid_actual_derivative_values a t).2,
      Real.tan_eq_sin_div_cos]
    field_simp [ha.ne', hc, hs]
  constructor
  · intro h
    change deriv (astroidY a) t * (p.1 - astroidX a t) =
      deriv (astroidX a) t * (p.2 - astroidY a t) at h
    have heq : (deriv (astroidY a) t * (p.1 - astroidX a t)) /
        deriv (astroidX a) t = p.2 - astroidY a t :=
      (div_eq_iff hx).mpr (h.trans (mul_comm _ _))
    have hfrac : (deriv (astroidY a) t / deriv (astroidX a) t) *
        (p.1 - astroidX a t) = p.2 - astroidY a t := by
      rw [div_mul_eq_mul_div]; exact heq
    rw [hquot] at hfrac
    linarith
  · intro h
    change deriv (astroidY a) t * (p.1 - astroidX a t) =
      deriv (astroidX a) t * (p.2 - astroidY a t)
    have hm : deriv (astroidX a) t * (-Real.tan t) = deriv (astroidY a) t := by
      exact (mul_comm _ _).trans ((div_eq_iff hx).mp hquot).symm
    calc
      _ = (deriv (astroidX a) t * (-Real.tan t)) * (p.1 - astroidX a t) := by rw [hm]
      _ = _ := by rw [h]; ring


theorem astroid_cusp_second_third_jets_independent {a t : ℝ} (ha : 0 < a)
    (h : Real.cos t = 0 ∨ Real.sin t = 0) :
    (deriv (deriv (astroidX a)) t ≠ 0 ∨ deriv (deriv (astroidY a)) t ≠ 0) ∧
      deriv (deriv (astroidX a)) t * deriv (deriv (deriv (astroidY a))) t -
        deriv (deriv (astroidY a)) t * deriv (deriv (deriv (astroidX a))) t ≠ 0 := by
  rw [(astroid_actual_second_derivatives a t).1.deriv, (astroid_actual_second_derivatives a t).2.deriv,
    (astroid_actual_third_derivatives a t).1.deriv, (astroid_actual_third_derivatives a t).2.deriv]
  rcases h with hc | hs
  · rcases Real.cos_eq_zero_iff_sin_eq.mp hc with hs | hs <;>
      norm_num [hc, hs, mul_ne_zero_iff, ha.ne', pow_ne_zero]
  · rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
      norm_num [hc, hs, mul_ne_zero_iff, ha.ne', pow_ne_zero]

theorem astroid_unit_cubic_secant_identity {u v σ : ℝ}
    (hunit : u ^ 2 + v ^ 2 = 1) (hσ : σ ^ 2 = 1) :
    v ^ 3 / (u ^ 3 - σ ^ 3) =
      -v * (u + σ) / (u ^ 2 + u * σ + σ ^ 2) := by
  have hpos : 0 < u ^ 2 + u * σ + σ ^ 2 := by
    nlinarith [sq_nonneg (u + σ / 2)]
  by_cases hu : u = σ
  · rw [hu] at hunit ⊢
    have hv : v = 0 := by nlinarith [sq_nonneg v]
    simp only [hv, zero_pow (by decide : (3 : ℕ) ≠ 0), neg_zero, zero_mul, zero_div]
  · have hv : v ^ 2 = σ ^ 2 - u ^ 2 := by nlinarith [hunit, hσ]
    have hcube : v ^ 3 = -v * (u - σ) * (u + σ) := by
      calc
        _ = v * v ^ 2 := by ring
        _ = v * (σ ^ 2 - u ^ 2) := by rw [hv]
        _ = _ := by ring
    generalize hqd : u ^ 2 + u * σ + σ ^ 2 = q
    have hq : q ≠ 0 := by rw [← hqd]; exact hpos.ne'
    have hf : u ^ 3 - σ ^ 3 = (u - σ) * q := by rw [← hqd]; ring
    rw [hcube, hf]
    field_simp [hq, sub_ne_zero.mpr hu]

theorem astroid_cusp_actual_secant_directions {a : ℝ} (ha : 0 < a) (t₀ : ℝ) :
    (Real.sin t₀ = 0 →
      Tendsto (fun t : ℝ ↦ astroidY a t / (astroidX a t - astroidX a t₀))
        (𝓝[≠] t₀) (𝓝 0)) ∧
    (Real.cos t₀ = 0 →
      Tendsto (fun t : ℝ ↦ astroidX a t / (astroidY a t - astroidY a t₀))
        (𝓝[≠] t₀) (𝓝 0)) := by
  have hunit (t : ℝ) : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  constructor
  · intro hs
    have hc : Real.cos t₀ ^ 2 = 1 := by nlinarith [hunit t₀]
    have heq (t : ℝ) : astroidY a t / (astroidX a t - astroidX a t₀) =
        -Real.sin t * (Real.cos t + Real.cos t₀) /
          (Real.cos t ^ 2 + Real.cos t * Real.cos t₀ + Real.cos t₀ ^ 2) := by
      rw [show astroidX a t - astroidX a t₀ = a * (Real.cos t ^ 3 - Real.cos t₀ ^ 3) from by
        unfold astroidX; ring]
      change (a * Real.sin t ^ 3) / (a * (Real.cos t ^ 3 - Real.cos t₀ ^ 3)) = _
      rw [mul_div_mul_left _ _ ha.ne']
      exact astroid_unit_cubic_secant_identity (hunit t) hc
    have hd : Real.cos t₀ ^ 2 + Real.cos t₀ * Real.cos t₀ + Real.cos t₀ ^ 2 ≠ 0 := by
      nlinarith [hc]
    have hn : Continuous (fun t : ℝ ↦ -Real.sin t * (Real.cos t + Real.cos t₀)) :=
      Real.continuous_sin.neg.mul (Real.continuous_cos.add continuous_const)
    have hden : Continuous (fun t : ℝ ↦ Real.cos t ^ 2 +
        Real.cos t * Real.cos t₀ + Real.cos t₀ ^ 2) :=
      ((Real.continuous_cos.pow 2).add (Real.continuous_cos.mul continuous_const)).add continuous_const
    have h := (hn.tendsto t₀).div (hden.tendsto t₀) hd
    have hl : Tendsto (fun t : ℝ ↦ -Real.sin t * (Real.cos t + Real.cos t₀) /
        (Real.cos t ^ 2 + Real.cos t * Real.cos t₀ + Real.cos t₀ ^ 2)) (𝓝 t₀) (𝓝 0) := by
      simpa only [hs, neg_zero, zero_mul, zero_div] using! h
    exact (hl.congr (fun t ↦ (heq t).symm)).mono_left nhdsWithin_le_nhds
  · intro hc
    have hs : Real.sin t₀ ^ 2 = 1 := by nlinarith [hunit t₀]
    have heq (t : ℝ) : astroidX a t / (astroidY a t - astroidY a t₀) =
        -Real.cos t * (Real.sin t + Real.sin t₀) /
          (Real.sin t ^ 2 + Real.sin t * Real.sin t₀ + Real.sin t₀ ^ 2) := by
      rw [show astroidY a t - astroidY a t₀ = a * (Real.sin t ^ 3 - Real.sin t₀ ^ 3) from by
        unfold astroidY; ring]
      change (a * Real.cos t ^ 3) / (a * (Real.sin t ^ 3 - Real.sin t₀ ^ 3)) = _
      rw [mul_div_mul_left _ _ ha.ne']
      exact astroid_unit_cubic_secant_identity (by nlinarith [hunit t]) hs
    have hd : Real.sin t₀ ^ 2 + Real.sin t₀ * Real.sin t₀ + Real.sin t₀ ^ 2 ≠ 0 := by
      nlinarith [hs]
    have hn : Continuous (fun t : ℝ ↦ -Real.cos t * (Real.sin t + Real.sin t₀)) :=
      Real.continuous_cos.neg.mul (Real.continuous_sin.add continuous_const)
    have hden : Continuous (fun t : ℝ ↦ Real.sin t ^ 2 +
        Real.sin t * Real.sin t₀ + Real.sin t₀ ^ 2) :=
      ((Real.continuous_sin.pow 2).add (Real.continuous_sin.mul continuous_const)).add continuous_const
    have h := (hn.tendsto t₀).div (hden.tendsto t₀) hd
    have hl : Tendsto (fun t : ℝ ↦ -Real.cos t * (Real.sin t + Real.sin t₀) /
        (Real.sin t ^ 2 + Real.sin t * Real.sin t₀ + Real.sin t₀ ^ 2)) (𝓝 t₀) (𝓝 0) := by
      simpa only [hc, neg_zero, zero_mul, zero_div] using! h
    exact (hl.congr (fun t ↦ (heq t).symm)).mono_left nhdsWithin_le_nhds

def astroidCuspTangent (a t : ℝ) : Set (ℝ × ℝ) :=
  {p | deriv (deriv (astroidY a)) t * (p.1 - astroidX a t) =
    deriv (deriv (astroidX a)) t * (p.2 - astroidY a t)}

theorem astroid_actual_cusp_tangent_lines {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (Real.sin t = 0 → ∀ p : ℝ × ℝ, p ∈ astroidCuspTangent a t ↔ p.2 = 0) ∧
    (Real.cos t = 0 → ∀ p : ℝ × ℝ, p ∈ astroidCuspTangent a t ↔ p.1 = 0) := by
  constructor
  · intro hs p
    rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
      simp [astroidCuspTangent, (astroid_actual_second_derivatives a t).1.deriv,
        (astroid_actual_second_derivatives a t).2.deriv, astroidX, astroidY, hc, hs,
        mul_eq_zero, ha.ne']
  · intro hc p
    rcases Real.cos_eq_zero_iff_sin_eq.mp hc with hs | hs <;>
      simp [astroidCuspTangent, (astroid_actual_second_derivatives a t).1.deriv,
        (astroid_actual_second_derivatives a t).2.deriv, astroidX, astroidY, hc, hs,
        mul_eq_zero, ha.ne']


theorem source_astroid_parametric_curve_investigation {a : ℝ} (ha : 0 < a) :
    astroidCurve a = astroidImplicit a ∧ IsCompact (astroidCurve a) ∧
    (∀ t : ℝ, HasDerivAt (astroidX a) (-3 * a * Real.cos t ^ 2 * Real.sin t) t ∧
      HasDerivAt (astroidY a) (3 * a * Real.sin t ^ 2 * Real.cos t) t) ∧
    (∀ t : ℝ, (deriv (astroidX a) t ≠ 0 ∨ deriv (astroidY a) t ≠ 0) ↔
      Real.cos t ≠ 0 ∧ Real.sin t ≠ 0) ∧
    (∀ t : ℝ, (deriv (astroidX a) t = 0 ∧ deriv (astroidY a) t = 0) ↔
      parametricPoint (astroidX a) (astroidY a) t ∈ astroidCuspPoints a) ∧
    InjOn (parametricPoint (astroidX a) (astroidY a)) (Ico 0 (2 * Real.pi)) := by
  exact ⟨astroid_complete_implicit_image ha, (astroid_continuous_compact a).2.2,
    astroid_actual_coordinate_derivatives a, astroid_regular_parameter_iff ha,
    astroid_singular_iff_cusp_point ha, astroid_half_open_parameter_injective ha⟩

end calculus.Chapter04.Section04AstroidParametricCurveInvestigation
