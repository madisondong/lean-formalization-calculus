import calculus.Chapter04.Section01ParametricExercises
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(a): đường cong x=t²,y=t³−3t

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2773–2776, với `t∈ℝ`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04CubicLoopParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric
open calculus.Chapter04.Section01ParametricExercises

def cubicLoopX (t : ℝ) : ℝ := t ^ 2
def cubicLoopY (t : ℝ) : ℝ := t ^ 3 - 3 * t
def cubicLoopCurve : Set (ℝ × ℝ) := parametricCurve cubicLoopX cubicLoopY univ
def cubicLoopTangent (t : ℝ) : Set (ℝ × ℝ) :=
  {p | (3 * t ^ 2 - 3) * (p.1 - cubicLoopX t) = 2 * t * (p.2 - cubicLoopY t)}
def cubicLoopLineDistance (m b t : ℝ) : ℝ :=
  |cubicLoopY t - (m * cubicLoopX t + b)| / Real.sqrt (m ^ 2 + 1)

theorem cubic_loop_actual_first_derivatives (t : ℝ) :
    HasDerivAt cubicLoopX (2 * t) t ∧ HasDerivAt cubicLoopY (3 * t ^ 2 - 3) t := by
  constructor
  · simpa only [cubicLoopX, Nat.cast_ofNat, Nat.reduceSub, pow_one] using! hasDerivAt_pow 2 t
  · have h := (hasDerivAt_pow 3 t).fun_sub ((hasDerivAt_id t).const_mul 3)
    simpa only [cubicLoopY, Nat.cast_ofNat, Nat.reduceSub, id_eq, mul_one] using! h

theorem cubic_loop_derivative_functions :
    deriv cubicLoopX = (fun t : ℝ ↦ 2 * t) ∧
      deriv cubicLoopY = (fun t : ℝ ↦ 3 * t ^ 2 - 3) := by
  exact ⟨funext (fun t ↦ (cubic_loop_actual_first_derivatives t).1.deriv),
    funext (fun t ↦ (cubic_loop_actual_first_derivatives t).2.deriv)⟩

theorem cubic_loop_actual_second_derivatives (t : ℝ) :
    HasDerivAt (deriv cubicLoopX) 2 t ∧ HasDerivAt (deriv cubicLoopY) (6 * t) t := by
  rw [cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
  constructor
  · simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul 2
  · have h := ((hasDerivAt_pow 2 t).const_mul 3).sub_const 3
    apply h.congr_deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

theorem cubic_loop_regular_at_every_parameter (t : ℝ) :
    deriv cubicLoopX t ≠ 0 ∨ deriv cubicLoopY t ≠ 0 := by
  rw [cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
  by_cases ht : t = 0
  · right
    simp only [ht, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
    norm_num
  · left
    exact mul_ne_zero (by norm_num) ht

theorem cubic_loop_continuous_coordinates : Continuous cubicLoopX ∧ Continuous cubicLoopY :=
  ⟨continuous_iff_continuousAt.mpr (fun t ↦ (cubic_loop_actual_first_derivatives t).1.continuousAt),
    continuous_iff_continuousAt.mpr (fun t ↦ (cubic_loop_actual_first_derivatives t).2.continuousAt)⟩

theorem cubic_loop_reflection (t : ℝ) :
    cubicLoopX (-t) = cubicLoopX t ∧ cubicLoopY (-t) = -cubicLoopY t := by
  unfold cubicLoopX cubicLoopY
  constructor <;> ring

theorem cubic_loop_implicit_equation (t : ℝ) :
    0 ≤ cubicLoopX t ∧ (cubicLoopY t) ^ 2 = cubicLoopX t * (cubicLoopX t - 3) ^ 2 := by
  exact ⟨sq_nonneg t, by unfold cubicLoopX cubicLoopY; ring⟩

theorem cubic_loop_every_implicit_point {x y : ℝ} (hx : 0 ≤ x)
    (hxy : y ^ 2 = x * (x - 3) ^ 2) :
    ∃ t : ℝ, cubicLoopX t = x ∧ cubicLoopY t = y := by
  by_cases h3 : x = 3
  · have hy : y = 0 := by rw [h3] at hxy; nlinarith [sq_nonneg y]
    refine ⟨Real.sqrt 3, ?_, ?_⟩
    · simpa only [cubicLoopX, h3] using Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by rw [← h3]; exact hx)
    · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      change (Real.sqrt 3) ^ 3 - 3 * Real.sqrt 3 = y
      rw [hy, pow_succ, hs]
      ring
  · let t : ℝ := y / (x - 3)
    have ht : t ^ 2 = x := by
      dsimp only [t]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr h3))).mpr
      exact hxy
    refine ⟨t, ht, ?_⟩
    change t ^ 3 - 3 * t = y
    rw [pow_succ, ht]
    have hty : t * (x - 3) = y := div_mul_cancel₀ y (sub_ne_zero.mpr h3)
    nlinarith

theorem cubic_loop_complete_image :
    cubicLoopCurve = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 ^ 2 = p.1 * (p.1 - 3) ^ 2} := by
  ext p
  constructor
  · rintro ⟨t, _, rfl⟩
    exact cubic_loop_implicit_equation t
  · intro hp
    obtain ⟨t, hx, hy⟩ := cubic_loop_every_implicit_point hp.1 hp.2
    exact ⟨t, mem_univ t, Prod.ext hx hy⟩

theorem cubic_loop_distinct_parameter_intersection_iff (s t : ℝ) :
    s ≠ t ∧ parametricPoint cubicLoopX cubicLoopY s = parametricPoint cubicLoopX cubicLoopY t ↔
      t ≠ 0 ∧ s = -t ∧ t ^ 2 = 3 := by
  constructor
  · rintro ⟨hst, hpoint⟩
    have hx : s ^ 2 = t ^ 2 := congrArg Prod.fst hpoint
    have hy : s ^ 3 - 3 * s = t ^ 3 - 3 * t := congrArg Prod.snd hpoint
    have hprod : (s - t) * (s + t) = 0 := by nlinarith
    have hs : s = -t := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact False.elim (hst (sub_eq_zero.mp h))
      · linarith
    have ht0 : t ≠ 0 := by intro h; apply hst; simp only [hs, h, neg_zero]
    rw [hs] at hy
    have hzero : t * (t ^ 2 - 3) = 0 := by nlinarith [hy]
    exact ⟨ht0, hs, by rcases mul_eq_zero.mp hzero with h | h; exact False.elim (ht0 h); linarith⟩
  · rintro ⟨ht0, rfl, ht⟩
    refine ⟨by intro h; apply ht0; linarith, ?_⟩
    apply Prod.ext
    · change (-t) ^ 2 = t ^ 2
      ring
    · change (-t) ^ 3 - 3 * (-t) = t ^ 3 - 3 * t
      rw [show (-t) ^ 3 - 3 * (-t) = -(t ^ 3 - 3 * t) by ring,
        pow_succ, ht]
      ring

theorem cubic_loop_node_parameters :
    parametricPoint cubicLoopX cubicLoopY (Real.sqrt 3) = (3, 0) ∧
      parametricPoint cubicLoopX cubicLoopY (-Real.sqrt 3) = (3, 0) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  constructor
  · apply Prod.ext
    · exact hs
    · change (Real.sqrt 3) ^ 3 - 3 * Real.sqrt 3 = 0
      rw [pow_succ, hs]
      ring
  · apply Prod.ext
    · change (-Real.sqrt 3) ^ 2 = 3
      simpa only [neg_sq] using hs
    · change (-Real.sqrt 3) ^ 3 - 3 * (-Real.sqrt 3) = 0
      rw [show (-Real.sqrt 3) ^ 3 - 3 * (-Real.sqrt 3) =
        -(Real.sqrt 3 * ((Real.sqrt 3) ^ 2 - 3)) by ring, hs]
      ring

theorem cubic_loop_tangent_slope {t : ℝ} (ht : t ≠ 0) (p : ℝ × ℝ) :
    p ∈ cubicLoopTangent t ↔
      p.2 - cubicLoopY t = ((3 * t ^ 2 - 3) / (2 * t)) * (p.1 - cubicLoopX t) := by
  unfold cubicLoopTangent
  change (3 * t ^ 2 - 3) * (p.1 - cubicLoopX t) = 2 * t * (p.2 - cubicLoopY t) ↔ _
  have hd : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  rw [div_mul_eq_mul_div, eq_div_iff hd]
  constructor <;> intro h <;> nlinarith

theorem cubic_loop_special_tangents (p : ℝ × ℝ) :
    (p ∈ cubicLoopTangent 0 ↔ p.1 = 0) ∧
    (p ∈ cubicLoopTangent (-1) ↔ p.2 = 2) ∧
    (p ∈ cubicLoopTangent 1 ↔ p.2 = -2) ∧
    (p ∈ cubicLoopTangent (Real.sqrt 3) ↔ p.2 = Real.sqrt 3 * (p.1 - 3)) ∧
    (p ∈ cubicLoopTangent (-Real.sqrt 3) ↔ p.2 = -Real.sqrt 3 * (p.1 - 3)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsne : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
  have hc : (3 * (Real.sqrt 3) ^ 2 - 3) / (2 * Real.sqrt 3) = Real.sqrt 3 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hsne)).mpr
    nlinarith [hs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cubicLoopTangent, mem_ofPred_eq, cubicLoopX, cubicLoopY, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, sub_zero, zero_sub]
    constructor <;> intro h <;> linarith
  · norm_num only [cubicLoopTangent, mem_ofPred_eq, cubicLoopX, cubicLoopY]
    constructor <;> intro h <;> linarith
  · norm_num only [cubicLoopTangent, mem_ofPred_eq, cubicLoopX, cubicLoopY]
    constructor <;> intro h <;> linarith
  · rw [cubic_loop_tangent_slope hsne, hc]
    have hn := cubic_loop_node_parameters.1
    have hx := congrArg Prod.fst hn
    have hy := congrArg Prod.snd hn
    simp only [parametricPoint] at hx hy
    rw [hx, hy, sub_zero]
  · rw [cubic_loop_tangent_slope (neg_ne_zero.mpr hsne)]
    have hcoef : (3 * (-Real.sqrt 3) ^ 2 - 3) / (2 * (-Real.sqrt 3)) = -Real.sqrt 3 := by
      simp only [neg_sq, mul_neg, div_neg, hc]
    rw [hcoef]
    have hn := cubic_loop_node_parameters.2
    have hx := congrArg Prod.fst hn
    have hy := congrArg Prod.snd hn
    simp only [parametricPoint] at hx hy
    rw [hx, hy, sub_zero]

theorem cubic_loop_full_coordinate_variation (t : ℝ) :
    (deriv cubicLoopX t < 0 ↔ t < 0) ∧
    (deriv cubicLoopX t = 0 ↔ t = 0) ∧
    (0 < deriv cubicLoopX t ↔ 0 < t) ∧
    (deriv cubicLoopY t < 0 ↔ -1 < t ∧ t < 1) ∧
    (deriv cubicLoopY t = 0 ↔ t = -1 ∨ t = 1) ∧
    (0 < deriv cubicLoopY t ↔ t < -1 ∨ 1 < t) := by
  rw [cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
  refine ⟨by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith, ?_, ?_, ?_⟩
  · constructor
    · intro h
      constructor
      · by_contra hn
        nlinarith [sq_nonneg (t + 1), le_of_not_gt hn]
      · by_contra hn
        nlinarith [sq_nonneg (t - 1), le_of_not_gt hn]
    · rintro ⟨hl, hr⟩
      nlinarith [mul_pos (by linarith : 0 < t + 1) (by linarith : 0 < 1 - t)]
  · constructor
    · intro h
      have hz : (t + 1) * (t - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  · constructor
    · intro h
      by_cases hl : t < -1
      · exact Or.inl hl
      · right
        by_contra hr
        have hn := mul_nonneg (by linarith : 0 ≤ t + 1) (by linarith : 0 ≤ 1 - t)
        nlinarith
    · rintro (hl | hr)
      · nlinarith [sq_nonneg (t + 1)]
      · nlinarith [sq_nonneg (t - 1)]

theorem cubic_loop_actual_graph_derivatives {t : ℝ} (ht : t ≠ 0) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ LeftInvOn g cubicLoopX (Ioo a b) ∧
      HasDerivAt (cubicLoopY ∘ g) ((3 * t ^ 2 - 3) / (2 * t)) (cubicLoopX t) ∧
      HasDerivAt (deriv (cubicLoopY ∘ g))
        (3 * (t ^ 2 + 1) / (4 * t ^ 3)) (cubicLoopX t) := by
  have hX : ContDiff ℝ 2 cubicLoopX := contDiff_id.pow 2
  have hY : ContDiff ℝ 2 cubicLoopY := by
    exact (contDiff_id.pow 3).sub ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ (3 : ℝ))).mul contDiff_id)
  have hn : deriv cubicLoopX t ≠ 0 := by
    rw [cubic_loop_derivative_functions.1]
    exact mul_ne_zero (by norm_num) ht
  obtain ⟨a, b, g, ha, hg, hd1, hd2⟩ := exists_local_parametric_derivatives hX hY t hn
  refine ⟨a, b, g, ha, hg, hd1.congr_deriv ?_, hd2.congr_deriv ?_⟩
  · rw [cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
  · rw [(cubic_loop_actual_second_derivatives t).1.deriv,
      (cubic_loop_actual_second_derivatives t).2.deriv,
      cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
    field_simp [ht]
    ring


theorem cubic_loop_signed_curvature_numerator (t : ℝ) :
    deriv cubicLoopX t * deriv (deriv cubicLoopY) t -
      deriv (deriv cubicLoopX) t * deriv cubicLoopY t = 6 * (t ^ 2 + 1) ∧
      0 < 6 * (t ^ 2 + 1) := by
  rw [(cubic_loop_actual_second_derivatives t).1.deriv,
    (cubic_loop_actual_second_derivatives t).2.deriv,
    cubic_loop_derivative_functions.1, cubic_loop_derivative_functions.2]
  exact ⟨by ring, by nlinarith [sq_nonneg t]⟩

theorem cubic_loop_closed_loop_location {t : ℝ}
    (ht : t ∈ Icc (-Real.sqrt 3) (Real.sqrt 3)) :
    0 ≤ cubicLoopX t ∧ cubicLoopX t ≤ 3 ∧
      (t ≤ 0 → 0 ≤ cubicLoopY t) ∧ (0 ≤ t → cubicLoopY t ≤ 0) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hb : t ^ 2 ≤ 3 := by
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + Real.sqrt 3)
      (by linarith [ht.2] : 0 ≤ Real.sqrt 3 - t)]
  refine ⟨sq_nonneg t, hb, ?_, ?_⟩
  · intro hn
    have hp := mul_nonneg_of_nonpos_of_nonpos hn (by linarith : t ^ 2 - 3 ≤ 0)
    change 0 ≤ t ^ 3 - 3 * t
    nlinarith
  · intro hp
    have hn := mul_nonpos_of_nonneg_of_nonpos hp (by linarith : t ^ 2 - 3 ≤ 0)
    change t ^ 3 - 3 * t ≤ 0
    nlinarith

theorem cubic_loop_monotonic_branches :
    StrictAntiOn cubicLoopX (Iio (0 : ℝ)) ∧ StrictMonoOn cubicLoopX (Ioi (0 : ℝ)) ∧
      StrictMonoOn cubicLoopY (Iio (-1 : ℝ)) ∧
      StrictAntiOn cubicLoopY (Ioo (-1 : ℝ) 1) ∧ StrictMonoOn cubicLoopY (Ioi (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg (convex_Iio (0 : ℝ)) cubic_loop_continuous_coordinates.1.continuousOn
    intro t ht
    exact (cubic_loop_full_coordinate_variation t).1.mpr
      (show t ∈ Iio (0 : ℝ) from interior_subset ht)
  · apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) cubic_loop_continuous_coordinates.1.continuousOn
    intro t ht
    exact (cubic_loop_full_coordinate_variation t).2.2.1.mpr (interior_subset ht)
  · apply strictMonoOn_of_deriv_pos (convex_Iio (-1 : ℝ)) cubic_loop_continuous_coordinates.2.continuousOn
    intro t ht
    exact (cubic_loop_full_coordinate_variation t).2.2.2.2.2.mpr
      (Or.inl (show t ∈ Iio (-1 : ℝ) from interior_subset ht))
  · apply strictAntiOn_of_deriv_neg (convex_Ioo (-1 : ℝ) 1) cubic_loop_continuous_coordinates.2.continuousOn
    intro t ht
    exact (cubic_loop_full_coordinate_variation t).2.2.2.1.mpr
      (show t ∈ Ioo (-1 : ℝ) 1 from interior_subset ht)
  · apply strictMonoOn_of_deriv_pos (convex_Ioi (1 : ℝ)) cubic_loop_continuous_coordinates.2.continuousOn
    intro t ht
    exact (cubic_loop_full_coordinate_variation t).2.2.2.2.2.mpr (Or.inr (interior_subset ht))

theorem cubic_loop_open_loop_injective :
    InjOn (parametricPoint cubicLoopX cubicLoopY) (Ioo (-Real.sqrt 3) (Real.sqrt 3)) := by
  intro s hs t ht hp
  by_contra hst
  have hc := (cubic_loop_distinct_parameter_intersection_iff s t).mp ⟨hst, hp⟩
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hm := mul_pos (by linarith [ht.1] : 0 < t + Real.sqrt 3)
    (by linarith [ht.2] : 0 < Real.sqrt 3 - t)
  nlinarith [hc.2.2]

theorem cubic_loop_outer_branches {t : ℝ} :
    (t < -Real.sqrt 3 → 3 < cubicLoopX t ∧ cubicLoopY t < 0) ∧
      (Real.sqrt 3 < t → 3 < cubicLoopX t ∧ 0 < cubicLoopY t) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)
  constructor
  · intro ht
    have hm := mul_pos (by linarith : 0 < -t - Real.sqrt 3)
      (by linarith : 0 < -t + Real.sqrt 3)
    have hsq : 3 < t ^ 2 := by nlinarith
    refine ⟨hsq, ?_⟩
    have hneg := mul_neg_of_neg_of_pos (by linarith : t < 0) (by linarith : 0 < t ^ 2 - 3)
    change t ^ 3 - 3 * t < 0
    nlinarith
  · intro ht
    have hm := mul_pos (by linarith : 0 < t - Real.sqrt 3)
      (by linarith : 0 < t + Real.sqrt 3)
    have hsq : 3 < t ^ 2 := by nlinarith
    refine ⟨hsq, ?_⟩
    have hpos := mul_pos (by linarith : 0 < t) (by linarith : 0 < t ^ 2 - 3)
    change 0 < t ^ 3 - 3 * t
    nlinarith

theorem cubic_loop_affine_residual_at_top (m b : ℝ) :
    Tendsto (fun t : ℝ ↦ cubicLoopY t - (m * cubicLoopX t + b)) atTop atTop := by
  have hi : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnorm : Tendsto (fun t : ℝ ↦
      (cubicLoopY t - (m * cubicLoopX t + b)) / t ^ 3) atTop (𝓝 1) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul m)).sub ((hi.pow 2).const_mul 3)).sub
      ((hi.pow 3).const_mul b)
    have hh : Tendsto (fun t : ℝ ↦ 1 - m * t⁻¹ - 3 * (t⁻¹) ^ 2 - b * (t⁻¹) ^ 3)
        atTop (𝓝 1) := by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, sub_zero] using! h
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold cubicLoopX cubicLoopY
    field_simp [ht.ne']
    ring
  have h := hnorm.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact div_mul_cancel₀ _ (pow_ne_zero 3 ht.ne')

theorem cubic_loop_affine_residual_at_bot (m b : ℝ) :
    Tendsto (fun t : ℝ ↦ cubicLoopY t - (m * cubicLoopX t + b)) atBot atBot := by
  have h := tendsto_neg_atTop_atBot.comp
    ((cubic_loop_affine_residual_at_top (-m) (-b)).comp tendsto_neg_atBot_atTop)
  apply h.congr'
  filter_upwards with t
  simp only [Function.comp_def, cubicLoopX, cubicLoopY]
  ring

theorem cubic_loop_coordinate_infinite_ends :
    Tendsto cubicLoopX atTop atTop ∧ Tendsto cubicLoopX atBot atTop ∧
      Tendsto cubicLoopY atTop atTop ∧ Tendsto cubicLoopY atBot atBot := by
  have hX : Tendsto cubicLoopX atTop atTop := tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  have hXB : Tendsto cubicLoopX atBot atTop := by
    simpa only [Function.comp_def, cubicLoopX, neg_sq] using! hX.comp tendsto_neg_atBot_atTop
  refine ⟨hX, hXB, ?_, ?_⟩
  · simpa only [zero_mul, zero_add, sub_zero] using! cubic_loop_affine_residual_at_top 0 0
  · simpa only [zero_mul, zero_add, sub_zero] using! cubic_loop_affine_residual_at_bot 0 0

theorem cubic_loop_no_line_asymptote_at_infinite_ends (m b : ℝ) :
    Tendsto (cubicLoopLineDistance m b) atTop atTop ∧
      Tendsto (cubicLoopLineDistance m b) atBot atTop := by
  have hK : 0 < Real.sqrt (m ^ 2 + 1) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg m])
  have hA := cubic_loop_affine_residual_at_top m b
  have hB := cubic_loop_affine_residual_at_bot m b
  have ha : Tendsto (fun t : ℝ ↦ |cubicLoopY t - (m * cubicLoopX t + b)|) atTop atTop := by
    apply hA.congr'
    filter_upwards [hA.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    exact (abs_of_pos ht).symm
  have hb : Tendsto (fun t : ℝ ↦ |cubicLoopY t - (m * cubicLoopX t + b)|) atBot atTop := by
    have hn := tendsto_neg_atBot_atTop.comp hB
    apply hn.congr'
    filter_upwards [hB.eventually (eventually_lt_atBot (0 : ℝ))] with t ht
    simpa only [Function.comp_def] using (abs_of_neg ht).symm
  exact ⟨by simpa only [cubicLoopLineDistance, div_eq_mul_inv] using! ha.atTop_mul_const (inv_pos.2 hK),
    by simpa only [cubicLoopLineDistance, div_eq_mul_inv] using! hb.atTop_mul_const (inv_pos.2 hK)⟩

theorem cubic_loop_vertical_line_distance_infinite_ends (c : ℝ) :
    Tendsto (fun t : ℝ ↦ |cubicLoopX t - c|) atTop atTop ∧
      Tendsto (fun t : ℝ ↦ |cubicLoopX t - c|) atBot atTop := by
  have hD {L : Filter ℝ} (hx : Tendsto cubicLoopX L atTop) :
      Tendsto (fun t : ℝ ↦ |cubicLoopX t - c|) L atTop := by
    have hh : Tendsto (fun t : ℝ ↦ cubicLoopX t - c) L atTop := by
      refine tendsto_atTop.2 (fun b ↦ ?_)
      filter_upwards [hx.eventually (eventually_ge_atTop (b + c))] with t ht
      linarith
    apply hh.congr'
    filter_upwards [hh.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    exact (abs_of_pos ht).symm
  exact ⟨hD cubic_loop_coordinate_infinite_ends.1, hD cubic_loop_coordinate_infinite_ends.2.1⟩

/-- Bài 15(a): khảo sát đường cong `x = t²`, `y = t³ − 3t`. -/
theorem source_cubic_loop_parametric_curve_investigation :
    (cubicLoopCurve = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 ^ 2 = p.1 * (p.1 - 3) ^ 2}) ∧
    (∀ t : ℝ, HasDerivAt cubicLoopX (2 * t) t ∧ HasDerivAt cubicLoopY (3 * t ^ 2 - 3) t) ∧
    (∀ t : ℝ, deriv cubicLoopX t ≠ 0 ∨ deriv cubicLoopY t ≠ 0) ∧
    (∀ s t : ℝ, s ≠ t ∧ parametricPoint cubicLoopX cubicLoopY s = parametricPoint cubicLoopX cubicLoopY t ↔
      t ≠ 0 ∧ s = -t ∧ t ^ 2 = 3) ∧
    (∀ p : ℝ × ℝ, (p ∈ cubicLoopTangent 0 ↔ p.1 = 0) ∧
      (p ∈ cubicLoopTangent (-1) ↔ p.2 = 2) ∧ (p ∈ cubicLoopTangent 1 ↔ p.2 = -2) ∧
      (p ∈ cubicLoopTangent (Real.sqrt 3) ↔ p.2 = Real.sqrt 3 * (p.1 - 3)) ∧
      (p ∈ cubicLoopTangent (-Real.sqrt 3) ↔ p.2 = -Real.sqrt 3 * (p.1 - 3))) ∧
    (∀ t : ℝ, (deriv cubicLoopX t < 0 ↔ t < 0) ∧ (deriv cubicLoopX t = 0 ↔ t = 0) ∧
      (0 < deriv cubicLoopX t ↔ 0 < t) ∧ (deriv cubicLoopY t < 0 ↔ -1 < t ∧ t < 1) ∧
      (deriv cubicLoopY t = 0 ↔ t = -1 ∨ t = 1) ∧ (0 < deriv cubicLoopY t ↔ t < -1 ∨ 1 < t)) ∧
    (∀ t ∈ Icc (-Real.sqrt 3) (Real.sqrt 3), 0 ≤ cubicLoopX t ∧ cubicLoopX t ≤ 3 ∧
      (t ≤ 0 → 0 ≤ cubicLoopY t) ∧ (0 ≤ t → cubicLoopY t ≤ 0)) ∧
    (Tendsto cubicLoopX atTop atTop ∧ Tendsto cubicLoopX atBot atTop ∧
      Tendsto cubicLoopY atTop atTop ∧ Tendsto cubicLoopY atBot atBot) ∧
    (∀ m b : ℝ, Tendsto (cubicLoopLineDistance m b) atTop atTop ∧
      Tendsto (cubicLoopLineDistance m b) atBot atTop) := by
  exact ⟨cubic_loop_complete_image, cubic_loop_actual_first_derivatives,
    cubic_loop_regular_at_every_parameter, cubic_loop_distinct_parameter_intersection_iff,
    cubic_loop_special_tangents, cubic_loop_full_coordinate_variation,
    fun _ ht ↦ cubic_loop_closed_loop_location ht, cubic_loop_coordinate_infinite_ends,
    cubic_loop_no_line_asymptote_at_infinite_ends⟩

end calculus.Chapter04.Section04CubicLoopParametricCurveInvestigation
