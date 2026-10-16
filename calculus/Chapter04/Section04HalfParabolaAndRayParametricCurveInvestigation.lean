import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# §4.4 Bài 15(c,e): hai quỹ tích theo công thức của sách

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2778, dòng 2780; chỉ dẫn khảo sát dòng 2773–2786. Phần (e) cho tia `y = x`, `x ≥ 0`, dù sách gọi là đường xoắn Archimedes.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04HalfParabolaAndRayParametricCurveInvestigation


theorem half_parabola_locus (x y : ℝ) :
    (∃ t : ℝ, 0 ≤ t ∧ t = x ∧ t ^ 2 = y) ↔ 0 ≤ x ∧ y = x ^ 2 := by
  constructor
  · rintro ⟨t, ht, rfl, hty⟩
    exact ⟨ht, hty.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl, rfl⟩


theorem half_parabola_actual_derivatives (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u) 1 t ∧
    HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t ∧
    HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
  have hd : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := by
    simpa using! (hasDerivAt_id t).fun_pow 2
  exact ⟨hasDerivAt_id t, hd, hd⟩


theorem half_parabola_strictMonoOn :
    StrictMonoOn (fun t : ℝ ↦ t ^ 2) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hp : 0 < y + x := by linarith
  have hm := mul_pos (sub_pos.mpr hxy) hp
  nlinarith


theorem half_parabola_strictConvexOn :
    StrictConvexOn ℝ (Ici 0) (fun x : ℝ ↦ x ^ 2) :=
  strictConvexOn_pow (by decide : 2 ≤ (2 : ℕ))


theorem half_parabola_above_any_line_atTop (m b : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ 2 - (m * x + b)) atTop atTop := by
  apply tendsto_atTop_mono' _ ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (max 1 (max (m + 2) (|b| + 1)))] with x hx
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hx
  have hxm : m + 2 < x := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hx)
  have hxb : |b| + 1 < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hx)
  have hp := mul_pos (by linarith : 0 < x) (by linarith : 0 < x - m - 2)
  change x ≤ x ^ 2 - (m * x + b)
  nlinarith [le_abs_self b]

/-- Bài 15(c): khảo sát nửa parabol `y = x²`, `x ≥ 0`. -/
theorem source_half_parabola_parametric_curve_investigation :
    (∀ x y : ℝ, (∃ t : ℝ, 0 ≤ t ∧ t = x ∧ t ^ 2 = y) ↔
      0 ≤ x ∧ y = x ^ 2) ∧
    (∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ u) 1 t ∧
      HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t ∧
      HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t) ∧
    StrictMonoOn (fun t : ℝ ↦ t ^ 2) (Ici 0) ∧
    StrictConvexOn ℝ (Ici 0) (fun x : ℝ ↦ x ^ 2) ∧
    ((0 : ℝ) ^ 2 = 0 ∧ HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 0) ∧
    Tendsto (fun t : ℝ ↦ t) atTop atTop ∧
    Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop ∧
    (∀ m b : ℝ, Tendsto (fun x : ℝ ↦ x ^ 2 - (m * x + b)) atTop atTop) := by
  refine ⟨half_parabola_locus, half_parabola_actual_derivatives,
    half_parabola_strictMonoOn, half_parabola_strictConvexOn, ?_,
    tendsto_id, tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0),
    half_parabola_above_any_line_atTop⟩
  simpa using (half_parabola_actual_derivatives 0).2.2


theorem printed_equal_coordinate_ray_locus (a : ℝ) (ha : 0 < a) (x y : ℝ) :
    (∃ t : ℝ, 0 ≤ t ∧ a * t = x ∧ a * t = y) ↔ 0 ≤ x ∧ y = x := by
  constructor
  · rintro ⟨t, ht, rfl, he⟩
    exact ⟨mul_nonneg ha.le ht, he.symm⟩
  · rintro ⟨hx, hy⟩
    have he : a * (x / a) = x := by field_simp [ha.ne']
    exact ⟨x / a, div_nonneg hx ha.le, he, he.trans hy.symm⟩

/-- Bài 15(e): công thức trong sách xác định tia `y = x`, `x ≥ 0`. -/
theorem source_printed_equal_coordinate_ray_parametric_curve_investigation (a : ℝ) (ha : 0 < a) :
    (∀ x y : ℝ, (∃ t : ℝ, 0 ≤ t ∧ a * t = x ∧ a * t = y) ↔
      0 ≤ x ∧ y = x) ∧
    (∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ a * u) a t ∧
      HasDerivAt (fun u : ℝ ↦ u) 1 (a * t)) ∧
    StrictMono (fun t : ℝ ↦ a * t) ∧
    ((a * (0 : ℝ), a * 0) = (0, 0)) ∧
    Tendsto (fun t : ℝ ↦ a * t) atTop atTop ∧
    (∀ t : ℝ, a * t - a * t = 0 ∧ a / a = 1) := by
  refine ⟨printed_equal_coordinate_ray_locus a ha, ?_, ?_, by simp,
    tendsto_id.const_mul_atTop ha, ?_⟩
  · intro t
    exact ⟨by simpa using (hasDerivAt_id t).const_mul a, hasDerivAt_id (a * t)⟩
  · intro x y hxy
    exact mul_lt_mul_of_pos_left hxy ha
  · intro t
    exact ⟨sub_self _, div_self ha.ne'⟩

end calculus.Chapter04.Section04HalfParabolaAndRayParametricCurveInvestigation
