import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 20: chọn điểm cập bến để thời gian qua sông nhỏ nhất

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2822–2825; hình tại dòng 2840–2852. Xét khoảng cách cập bến `x ≥ 0`; quãng đường chạy là `|7−x|`, kể cả khi cập bến quá đích.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04RiverOptimization

/-- Thời gian có đơn vị giờ, với quãng đường chèo và chạy. -/
def riverTravelTime (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 25 / 4) / 5 + |7 - x| / 9


def optimalRiverLanding : ℝ := 25 / (4 * Real.sqrt 14)


theorem optimalRiverLanding_data :
    0 < optimalRiverLanding ∧ optimalRiverLanding < 7 ∧
      4 * Real.sqrt 14 * optimalRiverLanding = 25 := by
  have hr : 0 < Real.sqrt (14 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr1 : 1 < Real.sqrt (14 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)]
  refine ⟨by unfold optimalRiverLanding; positivity, ?_, ?_⟩
  · unfold optimalRiverLanding
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sqrt 14)).mpr
    linarith
  · unfold optimalRiverLanding
    field_simp [hr.ne']


theorem river_distance_square_identity (x : ℝ) :
    (9 * Real.sqrt (x ^ 2 + 25 / 4)) ^ 2 - (5 * x + 5 * Real.sqrt 14) ^ 2 =
      (2 * Real.sqrt 14 * x - 25 / 2) ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 25 / 4 by positivity)
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hm := congrArg (fun z : ℝ ↦ x ^ 2 * z) hr
  nlinarith [hm]


theorem river_distance_lower_bound (x : ℝ) :
    5 * x + 5 * Real.sqrt 14 ≤ 9 * Real.sqrt (x ^ 2 + 25 / 4) ∧
      (9 * Real.sqrt (x ^ 2 + 25 / 4) = 5 * x + 5 * Real.sqrt 14 ↔
        x = optimalRiverLanding) := by
  have hs : 0 ≤ Real.sqrt (x ^ 2 + 25 / 4) := Real.sqrt_nonneg _
  have hr : 0 < Real.sqrt (14 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hid := river_distance_square_identity x
  constructor
  · by_contra h
    have hlt : 9 * Real.sqrt (x ^ 2 + 25 / 4) < 5 * x + 5 * Real.sqrt 14 :=
      lt_of_not_ge h
    have hprod : 0 <
        (5 * x + 5 * Real.sqrt 14 - 9 * Real.sqrt (x ^ 2 + 25 / 4)) *
        (5 * x + 5 * Real.sqrt 14 + 9 * Real.sqrt (x ^ 2 + 25 / 4)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (2 * Real.sqrt 14 * x - 25 / 2)]
  · constructor
    · intro he
      have hz : (2 * Real.sqrt 14 * x - 25 / 2) ^ 2 = 0 := by
        rw [he] at hid
        nlinarith
      have heq : 2 * Real.sqrt 14 * x = 25 / 2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      unfold optimalRiverLanding
      apply (eq_div_iff (by positivity : 4 * Real.sqrt (14 : ℝ) ≠ 0)).mpr
      nlinarith
    · intro he
      subst x
      have hu := optimalRiverLanding_data
      have hz : 2 * Real.sqrt 14 * optimalRiverLanding - 25 / 2 = 0 := by linarith [hu.2.2]
      rw [hz] at hid
      nlinarith [hu.1]


theorem riverTravelTime_fullshore_minimum (x : ℝ) :
    (7 + Real.sqrt 14) / 9 ≤ riverTravelTime x ∧
      (riverTravelTime x = (7 + Real.sqrt 14) / 9 ↔ x = optimalRiverLanding) := by
  have hb := river_distance_lower_bound x
  have ha : 7 - x ≤ |7 - x| := le_abs_self _
  constructor
  · unfold riverTravelTime
    linarith [hb.1]
  · constructor
    · intro he
      have hd : 9 * Real.sqrt (x ^ 2 + 25 / 4) = 5 * x + 5 * Real.sqrt 14 := by
        unfold riverTravelTime at he
        linarith [hb.1]
      exact hb.2.mp hd
    · intro he
      subst x
      have hu := optimalRiverLanding_data
      have hb := (river_distance_lower_bound optimalRiverLanding).2.mpr rfl
      unfold riverTravelTime
      rw [abs_of_pos (by linarith [hu.2.1] : 0 < 7 - optimalRiverLanding)]
      linarith

/-- Bài 20: nghiệm tối ưu duy nhất trên `x ≥ 0` thuộc `(0,7)`. -/
theorem riverTravelTime_source_minimum (x : ℝ) (_hx : 0 ≤ x) :
    (7 + Real.sqrt 14) / 9 ≤ riverTravelTime x ∧
      (riverTravelTime x = (7 + Real.sqrt 14) / 9 ↔ x = optimalRiverLanding) :=
  riverTravelTime_fullshore_minimum x

/-- Bài 20: khoảng cách cập bến tối ưu và thời gian nhỏ nhất. -/
theorem riverTravelTime_source_solution :
    0 < optimalRiverLanding ∧ optimalRiverLanding < 7 ∧
      riverTravelTime optimalRiverLanding = (7 + Real.sqrt 14) / 9 ∧
      ∀ x : ℝ, 0 ≤ x → riverTravelTime optimalRiverLanding ≤ riverTravelTime x := by
  have hu := optimalRiverLanding_data
  have ht := (riverTravelTime_fullshore_minimum optimalRiverLanding).2.mpr rfl
  refine ⟨hu.1, hu.2.1, ht, ?_⟩
  intro x hx
  rw [ht]
  exact (riverTravelTime_source_minimum x hx).1

end calculus.Chapter04.Section04RiverOptimization
