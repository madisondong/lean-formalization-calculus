import calculus.Chapter03.Section03Supplement
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bài 17–19,21: tối ưu hình học với nghiệm chính xác

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2807–2820, dòng 2875–2878. Các độ dài, bán kính và chiều cao đều dương; khoảng cách là khoảng cách Euclid.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04OptimizationExercises
open calculus.Chapter03.Section03Supplement


theorem sourceCubeRoot_pos {u : ℝ} (hu : 0 < u) : 0 < signedCubeRoot u := by
  have ho : Odd (3 : ℕ) := by decide
  apply ho.pow_lt_pow.mp
  simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), signedCubeRoot_cube] using hu

/-- Bài 17: diện tích lớn nhất và điều kiện đạt đẳng thức cho mọi hình chữ nhật thỏa ràng buộc. -/
theorem farmer_rectangular_area_bound (x y : ℝ) (_hx : 0 < x) (_hy : 0 < y)
    (hFence : 2 * x + y = 700) :
    x * y ≤ 61250 ∧ (x * y = 61250 ↔ x = 175 ∧ y = 350) := by
  have hid : 61250 - x * y = 2 * (x - 175) ^ 2 := by nlinarith [hFence]
  constructor
  · nlinarith [sq_nonneg (x - 175)]
  · constructor
    · intro harea
      have hz : (x - 175) ^ 2 = 0 := by nlinarith
      have hx : x = 175 := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      exact ⟨hx, by linarith⟩
    · rintro ⟨rfl, rfl⟩
      norm_num


theorem farmer_rectangular_solution :
    (0 : ℝ) < 175 ∧ (0 : ℝ) < 350 ∧ 2 * (175 : ℝ) + 350 = 700 ∧
      (175 : ℝ) * 350 = 61250 ∧
      ∀ x y : ℝ, 0 < x → 0 < y → 2 * x + y = 700 → x * y ≤ 61250 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro x y hx hy hf
  exact (farmer_rectangular_area_bound x y hx hy hf).1

/-- Bán kính tối ưu của lon mở nắp, đơn vị cm. -/
def optimalOpenCylinderRadius : ℝ := signedCubeRoot (800 / Real.pi)


theorem optimalOpenCylinderRadius_data :
    0 < optimalOpenCylinderRadius ∧ Real.pi * optimalOpenCylinderRadius ^ 3 = 800 := by
  constructor
  · exact sourceCubeRoot_pos (div_pos (by norm_num) Real.pi_pos)
  · rw [optimalOpenCylinderRadius, signedCubeRoot_cube]
    field_simp [Real.pi_ne_zero]

/-- Diện tích kim loại thực của lon mở nắp: một đáy và mặt bên. -/
def openCylinderArea (r h : ℝ) : ℝ := Real.pi * r ^ 2 + 2 * Real.pi * r * h


theorem openCylinderArea_difference (r h : ℝ) (hr : 0 < r)
    (hv : Real.pi * r ^ 2 * h = 800) :
    openCylinderArea r h - 3 * Real.pi * optimalOpenCylinderRadius ^ 2 =
      Real.pi / r * (r - optimalOpenCylinderRadius) ^ 2 *
        (r + 2 * optimalOpenCylinderRadius) := by
  have hr₀ := optimalOpenCylinderRadius_data.2
  have he : Real.pi * r ^ 2 * h = Real.pi * optimalOpenCylinderRadius ^ 3 := hv.trans hr₀.symm
  unfold openCylinderArea
  apply (mul_right_cancel₀ hr.ne')
  field_simp [hr.ne']
  have he' : r ^ 2 * h = optimalOpenCylinderRadius ^ 3 := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    simpa only [mul_assoc] using he
  nlinarith [he']

/-- Bài 18: giá trị nhỏ nhất duy nhất trên miền các kích thước dương, với `h₀ = r₀`. -/
theorem openCylinderArea_minimum (r h : ℝ) (hr : 0 < r) (_hh : 0 < h)
    (hv : Real.pi * r ^ 2 * h = 800) :
    3 * Real.pi * optimalOpenCylinderRadius ^ 2 ≤ openCylinderArea r h ∧
      (openCylinderArea r h = 3 * Real.pi * optimalOpenCylinderRadius ^ 2 ↔
        r = optimalOpenCylinderRadius ∧ h = optimalOpenCylinderRadius) := by
  have hr₀ := optimalOpenCylinderRadius_data.1
  have hcoef : 0 < Real.pi / r * (r + 2 * optimalOpenCylinderRadius) :=
    mul_pos (div_pos Real.pi_pos hr) (by linarith)
  have hdiff := openCylinderArea_difference r h hr hv
  have hprod : 0 ≤ Real.pi / r * (r - optimalOpenCylinderRadius) ^ 2 *
      (r + 2 * optimalOpenCylinderRadius) :=
    mul_nonneg (mul_nonneg (div_pos Real.pi_pos hr).le (sq_nonneg _)) (by linarith)
  constructor
  · linarith
  · constructor
    · intro he
      have hzero : (Real.pi / r * (r + 2 * optimalOpenCylinderRadius)) *
          (r - optimalOpenCylinderRadius) ^ 2 = 0 := by nlinarith [hdiff]
      have hs : (r - optimalOpenCylinderRadius) ^ 2 = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hcoef.ne'
      have hrEq : r = optimalOpenCylinderRadius := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
      refine ⟨hrEq, ?_⟩
      rw [hrEq] at hv
      have hid : Real.pi * optimalOpenCylinderRadius ^ 2 *
          optimalOpenCylinderRadius = 800 := by
        simpa only [pow_succ, mul_assoc] using optimalOpenCylinderRadius_data.2
      have hne : Real.pi * optimalOpenCylinderRadius ^ 2 ≠ 0 := by positivity
      exact (mul_left_cancel₀ hne) (hv.trans hid.symm)
    · rintro ⟨rfl, rfl⟩
      unfold openCylinderArea
      ring


theorem openCylinderArea_solution :
    0 < optimalOpenCylinderRadius ∧
      Real.pi * optimalOpenCylinderRadius ^ 2 * optimalOpenCylinderRadius = 800 ∧
      openCylinderArea optimalOpenCylinderRadius optimalOpenCylinderRadius =
        3 * Real.pi * optimalOpenCylinderRadius ^ 2 := by
  refine ⟨optimalOpenCylinderRadius_data.1, ?_, ?_⟩
  · simpa only [pow_succ, mul_assoc] using optimalOpenCylinderRadius_data.2
  · unfold openCylinderArea
    ring

/-- Bài 19: điểm gần nhất có tung độ `∛24`. -/
def closestParabolaY : ℝ := signedCubeRoot 24


def closestParabolaX : ℝ := closestParabolaY ^ 2 / 4


def parabolaSquaredDistance (x y : ℝ) : ℝ := (x - 2) ^ 2 + (y - 3) ^ 2


def parabolaDistance (x y : ℝ) : ℝ := Real.sqrt (parabolaSquaredDistance x y)

theorem closestParabolaY_data : 0 < closestParabolaY ∧ closestParabolaY ^ 3 = 24 :=
  ⟨sourceCubeRoot_pos (by norm_num), signedCubeRoot_cube 24⟩


theorem parabolaSquaredDistance_difference (x y : ℝ) (hp : y ^ 2 = 4 * x) :
    parabolaSquaredDistance x y - parabolaSquaredDistance closestParabolaX closestParabolaY =
      (y - closestParabolaY) ^ 2 *
        ((y + closestParabolaY) ^ 2 + 2 * closestParabolaY ^ 2) / 16 := by
  have hx : x = y ^ 2 / 4 := by linarith
  have ht := closestParabolaY_data.2
  rw [hx]
  unfold parabolaSquaredDistance closestParabolaX
  have hmul := congrArg (fun z : ℝ ↦ (y - closestParabolaY) * z) ht
  nlinarith [hmul]

/-- Bài 19: bình phương khoảng cách đạt giá trị nhỏ nhất duy nhất. -/
theorem parabolaSquaredDistance_minimum (x y : ℝ) (hp : y ^ 2 = 4 * x) :
    parabolaSquaredDistance closestParabolaX closestParabolaY ≤ parabolaSquaredDistance x y ∧
      (parabolaSquaredDistance x y = parabolaSquaredDistance closestParabolaX closestParabolaY ↔
        x = closestParabolaX ∧ y = closestParabolaY) := by
  have hcoef : 0 < (y + closestParabolaY) ^ 2 + 2 * closestParabolaY ^ 2 := by
    have ht : 0 < closestParabolaY ^ 2 := sq_pos_of_pos closestParabolaY_data.1
    nlinarith [sq_nonneg (y + closestParabolaY)]
  have hid := parabolaSquaredDistance_difference x y hp
  have hprod : 0 ≤ (y - closestParabolaY) ^ 2 *
      ((y + closestParabolaY) ^ 2 + 2 * closestParabolaY ^ 2) / 16 := by positivity
  constructor
  · linarith
  · constructor
    · intro he
      have hm : (y - closestParabolaY) ^ 2 *
          ((y + closestParabolaY) ^ 2 + 2 * closestParabolaY ^ 2) = 0 := by linarith
      have hz : (y - closestParabolaY) ^ 2 = 0 :=
        (mul_eq_zero.mp hm).resolve_right hcoef.ne'
      have hy : y = closestParabolaY := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      exact ⟨by unfold closestParabolaX; rw [hy] at hp; linarith, hy⟩
    · rintro ⟨rfl, rfl⟩
      rfl


theorem parabolaDistance_minimum (x y : ℝ) (hp : y ^ 2 = 4 * x) :
    parabolaDistance closestParabolaX closestParabolaY ≤ parabolaDistance x y ∧
      (parabolaDistance x y = parabolaDistance closestParabolaX closestParabolaY ↔
        x = closestParabolaX ∧ y = closestParabolaY) := by
  have hc := parabolaSquaredDistance_minimum x y hp
  constructor
  · exact Real.sqrt_le_sqrt hc.1
  · rw [parabolaDistance, parabolaDistance,
      Real.sqrt_inj (by unfold parabolaSquaredDistance; positivity)
        (by unfold parabolaSquaredDistance; positivity)]
    exact hc.2


theorem closestParabola_solution : closestParabolaY ^ 2 = 4 * closestParabolaX ∧
    ∀ x y : ℝ, y ^ 2 = 4 * x →
      parabolaDistance closestParabolaX closestParabolaY ≤ parabolaDistance x y := by
  refine ⟨by unfold closestParabolaX; ring, ?_⟩
  intro x y hp
  exact (parabolaDistance_minimum x y hp).1

/-- Bài 21: diện tích lớn nhất từ điều kiện đường tròn và `(x−y)² ≥ 0`. -/
theorem semicircle_rectangle_area_bound (r x y : ℝ) (_hr : 0 < r) (_hx : 0 < x)
    (_hy : 0 < y) (hc : x ^ 2 + y ^ 2 = r ^ 2) :
    2 * x * y ≤ r ^ 2 ∧ (2 * x * y = r ^ 2 ↔ x = y) := by
  constructor
  · nlinarith [sq_nonneg (x - y)]
  · constructor
    · intro he
      have hz : (x - y) ^ 2 = 0 := by nlinarith [hc]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro he
      nlinarith [hc]


theorem semicircle_rectangle_solution (r : ℝ) (hr : 0 < r) :
    0 < Real.sqrt (r ^ 2 / 2) ∧
      (Real.sqrt (r ^ 2 / 2)) ^ 2 + (Real.sqrt (r ^ 2 / 2)) ^ 2 = r ^ 2 ∧
      2 * Real.sqrt (r ^ 2 / 2) * Real.sqrt (r ^ 2 / 2) = r ^ 2 ∧
      ∀ x y : ℝ, 0 < x → 0 < y → x ^ 2 + y ^ 2 = r ^ 2 → 2 * x * y ≤ r ^ 2 := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have he : (Real.sqrt (r ^ 2 / 2)) ^ 2 = r ^ 2 / 2 := Real.sq_sqrt hs.le
  refine ⟨Real.sqrt_pos.mpr hs, by linarith, by nlinarith, ?_⟩
  intro x y hx hy hc
  exact (semicircle_rectangle_area_bound r x y hr hx hy hc).1

end calculus.Chapter04.Section04OptimizationExercises
