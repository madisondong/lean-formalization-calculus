import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 22–24: chi phí, đơn vị tiền và mô hình cầu bậc nhất

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2881–2922. Bài 23 đổi chi phí từ nghìn đồng sang đồng bằng hệ số 1000. Bài 24 giả định hàm cầu bậc nhất.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04EconomicExercises

/-- Tổng chi phí Bài 22, đơn vị nghìn đồng. -/
def productionCost (x : ℝ) : ℝ := 3000 + (9 / 5) * x + (3 / 2500) * x ^ 2

/-- Chi phí trung bình trong Bài 22, xét trên `x > 0`. -/
def averageProductionCost (x : ℝ) : ℝ := productionCost x / x


theorem productionCost_hasDerivAt (x : ℝ) :
    HasDerivAt productionCost (9 / 5 + (3 / 1250) * x) x := by
  have h : HasDerivAt productionCost
      (0 + (9 / 5) * 1 + (3 / 2500) * ((2 : ℝ) * x ^ (2 - 1) * 1)) x := by
    apply HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.add
        (HasDerivAt.add (hasDerivAt_const x (3000 : ℝ))
          (HasDerivAt.const_mul (9 / 5 : ℝ) (hasDerivAt_id x)))
        (HasDerivAt.const_mul (3 / 2500 : ℝ)
          (HasDerivAt.pow (hasDerivAt_id x) 2)))
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  apply HasDerivAt.congr_deriv h
  norm_num only [Nat.reduceSub, pow_one, mul_one, zero_add]
  ring

/-- Bài 22(a): giá trị chi phí tổng, trung bình và cận biên tại ba mức sản lượng. -/
theorem productionCost_source_table :
    (productionCost 1200 = 6888 ∧ averageProductionCost 1200 = 287 / 50 ∧
      deriv productionCost 1200 = 117 / 25) ∧
    (productionCost 2000 = 11400 ∧ averageProductionCost 2000 = 57 / 10 ∧
      deriv productionCost 2000 = 33 / 5) ∧
    (productionCost 3200 = 21048 ∧ averageProductionCost 3200 = 2631 / 400 ∧
      deriv productionCost 3200 = 237 / 25) := by
  simp only [(productionCost_hasDerivAt _).deriv]
  norm_num [productionCost, averageProductionCost]


def optimalContinuousProduction : ℝ := 500 * Real.sqrt 10

theorem optimalContinuousProduction_data :
    0 < optimalContinuousProduction ∧ optimalContinuousProduction ^ 2 = 2500000 := by
  have hs : (Real.sqrt (10 : ℝ)) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  constructor
  · unfold optimalContinuousProduction
    positivity
  · unfold optimalContinuousProduction
    nlinarith [hs]


theorem averageProductionCost_minimum (x : ℝ) (hx : 0 < x) :
    (9 + 6 * Real.sqrt 10) / 5 ≤ averageProductionCost x ∧
      (averageProductionCost x = (9 + 6 * Real.sqrt 10) / 5 ↔
        x = optimalContinuousProduction) := by
  have hid : averageProductionCost x - (9 + 6 * Real.sqrt 10) / 5 =
      3 / (2500 * x) * (x - optimalContinuousProduction) ^ 2 := by
    unfold averageProductionCost productionCost optimalContinuousProduction
    field_simp [hx.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  have hcoef : 0 < (3 : ℝ) / (2500 * x) := by positivity
  have hn : 0 ≤ 3 / (2500 * x) * (x - optimalContinuousProduction) ^ 2 :=
    mul_nonneg hcoef.le (sq_nonneg _)
  constructor
  · linarith
  · constructor
    · intro he
      have hz : 3 / (2500 * x) * (x - optimalContinuousProduction) ^ 2 = 0 := by
        linarith [hid]
      have hs := (mul_eq_zero.mp hz).resolve_left hcoef.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro he
      rw [he] at hid
      have hz : averageProductionCost optimalContinuousProduction -
          (9 + 6 * Real.sqrt 10) / 5 = 0 := by simpa using hid
      rw [he]
      exact sub_eq_zero.mp hz


theorem averageProductionCost_integer_difference (x : ℝ) (hx : x ≠ 0) :
    averageProductionCost x - averageProductionCost 1581 =
      (x - 1581) * (1581 * x - 2500000) * 3 / (2500 * 1581 * x) := by
  unfold averageProductionCost productionCost
  field_simp [hx]
  ring

/-- Bài 22(b): sản lượng nguyên dương tối ưu duy nhất là 1581. -/
theorem averageProductionCost_positive_integer_minimum (n : ℕ) (hn : 0 < n) :
    averageProductionCost 1581 ≤ averageProductionCost n ∧
      (averageProductionCost n = averageProductionCost 1581 ↔ n = 1581) := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := averageProductionCost_integer_difference n hx.ne'
  by_cases he : n = 1581
  · subst n
    simp
  · have hstrict : 0 < averageProductionCost n - averageProductionCost 1581 := by
      have hprod : 0 < ((n : ℝ) - 1581) * (1581 * (n : ℝ) - 2500000) := by
        rcases lt_or_gt_of_ne he with hl | hg
        · have hle : n ≤ 1580 := by omega
          have hreal : (n : ℝ) ≤ 1580 := by exact_mod_cast hle
          exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
        · have hle : 1582 ≤ n := by omega
          have hreal : (1582 : ℝ) ≤ n := by exact_mod_cast hle
          exact mul_pos (by linarith) (by linarith)
      rw [hd]
      positivity
    refine ⟨by linarith, ?_⟩
    constructor
    · intro h
      linarith
    · exact fun h ↦ (he h).elim

/-- Bài 23: chi phí có đơn vị nghìn đồng. -/
def companyCostThousands (x : ℝ) : ℝ := 90 + (11 / 10) * x + (3 / 250) * x ^ 2 +
  (1 / 20000) * x ^ 3

/-- Bài 23: giá bán có đơn vị đồng. -/
def companyPrice (x : ℝ) : ℝ := 4200 - 12 * x

/-- Bài 23(a): doanh thu bằng sản lượng nhân giá bán, có đơn vị đồng. -/
def companyRevenue (x : ℝ) : ℝ := x * companyPrice x

theorem companyRevenue_formula (x : ℝ) : companyRevenue x = 4200 * x - 12 * x ^ 2 := by
  unfold companyRevenue companyPrice
  ring

/-- Bài 23(b): lợi nhuận bằng doanh thu trừ chi phí, cùng tính bằng đồng. -/
def correctedProfit (x : ℝ) : ℝ := companyRevenue x - 1000 * companyCostThousands x

theorem correctedProfit_formula (x : ℝ) :
    correctedProfit x = -90000 + 3100 * x - 24 * x ^ 2 - x ^ 3 / 20 := by
  unfold correctedProfit companyRevenue companyPrice companyCostThousands
  ring


theorem company_profit_unit_mismatch :
    companyRevenue 0 - companyCostThousands 0 ≠ correctedProfit 0 := by
  norm_num [companyRevenue, companyPrice, companyCostThousands, correctedProfit]


def correctedOptimalProduction : ℝ := (-480 + 20 * Real.sqrt 1041) / 3

theorem correctedOptimalProduction_data :
    0 < correctedOptimalProduction ∧
      3 * correctedOptimalProduction ^ 2 + 960 * correctedOptimalProduction = 62000 ∧
      55 < correctedOptimalProduction ∧ correctedOptimalProduction < 111 / 2 := by
  have hs : (Real.sqrt (1041 : ℝ)) ^ 2 = 1041 := Real.sq_sqrt (by norm_num)
  have hsn : 0 ≤ Real.sqrt (1041 : ℝ) := Real.sqrt_nonneg _
  have hup : 0 < correctedOptimalProduction := by
    unfold correctedOptimalProduction
    nlinarith [hs]
  have hroot : 3 * correctedOptimalProduction ^ 2 +
      960 * correctedOptimalProduction = 62000 := by
    unfold correctedOptimalProduction
    nlinarith [hs]
  refine ⟨hup, hroot, ?_, ?_⟩
  · by_contra h
    have hle : correctedOptimalProduction ≤ 55 := le_of_not_gt h
    have hm : 0 ≤ correctedOptimalProduction * (55 - correctedOptimalProduction) :=
      mul_nonneg hup.le (by linarith)
    nlinarith [hm]
  · by_contra h
    have hle : 111 / 2 ≤ correctedOptimalProduction := le_of_not_gt h
    have hm : 0 ≤ (correctedOptimalProduction - 111 / 2) *
        (correctedOptimalProduction + 111 / 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hm]


theorem correctedOptimalProduction_rounds_to_fiftyfive :
    |correctedOptimalProduction - 55| < 1 / 2 ∧
      ∀ n : ℕ, n ≠ 55 →
        |correctedOptimalProduction - 55| < |correctedOptimalProduction - n| := by
  have hu := correctedOptimalProduction_data
  have h55 : 0 < correctedOptimalProduction - 55 := by linarith [hu.2.2.1]
  constructor
  · rw [abs_of_pos h55]
    linarith [hu.2.2.2]
  · intro n hn
    rcases lt_or_gt_of_ne hn with hl | hg
    · have hle : n ≤ 54 := by omega
      have hreal : (n : ℝ) ≤ 54 := by exact_mod_cast hle
      rw [abs_of_pos h55, abs_of_pos (by linarith : 0 < correctedOptimalProduction - n)]
      linarith
    · have hle : 56 ≤ n := by omega
      have hreal : (56 : ℝ) ≤ n := by exact_mod_cast hle
      rw [abs_of_pos h55, abs_of_neg (by linarith [hu.2.2.2] : correctedOptimalProduction - n < 0)]
      linarith [hu.2.2.2]


theorem correctedProfit_maximum (x : ℝ) (hx : 0 ≤ x) :
    correctedProfit x ≤ correctedProfit correctedOptimalProduction ∧
      (correctedProfit x = correctedProfit correctedOptimalProduction ↔
        x = correctedOptimalProduction) := by
  have hu := correctedOptimalProduction_data
  have hid : correctedProfit correctedOptimalProduction - correctedProfit x =
      (x - correctedOptimalProduction) ^ 2 * (24 + (x + 2 * correctedOptimalProduction) / 20) := by
    rw [correctedProfit_formula, correctedProfit_formula]
    have hm := congrArg (fun z : ℝ ↦ (x - correctedOptimalProduction) * z) hu.2.1
    nlinarith [hm]
  have hc : 0 < 24 + (x + 2 * correctedOptimalProduction) / 20 := by linarith [hu.1]
  have hprod : 0 ≤ (x - correctedOptimalProduction) ^ 2 *
      (24 + (x + 2 * correctedOptimalProduction) / 20) := mul_nonneg (sq_nonneg _) hc.le
  constructor
  · linarith
  · constructor
    · intro he
      have hz : (x - correctedOptimalProduction) ^ 2 *
          (24 + (x + 2 * correctedOptimalProduction) / 20) = 0 := by linarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right hc.ne'))
    · intro he
      simp [he]

/-- Bài 23(c): sản lượng nguyên tối ưu duy nhất là 55, cũng là giá trị làm tròn của nghiệm thực. -/
theorem correctedProfit_natural_maximum (n : ℕ) :
    correctedProfit n ≤ correctedProfit 55 ∧
      (correctedProfit n = correctedProfit 55 ↔ n = 55) := by
  by_cases he : n = 55
  · subst n
    simp
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hid : correctedProfit 55 - correctedProfit n =
        ((n : ℝ) - 55) * ((n : ℝ) ^ 2 + 535 * (n : ℝ) - 32575) / 20 := by
      rw [correctedProfit_formula, correctedProfit_formula]
      ring
    have hstrict : 0 < correctedProfit 55 - correctedProfit n := by
      rw [hid]
      apply div_pos _ (by norm_num)
      rcases lt_or_gt_of_ne he with hl | hg
      · have hle : n ≤ 54 := by omega
        have hreal : (n : ℝ) ≤ 54 := by exact_mod_cast hle
        have hm : 0 ≤ (n : ℝ) * (54 - (n : ℝ)) := mul_nonneg hn (by linarith)
        exact mul_pos_of_neg_of_neg (by linarith) (by nlinarith [hm])
      · have hle : 56 ≤ n := by omega
        have hreal : (56 : ℝ) ≤ n := by exact_mod_cast hle
        exact mul_pos (by linarith) (by nlinarith [sq_nonneg ((n : ℝ) - 56)])
    refine ⟨by linarith, ?_⟩
    constructor
    · intro h
      linarith
    · exact fun h ↦ (he h).elim


theorem correctedProfit_optimizers_feasible :
    0 < correctedOptimalProduction ∧ 0 < companyPrice correctedOptimalProduction ∧
      (0 : ℝ) < 55 ∧ 0 < companyPrice 55 := by
  have hu := correctedOptimalProduction_data
  refine ⟨hu.1, ?_, by norm_num, ?_⟩
  · unfold companyPrice
    linarith [hu.2.2.2]
  · norm_num [companyPrice]

/-- Hàm cầu bậc nhất trong Bài 24, với giá có đơn vị đồng mỗi sản phẩm. -/
def promotionPrice (x : ℝ) : ℝ := 472000 - 400 * x


theorem promotion_affine_calibration_unique (m b : ℝ)
    (h0 : m * 180 + b = 400000) (h1 : m * 205 + b = 390000) :
    m = -400 ∧ b = 472000 := by constructor <;> linarith

theorem promotionPrice_source_calibration :
    promotionPrice 180 = 400000 ∧ promotionPrice 205 = 390000 ∧
      ∀ x : ℝ, promotionPrice (x + 25) = promotionPrice x - 10000 := by
  refine ⟨by norm_num [promotionPrice], by norm_num [promotionPrice], ?_⟩
  intro x
  unfold promotionPrice
  ring


def promotionRevenue (x : ℝ) : ℝ := x * promotionPrice x

theorem promotionRevenue_formula (x : ℝ) : promotionRevenue x = 472000 * x - 400 * x ^ 2 := by
  unfold promotionRevenue promotionPrice
  ring


theorem promotionRevenue_maximum (x : ℝ) :
    promotionRevenue x ≤ 139240000 ∧ (promotionRevenue x = 139240000 ↔ x = 590) := by
  have hid : 139240000 - promotionRevenue x = 400 * (x - 590) ^ 2 := by
    rw [promotionRevenue_formula]
    ring
  constructor
  · nlinarith [sq_nonneg (x - 590)]
  · constructor
    · intro he
      have hz : (x - 590) ^ 2 = 0 := by linarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · rintro rfl
      norm_num [promotionRevenue, promotionPrice]

/-- Bài 24(c), theo mô hình bậc nhất: giảm giá 164000, giá bán 236000, sản lượng 590. -/
theorem promotion_source_solution :
    promotionPrice 590 = 236000 ∧ (400000 : ℝ) - promotionPrice 590 = 164000 ∧
      (180 : ℝ) + 164000 / 400 = 590 ∧ promotionRevenue 590 = 139240000 ∧
      ∀ x : ℝ, 180 ≤ x → promotionPrice x ≥ 0 → promotionRevenue x ≤ promotionRevenue 590 := by
  refine ⟨by norm_num [promotionPrice], by norm_num [promotionPrice], by norm_num,
    by norm_num [promotionRevenue, promotionPrice], ?_⟩
  intro x _ _
  calc
    promotionRevenue x ≤ 139240000 := (promotionRevenue_maximum x).1
    _ = promotionRevenue 590 := by norm_num [promotionRevenue, promotionPrice]


theorem promotion_calibration_does_not_determine_arbitrary_function :
    let q : ℝ → ℝ := fun x ↦ promotionPrice x + (x - 180) * (x - 205)
    q 180 = 400000 ∧ q 205 = 390000 ∧ q 181 ≠ promotionPrice 181 := by
  norm_num [promotionPrice]

/-- Nhiễu tuần hoàn vẫn thỏa dữ kiện tăng sản lượng ứng với mỗi bước giảm giá 25. -/
def promotionAlternativeDemand (x : ℝ) : ℝ := promotionPrice x +
  Real.sin (2 * Real.pi * (x - 180) / 25)


theorem promotion_constant_step_does_not_force_affine :
    promotionAlternativeDemand 180 = 400000 ∧
      (∀ x : ℝ, promotionAlternativeDemand (x + 25) = promotionAlternativeDemand x - 10000) ∧
      promotionAlternativeDemand (180 + 25 / 4) ≠ promotionPrice (180 + 25 / 4) := by
  constructor
  · norm_num [promotionAlternativeDemand, promotionPrice]
  · constructor
    · intro x
      have harg : 2 * Real.pi * (x + 25 - 180) / 25 =
          2 * Real.pi * (x - 180) / 25 + 2 * Real.pi := by ring
      unfold promotionAlternativeDemand
      rw [harg, Real.sin_add_two_pi, promotionPrice_source_calibration.2.2]
      ring
    · have harg : 2 * Real.pi * ((180 : ℝ) + 25 / 4 - 180) / 25 = Real.pi / 2 := by ring
      simp only [promotionAlternativeDemand, harg, Real.sin_pi_div_two]
      linarith

end calculus.Chapter04.Section04EconomicExercises
