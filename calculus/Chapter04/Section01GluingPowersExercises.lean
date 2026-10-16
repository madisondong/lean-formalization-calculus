import calculus.Chapter04.Section01GluingExercises
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Bài 13(e,h): ghép lũy thừa với hàm mũ tại 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 576–581,592–597.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01GluingPowersExercises
open calculus.Chapter04.Section01GluingExercises


def exponentialPolynomialJoin (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then Real.exp (-1 / x) else x ^ n

/-- Bài 13(h): nhánh `x^a exp(−x²)` liên tục bên phải tại 0 khi `a ≥ 1`. -/
def affineRealPowerJoinRepaired (a b x : ℝ) : ℝ :=
  if x < 0 then b * x else x ^ a * Real.exp (-x ^ 2)


theorem exponential_glue_hasDerivAt_zero : HasDerivAt expNegInvGlue 0 0 := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) 0


theorem exponentialPolynomialJoin_eq_splice (n : ℕ) :
    exponentialPolynomialJoin n = spliceZero (fun x : ℝ ↦ x ^ n) expNegInvGlue := by
  funext x
  by_cases hx : 0 < x
  · simp [exponentialPolynomialJoin, spliceZero, expNegInvGlue, hx, not_le.mpr hx,
      neg_div, one_div]
  · simp [exponentialPolynomialJoin, spliceZero, hx, le_of_not_gt hx]


theorem natural_power_hasDerivAt_zero (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (fun x : ℝ ↦ x ^ n) (if n = 1 then 1 else 0) 0 := by
  have h := hasDerivAt_pow n (0 : ℝ)
  by_cases he : n = 1
  · simpa [he] using h
  · have hs : n - 1 ≠ 0 := by omega
    simpa [he, zero_pow hs] using h

/-- Bài 13(e): hàm không khả vi khi `n = 1`; với `n ≥ 2`, đạo hàm tại 0 bằng 0. -/
theorem exponentialPolynomialJoin_differentiableAt_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (exponentialPolynomialJoin n) 0 ↔ n ≠ 1 := by
  rw [exponentialPolynomialJoin_eq_splice]
  have h := spliceZero_differentiableAt_iff (natural_power_hasDerivAt_zero n hn)
    exponential_glue_hasDerivAt_zero
  have hn0 : n ≠ 0 := by omega
  simpa [expNegInvGlue.zero, zero_pow hn0] using h


theorem exponentialPolynomialJoin_hasDerivAt_zero (n : ℕ) (hn : 1 ≤ n) (hne : n ≠ 1) :
    HasDerivAt (exponentialPolynomialJoin n) 0 0 := by
  rw [exponentialPolynomialJoin_eq_splice]
  apply spliceZero_hasDerivAt
  · simpa [hne] using natural_power_hasDerivAt_zero n hn
  · exact exponential_glue_hasDerivAt_zero
  · simp [zero_pow (show n ≠ 0 by omega), expNegInvGlue.zero]


theorem real_power_exponential_hasDerivAt_zero (a : ℝ) (ha : 1 ≤ a) :
    HasDerivAt (fun x : ℝ ↦ x ^ a * Real.exp (-x ^ 2))
      (if a = 1 then 1 else 0) 0 := by
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (-x ^ 2)) 0 0 := by
    have h := (Real.hasDerivAt_exp (-(0 : ℝ) ^ 2)).comp 0
      (hasDerivAt_pow 2 (0 : ℝ)).neg
    apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
    norm_num
  by_cases ha1 : a = 1
  · subst a
    have h : HasDerivAt (fun x : ℝ ↦ x * Real.exp (-x ^ 2)) 1 0 := by
      apply (((hasDerivAt_id (0 : ℝ)).mul he).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
      norm_num
    simpa using h
  · have hasub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hp := Real.hasDerivAt_rpow_const (x := (0 : ℝ)) (p := a) (Or.inr ha)
    have hp0 : HasDerivAt (fun x : ℝ ↦ x ^ a) 0 0 := by
      simpa only [Real.zero_rpow hasub, mul_zero] using hp
    have h : HasDerivAt (fun x : ℝ ↦ x ^ a * Real.exp (-x ^ 2)) 0 0 := by
      apply ((hp0.mul he).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
      simp
    simpa only [if_neg ha1] using h


theorem real_power_exponential_zero (a : ℝ) (ha : 1 ≤ a) :
    (0 : ℝ) ^ a * Real.exp (-(0 : ℝ) ^ 2) = 0 := by
  rw [Real.zero_rpow (show a ≠ 0 by linarith), zero_mul]


theorem affineRealPowerJoinRepaired_eq_splice (a b : ℝ) (ha : 1 ≤ a) :
    affineRealPowerJoinRepaired a b =
      spliceZero (fun x : ℝ ↦ b * x) (fun x ↦ x ^ a * Real.exp (-x ^ 2)) := by
  funext x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [affineRealPowerJoinRepaired, spliceZero, hx, hx.le]
  · subst x
    simp [affineRealPowerJoinRepaired, spliceZero,
      Real.zero_rpow (show a ≠ 0 by linarith)]
  · simp [affineRealPowerJoinRepaired, spliceZero, not_lt.mpr hx.le, not_le.mpr hx]

/-- Bài 13(h): với `a ≥ 1`, khả vi tại 0 khi và chỉ khi `b = 1` nếu `a = 1`, `b = 0` nếu `a > 1`. -/
theorem affineRealPowerJoinRepaired_differentiableAt_zero_iff (a b : ℝ) (ha : 1 ≤ a) :
    DifferentiableAt ℝ (affineRealPowerJoinRepaired a b) 0 ↔ b = if a = 1 then 1 else 0 := by
  rw [affineRealPowerJoinRepaired_eq_splice a b ha]
  have h := spliceZero_differentiableAt_iff
    (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul b)
    (real_power_exponential_hasDerivAt_zero a ha)
  simpa [Real.zero_rpow (show a ≠ 0 by linarith)] using h


theorem affineRealPowerJoinRepaired_hasDerivAt_zero (a b : ℝ) (ha : 1 ≤ a)
    (hb : b = if a = 1 then 1 else 0) : HasDerivAt (affineRealPowerJoinRepaired a b) b 0 := by
  rw [affineRealPowerJoinRepaired_eq_splice a b ha]
  apply spliceZero_hasDerivAt
  · simpa using (hasDerivAt_id (0 : ℝ)).const_mul b
  · simpa only [← hb] using real_power_exponential_hasDerivAt_zero a ha
  · simp [Real.zero_rpow (show a ≠ 0 by linarith)]


/-- Bài 13(h), số mũ nguyên: khả vi tại 0 khi và chỉ khi `b = 1` nếu `n = 1`, `b = 0` nếu `n > 1`. -/
theorem affineNaturalPowerJoin_differentiableAt_zero_iff (n : ℕ) (hn : 1 ≤ n) (b : ℝ) :
    DifferentiableAt ℝ (fun x : ℝ ↦ if x < 0 then b * x else x ^ n * Real.exp (-x ^ 2)) 0 ↔
      b = if n = 1 then 1 else 0 := by
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfun : affineRealPowerJoinRepaired (n : ℝ) b =
      fun x : ℝ ↦ if x < 0 then b * x else x ^ n * Real.exp (-x ^ 2) := by
    funext x
    simp [affineRealPowerJoinRepaired, Real.rpow_natCast]
  have h := affineRealPowerJoinRepaired_differentiableAt_zero_iff (n : ℝ) b hnr
  rw [hfun] at h
  simpa using h

end calculus.Chapter04.Section01GluingPowersExercises
