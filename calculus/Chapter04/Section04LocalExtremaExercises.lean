import calculus.Chapter04.Section03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bài tập 4.4.10: cực trị tại hai điểm đã cho

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2721–2722.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04LocalExtremaExercises
open Set calculus.Chapter04.Section03


def cubicSine (x : ℝ) : ℝ := x ^ 3 * Real.sin x


def oneSubIdentityLog (x : ℝ) : ℝ := (1 - x) * Real.log x

theorem cubicSine_zero : cubicSine 0 = 0 := by simp [cubicSine]

theorem oneSubIdentityLog_one : oneSubIdentityLog 1 = 0 := by simp [oneSubIdentityLog]


theorem cubicSine_hasDerivAt (x : ℝ) :
    HasDerivAt cubicSine (3 * x ^ 2 * Real.sin x + x ^ 3 * Real.cos x) x := by
  change HasDerivAt (fun y : ℝ ↦ y ^ 3 * Real.sin y)
    (3 * x ^ 2 * Real.sin x + x ^ 3 * Real.cos x) x
  simpa only [Nat.cast_ofNat, Nat.reduceSub, mul_one, id_eq] using
    ((hasDerivAt_id x).fun_pow 3).fun_mul (Real.hasDerivAt_sin x)


theorem oneSubIdentityLog_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt oneSubIdentityLog (-Real.log x + (1 - x) / x) x := by
  change HasDerivAt (fun y : ℝ ↦ (1 - y) * Real.log y)
    (-Real.log x + (1 - x) / x) x
  simpa only [neg_mul, one_mul, div_eq_mul_inv, id_eq] using
    ((hasDerivAt_id x).const_sub 1).fun_mul (Real.hasDerivAt_log hx.ne')

theorem cubicSine_deriv_zero : deriv cubicSine 0 = 0 := by
  simpa using (cubicSine_hasDerivAt 0).deriv

theorem oneSubIdentityLog_deriv_one : deriv oneSubIdentityLog 1 = 0 := by
  simpa using (oneSubIdentityLog_hasDerivAt (by norm_num : (0 : ℝ) < 1)).deriv


theorem cubicSine_pos_near_zero {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi)
    (hne : x ≠ 0) : 0 < cubicSine x := by
  unfold cubicSine
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hcube : x ^ 3 < 0 := by
      rw [pow_succ]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hne) hneg
    exact mul_pos_of_neg_of_neg hcube
      (Real.sin_neg_of_neg_of_neg_pi_lt hneg hx.1)
  · exact mul_pos (pow_pos hpos 3) (Real.sin_pos_of_pos_of_lt_pi hpos hx.2)


theorem cubicSine_source_local_minimum : IsLocalMinimumOn cubicSine univ 0 := by
  refine ⟨by simp, Real.pi, Real.pi_pos, ?_⟩
  rintro x ⟨hx, _⟩
  rw [cubicSine_zero]
  by_cases hz : x = 0
  · subst x
    simp only [cubicSine_zero, le_refl]
  · exact (cubicSine_pos_near_zero (by simpa using hx) hz).le


theorem cubicSine_not_source_local_maximum : ¬ IsLocalMaximumOn cubicSine univ 0 := by
  rintro ⟨_, δ, hδ, hbound⟩
  let x : ℝ := min (δ / 2) (Real.pi / 2)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxδ : x < δ := (min_le_left _ _).trans_lt (by linarith)
  have hxpi : x < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hpos := cubicSine_pos_near_zero
    (show x ∈ Ioo (-Real.pi) Real.pi from ⟨by linarith [Real.pi_pos], hxpi⟩) hxpos.ne'
  have hb : cubicSine x ≤ cubicSine 0 :=
    hbound x ⟨⟨by linarith, by linarith⟩, by simp⟩
  rw [cubicSine_zero] at hb
  exact hpos.not_ge hb


theorem oneSubIdentityLog_neg_of_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    oneSubIdentityLog x < 0 := by
  unfold oneSubIdentityLog
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (Real.log_neg hx hlt)
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr hgt) (Real.log_pos hgt)


theorem oneSubIdentityLog_nonpos {x : ℝ} (hx : 0 < x) : oneSubIdentityLog x ≤ 0 := by
  by_cases hne : x = 1
  · subst x
    simp only [oneSubIdentityLog_one, le_refl]
  · exact (oneSubIdentityLog_neg_of_ne_one hx hne).le


theorem oneSubIdentityLog_source_local_maximum :
    IsLocalMaximumOn oneSubIdentityLog (Ioi 0) 1 := by
  refine ⟨by norm_num, (1 : ℝ) / 2, by norm_num, ?_⟩
  rintro x ⟨_, hx⟩
  rw [oneSubIdentityLog_one]
  exact oneSubIdentityLog_nonpos hx


theorem oneSubIdentityLog_not_source_local_minimum :
    ¬ IsLocalMinimumOn oneSubIdentityLog (Ioi 0) 1 := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) ((1 : ℝ) / 2)
  have htpos : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  let x : ℝ := 1 + t
  have hxpos : 0 < x := by dsimp [x]; linarith
  have hxne : x ≠ 1 := by dsimp [x]; linarith
  have hneg := oneSubIdentityLog_neg_of_ne_one hxpos hxne
  have hb : oneSubIdentityLog 1 ≤ oneSubIdentityLog x :=
    hbound x ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, hxpos⟩
  rw [oneSubIdentityLog_one] at hb
  exact hneg.not_ge hb

/-- Bài 10(a): hàm có cực tiểu địa phương tại 0 và không có cực đại tại đó. -/
theorem source_cubic_sine_extremum :
    cubicSine 0 = 0 ∧ deriv cubicSine 0 = 0 ∧
      IsLocalMinimumOn cubicSine univ 0 ∧ ¬ IsLocalMaximumOn cubicSine univ 0 :=
  ⟨cubicSine_zero, cubicSine_deriv_zero, cubicSine_source_local_minimum,
    cubicSine_not_source_local_maximum⟩

/-- Bài 10(b): hàm có cực đại địa phương tại 1 trên `x > 0` và không có cực tiểu tại đó. -/
theorem source_one_sub_identity_log_extremum :
    oneSubIdentityLog 1 = 0 ∧ deriv oneSubIdentityLog 1 = 0 ∧
      IsLocalMaximumOn oneSubIdentityLog (Ioi 0) 1 ∧
        ¬ IsLocalMinimumOn oneSubIdentityLog (Ioi 0) 1 :=
  ⟨oneSubIdentityLog_one, oneSubIdentityLog_deriv_one,
    oneSubIdentityLog_source_local_maximum, oneSubIdentityLog_not_source_local_minimum⟩

end calculus.Chapter04.Section04LocalExtremaExercises
