import calculus.Chapter04.Section03BoundedSecondDerivativeExercise
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bài tập 4.3.41: cận bậc ba của đạo hàm

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1411–1413.
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section03BoundedThirdDerivativeExercise

open Set
open calculus.Chapter04.Section03BoundedSecondDerivativeExercise


theorem taylor_third_order_real {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (x h : ℝ) (hh : h ≠ 0) :
    ∃ c ∈ uIoo x (x + h),
      f (x + h) = f x + h * deriv f x + h ^ 2 / 2 * deriv (deriv f) x +
        h ^ 3 / 6 * deriv (deriv (deriv f)) c := by
  have hne : x ≠ x + h := by intro he; apply hh; linarith
  obtain ⟨c, hc, hr⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  have h₁ : iteratedDerivWithin 1 f (uIcc x (x + h)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc, iteratedDeriv_one]
  have h₂ : iteratedDerivWithin 2 f (uIcc x (x + h)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc,
      show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hp : taylorWithinEval f 2 (uIcc x (x + h)) x (x + h) =
      f x + h * deriv f x + h ^ 2 / 2 * deriv (deriv f) x := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    simp only [Nat.factorial, Nat.cast_zero, Nat.cast_one, zero_add, one_mul,
      pow_one, inv_one, add_sub_cancel_left, h₁, h₂, smul_eq_mul]
    norm_num only
    ring
  have hi : iteratedDeriv 3 f c = deriv (deriv (deriv f)) c := by
    rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
      show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hp] at hr
  norm_num only [Nat.factorial, add_sub_cancel_left, hi] at hr
  refine ⟨c, hc, ?_⟩
  nlinarith [hr]


theorem symmetric_step_abs_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {M₀ M₃ : ℝ} (h₀ : ∀ x, |f x| ≤ M₀)
    (h₃ : ∀ x, |deriv (deriv (deriv f)) x| ≤ M₃)
    (x h : ℝ) (hh : 0 < h) :
    |deriv f x| * h ≤ M₀ + M₃ * h ^ 3 / 6 := by
  obtain ⟨cPlus, _, hp⟩ := taylor_third_order_real hf x h hh.ne'
  obtain ⟨cMinus, _, hm⟩ := taylor_third_order_real hf x (-h) (neg_ne_zero.mpr hh.ne')
  have he : 2 * h * deriv f x =
      (f (x + h) - f (x - h)) - h ^ 3 / 6 *
        (deriv (deriv (deriv f)) cPlus + deriv (deriv (deriv f)) cMinus) := by
    have hcube : (-h) ^ 3 = -(h ^ 3) := by ring
    simp only [neg_sq, hcube, ← sub_eq_add_neg] at hm
    nlinarith [hp, hm]
  have hb : |deriv (deriv (deriv f)) cPlus + deriv (deriv (deriv f)) cMinus| ≤ 2 * M₃ :=
    (abs_add_le _ _).trans (by linarith [h₃ cPlus, h₃ cMinus])
  have hr : |h ^ 3 / 6 *
      (deriv (deriv (deriv f)) cPlus + deriv (deriv (deriv f)) cMinus)| ≤ M₃ * h ^ 3 / 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h ^ 3 / 6)]
    have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ h ^ 3 / 6)
    nlinarith [this]
  have hd : |2 * h * deriv f x| = 2 * h * |deriv f x| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * h)]
  have ht : 2 * h * |deriv f x| ≤ 2 * M₀ + M₃ * h ^ 3 / 3 := by
    rw [← hd, he]
    have htr := abs_sub (f (x + h) - f (x - h))
      (h ^ 3 / 6 * (deriv (deriv (deriv f)) cPlus + deriv (deriv (deriv f)) cMinus))
    have hfn := abs_sub (f (x + h)) (f (x - h))
    linarith [htr, hfn, h₀ (x + h), h₀ (x - h), hr]
  nlinarith [ht]


theorem abs_deriv_cube_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {M₀ M₃ : ℝ} (hM₀ : 0 ≤ M₀) (hM₃ : 0 ≤ M₃)
    (h₀ : ∀ x, |f x| ≤ M₀) (h₃ : ∀ x, |deriv (deriv (deriv f)) x| ≤ M₃)
    (x : ℝ) : (2 * |deriv f x|) ^ 3 ≤ 9 * M₀ ^ 2 * M₃ := by
  by_cases hd : |deriv f x| = 0
  · simp only [hd, mul_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M₀)) hM₃
  by_cases hz : M₀ = 0
  · have he : f = fun _ ↦ 0 := by
      funext y
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [hz] using h₀ y) (abs_nonneg _)
    rw [he]
    simp [hz]
  have hdpos : 0 < |deriv f x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
  have hmpos : 0 < M₀ := lt_of_le_of_ne hM₀ (Ne.symm hz)
  have hh : 0 < 3 * M₀ / (2 * |deriv f x|) := by positivity
  have hb := symmetric_step_abs_deriv_bound hf h₀ h₃ x
    (3 * M₀ / (2 * |deriv f x|)) hh
  have hb' := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ 16 * |deriv f x| ^ 3)
  have hl : (16 * |deriv f x| ^ 3) *
      (|deriv f x| * (3 * M₀ / (2 * |deriv f x|))) =
      M₀ * (24 * |deriv f x| ^ 3) := by
    (field_simp [hd]; ring)
  have hr : (16 * |deriv f x| ^ 3) *
      (M₀ + M₃ * (3 * M₀ / (2 * |deriv f x|)) ^ 3 / 6) =
      M₀ * (16 * |deriv f x| ^ 3 + 9 * M₀ ^ 2 * M₃) := by
    (field_simp [hd]; ring)
  rw [hl, hr] at hb'
  have hc := (mul_le_mul_iff_right₀ hmpos).mp hb'
  nlinarith [hc]


theorem abs_deriv_le_half_cube_root {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {M₀ M₃ : ℝ} (hM₀ : 0 ≤ M₀) (hM₃ : 0 ≤ M₃)
    (h₀ : ∀ x, |f x| ≤ M₀) (h₃ : ∀ x, |deriv (deriv (deriv f)) x| ≤ M₃)
    (x : ℝ) : |deriv f x| ≤ Real.rpow (9 * M₀ ^ 2 * M₃) (1 / 3) / 2 := by
  rw [Real.rpow_eq_pow]
  have hA : 0 ≤ 9 * M₀ ^ 2 * M₃ := by positivity
  have hs : ((9 * M₀ ^ 2 * M₃) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 9 * M₀ ^ 2 * M₃ := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (n := 3) hA (by decide)
  have hn := Real.rpow_nonneg hA (1 / 3)
  have hc := abs_deriv_cube_bound hf hM₀ hM₃ h₀ h₃ x
  have hb : 2 * |deriv f x| ≤ (9 * M₀ ^ 2 * M₃) ^ (1 / 3 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by decide) hn
    rw [hs]
    exact hc
  linarith

/-- Bài 4.3.41: cận của đạo hàm cấp một từ cận của hàm và đạo hàm cấp ba. -/
theorem source_bounded_third_derivative_inequality {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f)
    (h₀ : BddAbove (range fun x ↦ |f x|))
    (h₃ : BddAbove (range fun x ↦ |deriv (deriv (deriv f)) x|)) :
    BddAbove (range fun x ↦ |deriv f x|) ∧
      BddAbove (range fun x ↦ |deriv (deriv f) x|) ∧
      sSup (range fun x ↦ |deriv f x|) ≤
        Real.rpow (9 * sSup (range fun x ↦ |f x|) ^ 2 *
          sSup (range fun x ↦ |deriv (deriv (deriv f)) x|)) (1 / 3) / 2 := by
  have hu₀ (x : ℝ) : |f x| ≤ sSup (range fun y ↦ |f y|) :=
    le_csSup h₀ (mem_range_self x)
  have hu₃ (x : ℝ) : |deriv (deriv (deriv f)) x| ≤
      sSup (range fun y ↦ |deriv (deriv (deriv f)) y|) := le_csSup h₃ (mem_range_self x)
  have hn₀ : 0 ≤ sSup (range fun y ↦ |f y|) := (abs_nonneg (f 0)).trans (hu₀ 0)
  have hn₃ : 0 ≤ sSup (range fun y ↦ |deriv (deriv (deriv f)) y|) :=
    (abs_nonneg _).trans (hu₃ 0)
  have hb (x : ℝ) := abs_deriv_le_half_cube_root hf hn₀ hn₃ hu₀ hu₃ x
  have hd : BddAbove (range fun x ↦ |deriv f x|) := by
    refine ⟨Real.rpow (9 * sSup (range fun y ↦ |f y|) ^ 2 *
      sSup (range fun y ↦ |deriv (deriv (deriv f)) y|)) (1 / 3) / 2, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hb x
  have hg : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hdd := (source_bounded_second_derivative_inequality hg hd h₃).1
  refine ⟨hd, hdd, csSup_le (range_nonempty _) ?_⟩
  rintro y ⟨x, rfl⟩
  exact hb x

end calculus.Chapter04.Section03BoundedThirdDerivativeExercise
