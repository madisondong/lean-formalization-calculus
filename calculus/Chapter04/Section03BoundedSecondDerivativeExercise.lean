import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bài tập 4.3.40: chặn đạo hàm bằng hàm và đạo hàm cấp hai

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1408–1409.
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section03BoundedSecondDerivativeExercise

open Set


theorem taylor_second_order_real {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (x h : ℝ) (hh : h ≠ 0) :
    ∃ c ∈ uIoo x (x + h),
      f (x + h) = f x + h * deriv f x + h ^ 2 / 2 * deriv (deriv f) c := by
  have hne : x ≠ x + h := by intro he; apply hh; linarith
  obtain ⟨c, hc, hr⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf.contDiffOn
  have hd : iteratedDerivWithin 1 f (uIcc x (x + h)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x (x + h)) x (x + h) =
      f x + h * deriv f x := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    simp [smul_eq_mul, hd]
  rw [hp] at hr
  have hi : iteratedDeriv 2 f c = deriv (deriv f) c := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [Nat.factorial, add_sub_cancel_left, hi] at hr
  refine ⟨c, hc, ?_⟩
  nlinarith [hr]


theorem positive_step_abs_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {M₀ M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (h₀ : ∀ x, |f x| ≤ M₀) (h₂ : ∀ x, |deriv (deriv f) x| ≤ M₂)
    (x h : ℝ) (hh : 0 < h) :
    |deriv f x| * h ≤ 2 * M₀ + M₂ * h ^ 2 / 2 := by
  obtain ⟨c, _, ht⟩ := taylor_second_order_real hf x h hh.ne'
  have hrem : |h ^ 2 / 2 * deriv (deriv f) c| ≤ M₂ * h ^ 2 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)]
    calc
      h ^ 2 / 2 * |deriv (deriv f) c| = |deriv (deriv f) c| * (h ^ 2 / 2) := mul_comm _ _
      _ ≤ M₂ * (h ^ 2 / 2) :=
        mul_le_mul (h₂ c) (le_refl (h ^ 2 / 2)) (by positivity) hM₂
      _ = M₂ * h ^ 2 / 2 := by ring
  have he : h * deriv f x =
      (f (x + h) - f x) - h ^ 2 / 2 * deriv (deriv f) c := by linarith [ht]
  calc
    |deriv f x| * h = |h * deriv f x| := by rw [abs_mul, abs_of_pos hh]; ring
    _ = |(f (x + h) - f x) - h ^ 2 / 2 * deriv (deriv f) c| := by rw [he]
    _ ≤ |f (x + h) - f x| + |h ^ 2 / 2 * deriv (deriv f) c| := abs_sub _ _
    _ ≤ (|f (x + h)| + |f x|) + |h ^ 2 / 2 * deriv (deriv f) c| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ 2 * M₀ + M₂ * h ^ 2 / 2 := by linarith [h₀ (x + h), h₀ x, hrem]


theorem abs_deriv_le_twice_sqrt {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {M₀ M₂ : ℝ} (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (h₀ : ∀ x, |f x| ≤ M₀) (h₂ : ∀ x, |deriv (deriv f) x| ≤ M₂)
    (x : ℝ) : |deriv f x| ≤ 2 * Real.sqrt (M₀ * M₂) := by
  by_cases hd : |deriv f x| = 0
  · rw [hd]
    positivity
  have hdpos : 0 < |deriv f x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
  rcases eq_or_lt_of_le hM₂ with hzero | hpos
  · have hz : M₂ = 0 := hzero.symm
    have hh : 0 < (2 * M₀ + 1) / |deriv f x| := by positivity
    have hb := positive_step_abs_deriv_bound hf hM₂ h₀ h₂ x
      ((2 * M₀ + 1) / |deriv f x|) hh
    rw [hz, zero_mul, zero_div, add_zero] at hb
    have he : |deriv f x| * ((2 * M₀ + 1) / |deriv f x|) = 2 * M₀ + 1 := by
      field_simp [hd]
    rw [he] at hb
    linarith
  · have hh : 0 < |deriv f x| / M₂ := div_pos hdpos hpos
    have hb := positive_step_abs_deriv_bound hf hM₂ h₀ h₂ x (|deriv f x| / M₂) hh
    have hb' := mul_le_mul_of_nonneg_left hb hM₂
    have hl : M₂ * (|deriv f x| * (|deriv f x| / M₂)) = |deriv f x| ^ 2 := by
      field_simp [hpos.ne']
    have hr : M₂ * (2 * M₀ + M₂ * (|deriv f x| / M₂) ^ 2 / 2) =
        2 * M₀ * M₂ + |deriv f x| ^ 2 / 2 := by
      field_simp [hpos.ne']
    rw [hl, hr] at hb'
    have hs := Real.sq_sqrt (mul_nonneg hM₀ hM₂)
    have hsn := Real.sqrt_nonneg (M₀ * M₂)
    nlinarith [hb', hs]

/-- Bài 4.3.40: cận của đạo hàm từ cận của hàm và đạo hàm cấp hai. -/
theorem source_bounded_second_derivative_inequality {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f)
    (h₀ : BddAbove (range fun x ↦ |f x|))
    (h₂ : BddAbove (range fun x ↦ |deriv (deriv f) x|)) :
    BddAbove (range fun x ↦ |deriv f x|) ∧
      sSup (range fun x ↦ |deriv f x|) ≤
        2 * Real.sqrt (sSup (range fun x ↦ |f x|) *
          sSup (range fun x ↦ |deriv (deriv f) x|)) := by
  have hu₀ (x : ℝ) : |f x| ≤ sSup (range fun y ↦ |f y|) :=
    le_csSup h₀ (mem_range_self x)
  have hu₂ (x : ℝ) : |deriv (deriv f) x| ≤ sSup (range fun y ↦ |deriv (deriv f) y|) :=
    le_csSup h₂ (mem_range_self x)
  have hn₀ : 0 ≤ sSup (range fun y ↦ |f y|) := (abs_nonneg (f 0)).trans (hu₀ 0)
  have hn₂ : 0 ≤ sSup (range fun y ↦ |deriv (deriv f) y|) :=
    (abs_nonneg (deriv (deriv f) 0)).trans (hu₂ 0)
  have hb (x : ℝ) := abs_deriv_le_twice_sqrt hf hn₀ hn₂ hu₀ hu₂ x
  constructor
  · refine ⟨2 * Real.sqrt (sSup (range fun x ↦ |f x|) *
      sSup (range fun x ↦ |deriv (deriv f) x|)), ?_⟩
    rintro y ⟨x, rfl⟩
    exact hb x
  · refine csSup_le (range_nonempty _) ?_
    rintro y ⟨x, rfl⟩
    exact hb x

end calculus.Chapter04.Section03BoundedSecondDerivativeExercise
