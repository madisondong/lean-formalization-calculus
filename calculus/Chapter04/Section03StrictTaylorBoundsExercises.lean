import calculus.Chapter04.Section03
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.3 — Bài 28: hai cặp bất đẳng thức Taylor ngặt

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1348–1355, Bài 4.3.28(a,b).
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter04.Section03StrictTaylorBoundsExercises

open calculus.Chapter04.Section03


theorem positive_of_positive_derivative {f d : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivAt f (d t) t)
    (hd : ∀ t : ℝ, 0 < t → 0 < d t) (hzero : f 0 = 0)
    {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hc : ContinuousOn f (Icc 0 x) := fun t ht ↦
    (hf t ht.1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo 0 x) := fun t ht ↦
    (hf t ht.1.le).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, he⟩ := lagrange_increment hx hc hdiff
  rw [(hf c hc.1.le).deriv, hzero, sub_zero, sub_zero] at he
  have hp : 0 < d c * x := mul_pos (hd c hc.1) hx
  linarith

noncomputable def logUpperResidual (x : ℝ) : ℝ :=
  x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)

noncomputable def logLowerResidual (x : ℝ) : ℝ :=
  Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)


theorem log_upper_residual_hasDerivAt (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt logUpperResidual (x ^ 3 / (1 + x)) x := by
  have hden : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
  have hi := hasDerivAt_id x
  have hlog := (hi.const_add 1).log hden
  have hp := (hi.fun_sub ((hi.fun_pow 2).div_const 2)).fun_add
    ((hi.fun_pow 3).div_const 3)
  have h := hp.fun_sub hlog
  apply h.congr_deriv
  norm_num
  field_simp [hden]
  ring

theorem log_lower_residual_hasDerivAt (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt logLowerResidual (x ^ 4 / (1 + x)) x := by
  have hden : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
  have hi := hasDerivAt_id x
  have hlog := (hi.const_add 1).log hden
  have hp := ((hi.fun_sub ((hi.fun_pow 2).div_const 2)).fun_add
    ((hi.fun_pow 3).div_const 3)).fun_sub ((hi.fun_pow 4).div_const 4)
  have h := hlog.fun_sub hp
  apply h.congr_deriv
  norm_num
  field_simp [hden]
  ring

theorem log_upper_residual_pos {x : ℝ} (hx : 0 < x) : 0 < logUpperResidual x := by
  apply positive_of_positive_derivative log_upper_residual_hasDerivAt
    (fun t ht ↦ div_pos (pow_pos ht 3) (by linarith : 0 < 1 + t))
    (by norm_num [logUpperResidual]) hx

theorem log_lower_residual_pos {x : ℝ} (hx : 0 < x) : 0 < logLowerResidual x := by
  apply positive_of_positive_derivative log_lower_residual_hasDerivAt
    (fun t ht ↦ div_pos (pow_pos ht 4) (by linarith : 0 < 1 + t))
    (by norm_num [logLowerResidual]) hx

/-- Bài 4.3.28(a): hai cận ngặt của `log(1+x)` trên `x > 0`. -/
theorem source_logarithm_strict_bounds (x : ℝ) (hx : 0 < x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 < Real.log (1 + x) ∧
      Real.log (1 + x) < x - x ^ 2 / 2 + x ^ 3 / 3 := by
  have hl := log_lower_residual_pos hx
  have hu := log_upper_residual_pos hx
  dsimp [logLowerResidual] at hl
  dsimp [logUpperResidual] at hu
  exact ⟨by linarith, by linarith⟩

theorem sqrt_one_add_gt_one {x : ℝ} (hx : 0 < x) : 1 < Real.sqrt (1 + x) := by
  have hsq : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  nlinarith [Real.sqrt_nonneg (1 + x)]


theorem sqrt_lower_residual_factor (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) - (1 + x / 2 - x ^ 2 / 8) =
      (Real.sqrt (1 + x) - 1) ^ 3 * (Real.sqrt (1 + x) + 3) / 8 := by
  let t := Real.sqrt (1 + x)
  have hs : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hxid : x = t ^ 2 - 1 := by linarith
  change t - (1 + x / 2 - x ^ 2 / 8) = (t - 1) ^ 3 * (t + 3) / 8
  rw [hxid]
  ring


theorem sqrt_upper_residual_factor (x : ℝ) (hx : 0 ≤ x) :
    1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 - Real.sqrt (1 + x) =
      (Real.sqrt (1 + x) - 1) ^ 4 *
        (Real.sqrt (1 + x) ^ 2 + 4 * Real.sqrt (1 + x) + 5) / 16 := by
  let t := Real.sqrt (1 + x)
  have hs : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hxid : x = t ^ 2 - 1 := by linarith
  change 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 - t =
    (t - 1) ^ 4 * (t ^ 2 + 4 * t + 5) / 16
  rw [hxid]
  ring

/-- Bài 4.3.28(b): cận dưới bậc hai và cận trên bậc ba trên toàn miền `x > 0`. -/
theorem source_square_root_strict_bounds (x : ℝ) (hx : 0 < x) :
    1 + x / 2 - x ^ 2 / 8 < Real.sqrt (x + 1) ∧
      Real.sqrt (x + 1) < 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 := by
  have ht := sqrt_one_add_gt_one hx
  have hdiff : 0 < Real.sqrt (1 + x) - 1 := sub_pos.mpr ht
  have hl : 0 < Real.sqrt (1 + x) - (1 + x / 2 - x ^ 2 / 8) := by
    rw [sqrt_lower_residual_factor x hx.le]
    exact div_pos (mul_pos (pow_pos hdiff 3) (by linarith)) (by norm_num)
  have hu : 0 < 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 - Real.sqrt (1 + x) := by
    rw [sqrt_upper_residual_factor x hx.le]
    exact div_pos (mul_pos (pow_pos hdiff 4)
      (by nlinarith [sq_nonneg (Real.sqrt (1 + x))])) (by norm_num)
  rw [add_comm x 1]
  exact ⟨by linarith, by linarith⟩

end calculus.Chapter04.Section03StrictTaylorBoundsExercises
