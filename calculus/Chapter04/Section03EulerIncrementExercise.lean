import calculus.Chapter02.Section06Euler
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bài tập 4.3.14: tốc độ của hiệu hai xấp xỉ Euler

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1155–1156.
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section03EulerIncrementExercise

open Filter
open scoped Topology
open calculus.Chapter02.Section06Euler


theorem euler_approx_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.exp 1 * (1 - 1 / ((n : ℝ) + 1)) ≤ eulerApprox n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hbase
  have hscale := mul_le_mul_of_nonneg_left hl hnpos.le
  have hid : (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) =
      1 - 1 / ((n : ℝ) + 1) := by
    (field_simp [hnpos.ne', hnp.ne']; ring)
  rw [hid] at hscale
  have hexact : Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) =
      eulerApprox n := by
    rw [Real.exp_nat_mul, Real.exp_log hbase]
    rfl
  have hsmall : 1 - 1 / ((n : ℝ) + 1) ≤
      Real.exp (-(1 / ((n : ℝ) + 1))) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / ((n : ℝ) + 1)))
  calc
    Real.exp 1 * (1 - 1 / ((n : ℝ) + 1)) ≤
        Real.exp 1 * Real.exp (-(1 / ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos 1).le
    _ = Real.exp (1 - 1 / ((n : ℝ) + 1)) := by
      rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ eulerApprox n := by
      rw [← hexact]
      exact Real.exp_le_exp.mpr hscale


theorem euler_increment_sqrt_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.sqrt (n : ℝ) * (eulerApprox (n + 1) - eulerApprox n) ∧
      Real.sqrt (n : ℝ) * (eulerApprox (n + 1) - eulerApprox n) ≤
        Real.exp 1 / Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hi := eulerApprox_le_succ n hn
  have hu : eulerApprox (n + 1) ≤ Real.exp 1 := by
    simpa only [eulerApprox, one_div] using
      (Real.one_add_inv_pow_le_exp (n := n + 1))
  have hl := euler_approx_lower_bound n hn
  have he : Real.exp 1 - eulerApprox n ≤ Real.exp 1 / ((n : ℝ) + 1) := by
    rw [mul_sub, mul_one] at hl
    simpa only [mul_one_div] using (by linarith :
      Real.exp 1 - eulerApprox n ≤ Real.exp 1 * (1 / ((n : ℝ) + 1)))
  have hlast : Real.sqrt (n : ℝ) * (Real.exp 1 / ((n : ℝ) + 1)) ≤
      Real.exp 1 / Real.sqrt (n : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hnp hs).mpr
    calc
      Real.sqrt (n : ℝ) * Real.exp 1 * Real.sqrt (n : ℝ) =
          Real.exp 1 * Real.sqrt (n : ℝ) ^ 2 := by ring
      _ = Real.exp 1 * (n : ℝ) := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ Real.exp 1 * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
  refine ⟨mul_nonneg hs.le (sub_nonneg.mpr hi), ?_⟩
  calc
    Real.sqrt (n : ℝ) * (eulerApprox (n + 1) - eulerApprox n) ≤
        Real.sqrt (n : ℝ) * (Real.exp 1 - eulerApprox n) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hu _) hs.le
    _ ≤ Real.sqrt (n : ℝ) * (Real.exp 1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left he hs.le
    _ ≤ Real.exp 1 / Real.sqrt (n : ℝ) := hlast


theorem euler_increment_sqrt_tendsto :
    Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ) *
      (eulerApprox (n + 1) - eulerApprox n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hz : Tendsto (fun n : ℕ ↦ Real.exp 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := Real.exp 1)).mul hs.inv_tendsto_atTop
  apply squeeze_zero' (g := fun n : ℕ ↦ Real.exp 1 / Real.sqrt (n : ℝ))
  · exact eventually_atTop.mpr ⟨1, fun n hn ↦ (euler_increment_sqrt_bounds n hn).1⟩
  · exact eventually_atTop.mpr ⟨1, fun n hn ↦ (euler_increment_sqrt_bounds n hn).2⟩
  · exact hz

/-- Bài 4.3.14: giới hạn bằng 0. -/
theorem source_euler_increment_sqrt_limit :
    calculus.Chapter02.Section03.ConvergesTo
      (fun n : ℕ ↦ Real.sqrt (n : ℝ) *
        ((1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) - (1 + 1 / (n : ℝ)) ^ n)) 0 := by
  apply calculus.Chapter02.Section03.convergesTo_iff_tendsto.mpr
  simpa only [eulerApprox] using euler_increment_sqrt_tendsto

end calculus.Chapter04.Section03EulerIncrementExercise
