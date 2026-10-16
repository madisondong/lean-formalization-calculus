import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §4.3, Bài 43: giới hạn hàm và cận đạo hàm cấp hai

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1418–1420. Không cần `f″` liên tục; đạo hàm tại 0 được hiểu trong nửa trục.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03BoundedSecondDerivativeVanishingExercise
open Set Filter
open scoped Topology


theorem first_derivative_forward_estimate {f d d₂ : ℝ → ℝ} {M x h : ℝ}
    (hf : ∀ y ∈ Ioi 0, HasDerivAt f (d y) y)
    (hd : ∀ y ∈ Ioi 0, HasDerivAt d (d₂ y) y)
    (hM : 0 ≤ M) (hbound : ∀ y ∈ Ioi 0, |d₂ y| ≤ M)
    (hx : 0 < x) (hh : 0 < h) :
    |d x| ≤ M * h + |f (x + h) - f x| / h := by
  have hcont : ContinuousOn f (Icc x (x + h)) := by
    intro y hy
    exact (hf y (by change 0 < y; linarith [hy.1])).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzs⟩ := exists_hasDerivAt_eq_slope f d (by linarith : x < x + h)
    hcont (fun y hy ↦ hf y (by change 0 < y; linarith [hy.1]))
  have hzpos : z ∈ Ioi 0 := by change 0 < z; linarith [hz.1]
  have hvar : |d z - d x| ≤ M * |z - x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy ↦ (hd y hy).hasDerivWithinAt)
        (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hbound y hy)
        (convex_Ioi 0) hx hzpos
  have hstep : |z - x| ≤ h := by
    rw [abs_of_pos (sub_pos.mpr hz.1)]
    linarith [hz.2]
  have hdz : |d z| = |f (x + h) - f x| / h := by
    rw [hzs, show x + h - x = h by ring, abs_div, abs_of_pos hh]
  calc
    |d x| = |(d x - d z) + d z| := by congr 1; ring
    _ ≤ |d x - d z| + |d z| := abs_add_le _ _
    _ ≤ M * h + |f (x + h) - f x| / h := by
      rw [abs_sub_comm, hdz]
      exact add_le_add (hvar.trans (mul_le_mul_of_nonneg_left hstep hM)) le_rfl


theorem first_derivative_tendsto_zero_of_bounded_second_derivative
    {f d d₂ : ℝ → ℝ} {L M : ℝ}
    (hf : ∀ x ∈ Ioi 0, HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Ioi 0, HasDerivAt d (d₂ x) x)
    (hbound : ∀ x ∈ Ioi 0, |d₂ x| ≤ M)
    (hl : Tendsto f atTop (𝓝 L)) : Tendsto d atTop (𝓝 0) := by
  have hM : 0 ≤ M := (abs_nonneg (d₂ 1)).trans (hbound 1 (by norm_num))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h : ℝ := ε / (4 * (M + 1))
  have hden : 0 < 4 * (M + 1) := by linarith
  have hh : 0 < h := div_pos hε hden
  have hprod : h * (4 * (M + 1)) = ε := by
    exact div_mul_cancel₀ ε hden.ne'
  have hMh : M * h < ε / 2 := by nlinarith
  have hshift : Tendsto (fun x : ℝ ↦ x + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hdiff : Tendsto (fun x : ℝ ↦ f (x + h) - f x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using! (hl.comp hshift).sub hl
  have hsmall := (Metric.tendsto_nhds.mp hdiff) (ε * h / 2) (by positivity)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hfx hx
  have hfx' : |f (x + h) - f x| < ε * h / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hfx
  have hquot : |f (x + h) - f x| / h < ε / 2 := by
    apply (div_lt_iff₀ hh).mpr
    nlinarith
  have hest := first_derivative_forward_estimate hf hd hM hbound hx hh
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Bài 43: `f → 0` và `f″` bị chặn trên nửa trục kéo theo `f′ → 0`. -/
theorem source_bounded_second_derivative_vanishing
    {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hd : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hbound : BddAbove ((fun x : ℝ ↦ |deriv (deriv f) x|) '' Ioi 0))
    (hl : Tendsto f atTop (𝓝 0)) : Tendsto (deriv f) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hbound
  apply first_derivative_tendsto_zero_of_bounded_second_derivative
    (M := M) (d₂ := deriv (deriv f)) _ _ _ hl
  · intro x hx
    exact ((hf x (mem_Ici.mpr (mem_Ioi.mp hx).le)).differentiableAt (Ici_mem_nhds hx)).hasDerivAt
  · intro x hx
    exact ((hd x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  · intro x hx
    exact hM ⟨x, hx, rfl⟩

end calculus.Chapter04.Section03BoundedSecondDerivativeVanishingExercise
