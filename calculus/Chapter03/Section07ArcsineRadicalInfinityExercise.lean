import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
§3.7 — Bài tập 3.7.14(h)

Nguồn: dòng 3756.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07ArcsineRadicalInfinityExercise
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section07QuadraticRadicalInfinityExercises


def arcsineRadicalDomain : Set ℝ :=
  {x | 0 ≤ x ^ 2 + x ∧ -1 ≤ Real.sqrt (x ^ 2 + x) + x ∧
    Real.sqrt (x ^ 2 + x) + x ≤ 1}


theorem arcsine_negative_half : Real.arcsin (-1 / 2) = -(Real.pi / 6) := by
  apply Real.arcsin_eq_of_sin_eq
  · norm_num only [Real.sin_neg, Real.sin_pi_div_six]
  · constructor <;> linarith [Real.pi_pos]


theorem arcsineRadicalDomain_eventually_atBot :
    ∀ᶠ x : ℝ in atBot, x ∈ arcsineRadicalDomain := by
  have hq : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + x) + x) atBot (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [one_mul, add_zero] using quadratic_sqrt_plus_identity_atBot 1 0
  have hr := hq.eventually
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < -1 / 2) (by norm_num : (-1 / 2 : ℝ) < 1))
  filter_upwards [eventually_lt_atBot (-1 : ℝ), hr] with x hx harg
  change 0 ≤ x ^ 2 + x ∧ -1 ≤ Real.sqrt (x ^ 2 + x) + x ∧
    Real.sqrt (x ^ 2 + x) + x ≤ 1
  exact ⟨by nlinarith, harg.1.le, harg.2.le⟩

/-- Bài tập 3.7.14(h): giới hạn tại −∞ bằng −π/6. -/
theorem arcsine_radical_at_negative_infinity :
    DomainAtBotLimit arcsineRadicalDomain
      (fun x ↦ Real.arcsin (Real.sqrt (x ^ 2 + x) + x)) (-(Real.pi / 6)) := by
  apply domainAtBotLimit_of_eventually_domain arcsineRadicalDomain_eventually_atBot
  have hq : Tendsto (fun x : ℝ ↦ Real.sqrt (x ^ 2 + x) + x) atBot (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [one_mul, add_zero] using quadratic_sqrt_plus_identity_atBot 1 0
  rw [← arcsine_negative_half]
  simpa only [Function.comp_def] using!
    Real.continuous_arcsin.continuousAt.tendsto.comp hq

end calculus.Chapter03.Section07ArcsineRadicalInfinityExercise
