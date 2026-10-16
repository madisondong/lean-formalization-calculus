import calculus.Chapter03.Section04ExercisesDense
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# §3.6 — Bài tập 5: điểm liên tục của hàm hai nhánh

Nguồn: dòng 3137–3152.
-/
namespace calculus.Chapter03.Section06ExercisesMixtures

open Set
open calculus.Chapter03.Section04 calculus.Chapter03.Section04ExercisesDense

/-- Bài tập 5(a): hàm liên tục tại a khi và chỉ khi sin|a|=0. -/
theorem exercise05_absolute_sine_mixture (a : ℝ) :
    DomainContinuousAt univ (rationalMixture (fun x => Real.sin  |x| ) (fun _ => 0)) a ↔
      Real.sin  |a| =0 :=
  rational_mixture_continuity_iff (Real.continuous_sin.continuousAt.comp
    continuous_abs.continuousAt) continuousAt_const

/-- Bài tập 5(b): tập điểm liên tục chính xác là {−1,1}. -/
theorem exercise05_quadratic_mixture (a : ℝ) :
    DomainContinuousAt univ (rationalMixture (fun _ => 0) (fun x => x^2-1)) a ↔
      a=(-1:ℝ) ∨ a=1 := by
  have hh : ContinuousAt (fun x : ℝ => x^2-1) a :=
    ((continuous_id.pow 2).sub continuous_const).continuousAt
  rw [rational_mixture_continuity_iff (g := fun _ => 0) (h := fun x => x^2-1)
    continuousAt_const hh]
  change (0:ℝ)=a^2-1 ↔ a=(-1:ℝ) ∨ a=1
  constructor
  · intro h
    have hp : (a+1)*(a-1)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> rw [h] <;> norm_num

end calculus.Chapter03.Section06ExercisesMixtures
