import calculus.Chapter03.Section01Exercises
import calculus.Chapter03.Section04ExercisesClassification
import Mathlib.Topology.Order.OrderClosed

/-! Bài tập 3.1.20 và 3.4.3(d): phép lặp hàm và hàm xác định theo từng khoảng. -/
namespace calculus.Chapter03.Section01IteratesAndSection04PiecewiseContinuity

set_option autoImplicit false

open Set
open calculus.Chapter03.Section04

/-- Bài tập 3.1.20: lần lặp thứ hai tăng ngặt, lần lặp thứ ba giảm không ngặt. -/
theorem strictAnti_of_strictMono_second_antitone_third {f : ℝ → ℝ}
    (h2 : StrictMono (fun x ↦ f (f x)))
    (h3 : Antitone (fun x ↦ f (f (f x)))) : StrictAnti f := by
  intro x y hxy
  by_contra h
  have hle : f x ≤ f y := le_of_not_gt h
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (not_lt_of_ge (h3 hxy.le)) (h2 hlt)
  · have hh := h2 hxy
    change f (f x) < f (f y) at hh
    rw [heq] at hh
    exact lt_irrefl _ hh

/-- Bài tập 3.4.3(d): nhánh thứ hai áp dụng khi x>1. -/
noncomputable def cosineAbsoluteValuePiecewise (x : ℝ) : ℝ :=
  if x ≤ 1 then Real.cos (Real.pi * x / 2) else |x - 1|


theorem cosineAbsoluteValuePiecewise_left {x : ℝ} (hx : x ≤ 1) :
    cosineAbsoluteValuePiecewise x = Real.cos (Real.pi * x / 2) := by
  simp only [cosineAbsoluteValuePiecewise, if_pos hx]


theorem cosineAbsoluteValuePiecewise_right {x : ℝ} (hx : 1 < x) :
    cosineAbsoluteValuePiecewise x = |x - 1| := by
  simp only [cosineAbsoluteValuePiecewise, if_neg (not_le.mpr hx)]


theorem cosineAbsoluteValuePiecewise_continuous :
    Continuous cosineAbsoluteValuePiecewise := by
  have hcos : Continuous (fun x : ℝ ↦ Real.cos (Real.pi * x / 2)) := by
    fun_prop
  have habs : Continuous (fun x : ℝ ↦ |x - 1|) := by
    fun_prop
  exact hcos.if_le habs continuous_id continuous_const (by
    intro x hx
    change x = 1 at hx
    rw [hx]
    simp [Real.cos_pi_div_two])


theorem cosineAbsoluteValuePiecewise_domain_continuous_iff (a : ℝ) :
    DomainContinuousAt univ cosineAbsoluteValuePiecewise a ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact (domainContinuousAt_univ cosineAbsoluteValuePiecewise a).mpr
      cosineAbsoluteValuePiecewise_continuous.continuousAt

end calculus.Chapter03.Section01IteratesAndSection04PiecewiseContinuity
