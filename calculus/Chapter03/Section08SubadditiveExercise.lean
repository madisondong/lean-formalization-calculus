import calculus.Chapter03.Section04
import calculus.Chapter03.Section08
import Mathlib.Algebra.Order.Group.Abs

/-!
# §3.8 — Bài tập 3.8.11: liên tục đều của hàm dưới cộng

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3976–3978.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08SubadditiveExercise
open calculus.Chapter03.Section04 calculus.Chapter03.Section08

/-- Bài tập 3.8.11: f dưới cộng trên ℝ, liên tục tại 0 và f(0)=0 thì liên tục đều trên ℝ. -/
theorem nonemptyUniformContinuousOn_univ_of_subadditive {f : ℝ → ℝ}
    (hf : DomainContinuousAt univ f 0) (hzero : f 0 = 0)
    (hsub : ∀ x y : ℝ, f (x + y) ≤ f x + f y) :
    NonemptyUniformContinuousOn univ f := by
  refine ⟨⟨0, mem_univ 0⟩, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := hf.2 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u _ v _ huv
  have huv_near : |f (u - v)| < ε := by
    simpa only [hzero, sub_zero] using
      hnear (u - v) (mem_univ _) (by simpa only [sub_zero] using huv)
  have hvu : |v - u| < δ := by
    rw [abs_sub_comm v u]
    exact huv
  have hvu_near : |f (v - u)| < ε := by
    simpa only [hzero, sub_zero] using
      hnear (v - u) (mem_univ _) (by simpa only [sub_zero] using hvu)
  have hu : f u ≤ f (u - v) + f v := by
    simpa only [sub_add_cancel] using hsub (u - v) v
  have hv : f v ≤ f (v - u) + f u := by
    simpa only [sub_add_cancel] using hsub (v - u) u
  apply abs_sub_lt_iff.mpr
  constructor
  · calc
      f u - f v ≤ f (u - v) := sub_le_iff_le_add.mpr hu
      _ < ε := (abs_lt.mp huv_near).2
  · calc
      f v - f u ≤ f (v - u) := sub_le_iff_le_add.mpr hv
      _ < ε := (abs_lt.mp hvu_near).2

end calculus.Chapter03.Section08SubadditiveExercise
