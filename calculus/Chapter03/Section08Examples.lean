import calculus.Chapter03.Section08
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §3.8 — Ví dụ 3.8.4: hàm 7x−2

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3779–3783.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08Examples
open calculus.Chapter03.Section08


theorem seven_x_sub_two_difference (u v : ℝ) :
    |(7 * u - 2) - (7 * v - 2)| = 7 * |u - v| := by
  rw [show (7 * u - 2) - (7 * v - 2) = 7 * (u - v) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 7)]

/-- Ví dụ 3.8.4: 7x−2 liên tục đều trên ℝ, với δ=ε/7. -/
theorem seven_x_sub_two_uniformContinuous :
    NonemptyUniformContinuousOn univ (fun x : ℝ ↦ 7 * x - 2) := by
  refine ⟨univ_nonempty, ?_⟩
  intro ε hε
  refine ⟨ε / 7, div_pos hε (by norm_num : (0 : ℝ) < 7), ?_⟩
  intro u _ v _ huv
  rw [seven_x_sub_two_difference]
  linarith

end calculus.Chapter03.Section08Examples
