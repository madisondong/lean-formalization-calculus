import calculus.Chapter03.Section08
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# §3.8 — hai ví dụ liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3785–3797, Ví dụ 3.8.5 và 3.8.6.
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter03.Section08ElementaryExamples
open calculus.Chapter03.Section08


theorem square_difference_bound_Icc (u v : ℝ)
    (hu : u ∈ Icc (-3 : ℝ) 2) (hv : v ∈ Icc (-3 : ℝ) 2) :
    |u ^ 2 - v ^ 2| ≤ 6 * |u - v| := by
  have hu3 : |u| ≤ 3 := abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
  have hv3 : |v| ≤ 3 := abs_le.mpr ⟨hv.1, by linarith [hv.2]⟩
  have hs : |u + v| ≤ 6 := (abs_add_le u v).trans (by linarith)
  rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring, abs_mul]
  calc
    |u - v| * |u + v| ≤ |u - v| * 6 :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = 6 * |u - v| := by ring

/-- Ví dụ 3.8.5: x² liên tục đều trên [−3,2], với δ=ε/6. -/
theorem square_uniformContinuous_Icc :
    NonemptyUniformContinuousOn (Icc (-3 : ℝ) 2) (fun x : ℝ ↦ x ^ 2) := by
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  intro ε hε
  refine ⟨ε / 6, div_pos hε (by norm_num : (0 : ℝ) < 6), ?_⟩
  intro u hu v hv huv
  have hb := square_difference_bound_Icc u v hu hv
  have hh : 6 * |u - v| < ε := by linarith
  exact lt_of_le_of_lt hb hh


theorem square_continuousOn_Icc :
    ContinuousOn (fun x : ℝ ↦ x ^ 2) (Icc (-3 : ℝ) 2) :=
  nonemptyUniformContinuousOn_continuousOn square_uniformContinuous_Icc


theorem square_rational_difference_identity (u v : ℝ) :
    |u ^ 2 / (u ^ 2 + 1) - v ^ 2 / (v ^ 2 + 1)| =
      |u - v| * |u + v| / ((u ^ 2 + 1) * (v ^ 2 + 1)) := by
  have hu : 0 < u ^ 2 + 1 := by nlinarith [sq_nonneg u]
  have hv : 0 < v ^ 2 + 1 := by nlinarith [sq_nonneg v]
  have hd : 0 < (u ^ 2 + 1) * (v ^ 2 + 1) := mul_pos hu hv
  have he : u ^ 2 / (u ^ 2 + 1) - v ^ 2 / (v ^ 2 + 1) =
      (u - v) * (u + v) / ((u ^ 2 + 1) * (v ^ 2 + 1)) := by
    rw [div_sub_div (u ^ 2) (v ^ 2) hu.ne' hv.ne']
    congr 1
    ring
  rw [he, abs_div, abs_mul, abs_of_pos hd]


theorem square_rational_difference_bound (u v : ℝ) :
    |u ^ 2 / (u ^ 2 + 1) - v ^ 2 / (v ^ 2 + 1)| ≤ 2 * |u - v| := by
  have hu : 0 < u ^ 2 + 1 := by nlinarith [sq_nonneg u]
  have hv : 0 < v ^ 2 + 1 := by nlinarith [sq_nonneg v]
  have hd : 0 < (u ^ 2 + 1) * (v ^ 2 + 1) := mul_pos hu hv
  have heu : |u| ≤ u ^ 2 + 1 := by
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u]
  have hev : |v| ≤ v ^ 2 + 1 := by
    nlinarith [sq_nonneg (|v| - 1 / 2), sq_abs v]
  have hs : |u + v| ≤ (u ^ 2 + 1) + (v ^ 2 + 1) :=
    (abs_add_le u v).trans (add_le_add heu hev)
  have hsum : (u ^ 2 + 1) + (v ^ 2 + 1) ≤
      2 * ((u ^ 2 + 1) * (v ^ 2 + 1)) := by
    nlinarith [sq_nonneg u, sq_nonneg v,
      mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  calc
    |u ^ 2 / (u ^ 2 + 1) - v ^ 2 / (v ^ 2 + 1)| =
        |u - v| * |u + v| / ((u ^ 2 + 1) * (v ^ 2 + 1)) :=
      square_rational_difference_identity u v
    _ ≤ |u - v| * ((u ^ 2 + 1) + (v ^ 2 + 1)) /
        ((u ^ 2 + 1) * (v ^ 2 + 1)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) hd.le
    _ ≤ |u - v| * (2 * ((u ^ 2 + 1) * (v ^ 2 + 1))) /
        ((u ^ 2 + 1) * (v ^ 2 + 1)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)) hd.le
    _ = 2 * |u - v| := by
      apply (div_eq_iff hd.ne').mpr
      ring

/-- Ví dụ 3.8.6: x²/(x²+1) liên tục đều trên ℝ, với δ=ε/2. -/
theorem square_rational_uniformContinuous :
    NonemptyUniformContinuousOn univ (fun x : ℝ ↦ x ^ 2 / (x ^ 2 + 1)) := by
  refine ⟨univ_nonempty, ?_⟩
  intro ε hε
  refine ⟨ε / 2, div_pos hε (by norm_num : (0 : ℝ) < 2), ?_⟩
  intro u _ v _ huv
  have hb := square_rational_difference_bound u v
  have hh : 2 * |u - v| < ε := by linarith
  exact lt_of_le_of_lt hb hh

end calculus.Chapter03.Section08ElementaryExamples
