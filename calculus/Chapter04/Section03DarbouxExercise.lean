import calculus.Chapter04.Section01Derivatives
import calculus.Chapter04.Section01HigherClosed
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bài 25: giá trị trung gian của đạo hàm trên đoạn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1198–1199; Định nghĩa 4.1.7 tại dòng 97–102. Xét `a < b`; đạo hàm tại đầu mút là đạo hàm một bên. Không cần `f′` liên tục.
-/
namespace calculus.Chapter04.Section03DarbouxExercise
open Set Filter calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section01HigherClosed
open scoped Topology


theorem right_derivative_hasDerivWithinAt_Icc {f : ℝ → ℝ} {a b p : ℝ}
    (ha : HasRightDerivativeAt f a p) : HasDerivWithinAt f p (Icc a b) a := by
  have hd : HasDerivWithinAt f p (Ioi a) a := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).mpr
    simpa only [HasRightDerivativeAt, slope_eq_difference_quotient] using ha
  exact hd.Ici_of_Ioi.mono Icc_subset_Ici_self


theorem left_derivative_hasDerivWithinAt_Icc {f : ℝ → ℝ} {a b q : ℝ}
    (hb : HasLeftDerivativeAt f b q) : HasDerivWithinAt f q (Icc a b) b := by
  have hd : HasDerivWithinAt f q (Iio b) b := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mpr
    simpa only [HasLeftDerivativeAt, slope_eq_difference_quotient] using hb
  exact hd.Iic_of_Iio.mono Icc_subset_Iic_self

/-- Bài 25 trên đoạn không suy biến, với đạo hàm một bên tại hai đầu mút. -/
theorem source_endpoint_darboux_non_degenerate {f : ℝ → ℝ} {a b p q «λ» : ℝ}
    (hab : a < b) (hf : DifferentiableOnClosedInterval f a b)
    (ha : HasRightDerivativeAt f a p) (hb : HasLeftDerivativeAt f b q)
    (hp : p < «λ») (hq : «λ» < q) : ∃ c ∈ Ioo a b, deriv f c = «λ» := by
  classical
  let d : ℝ → ℝ := fun x ↦ if x = a then p else if x = b then q else deriv f x
  have hda : d a = p := by simp [d]
  have hdb : d b = q := by simp [d, hab.ne']
  have hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      simpa only [hda] using right_derivative_hasDerivWithinAt_Icc ha
    by_cases hxb : x = b
    · subst x
      simpa only [hdb] using left_derivative_hasDerivWithinAt_Icc hb
    have hxi : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    simpa only [d, if_neg hxa, if_neg hxb] using
      (hf.1 x hxi).hasDerivAt.hasDerivWithinAt (s := Icc a b)
  obtain ⟨c, hc, he⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt hab.le hd
    (by simpa only [hda] using hp) (by simpa only [hdb] using hq)
  refine ⟨c, hc, ?_⟩
  simpa only [d, if_neg hc.1.ne', if_neg hc.2.ne] using he

/-- Bài 25: giá trị trung gian của đạo hàm, kể cả đạo hàm một bên tại đầu mút. -/
theorem source_endpoint_darboux {f : ℝ → ℝ} {a b p q «λ» : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval 1 f a b)
    (ha : HasRightDerivativeAt f a p) (hb : HasLeftDerivativeAt f b q)
    (hp : p < «λ») (hq : «λ» < q) : ∃ c ∈ Ioo a b, deriv f c = «λ» :=
  source_endpoint_darboux_non_degenerate hf.1
    ((source_closed_order_one_iff hf.1).mp hf) ha hb hp hq

/-- Trường hợp phụ ngoài quy ước đoạn của sách: `a = b = 0` không có điểm nội khoảng. -/
theorem degenerate_endpoint_darboux_counterexample :
    DifferentiableOnClosedInterval (fun x : ℝ ↦ -|x|) 0 0 ∧
      HasRightDerivativeAt (fun x : ℝ ↦ -|x|) 0 (-1) ∧
      HasLeftDerivativeAt (fun x : ℝ ↦ -|x|) 0 1 ∧
      ((-1 : ℝ) < 0 ∧ (0 : ℝ) < 1) ∧
      ¬∃ c ∈ Ioo (0 : ℝ) 0, deriv (fun x : ℝ ↦ -|x|) c = 0 := by
  have hr : HasRightDerivativeAt (fun x : ℝ ↦ -|x|) 0 (-1) := by
    simpa only [HasRightDerivativeAt, abs_zero, neg_zero, sub_zero, neg_div] using
      abs_slope_right_limit.neg
  have hl : HasLeftDerivativeAt (fun x : ℝ ↦ -|x|) 0 1 := by
    simpa only [HasLeftDerivativeAt, abs_zero, neg_zero, sub_zero, neg_div, neg_neg] using
      abs_slope_left_limit.neg
  refine ⟨⟨?_, ⟨-1, hr⟩, ⟨1, hl⟩⟩, hr, hl, ⟨by norm_num, by norm_num⟩, ?_⟩
  · intro x hx
    exact (lt_asymm hx.1 hx.2).elim
  · rintro ⟨c, hc, _⟩
    exact lt_asymm hc.1 hc.2

end calculus.Chapter04.Section03DarbouxExercise
