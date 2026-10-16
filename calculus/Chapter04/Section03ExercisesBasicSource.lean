import calculus.Chapter04.Section03ExercisesBasic
import calculus.Chapter04.Section01Derivatives

/-!
# Quy ước khả vi một bên trong Bài tập 4.3.6

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1118–1119 và Định nghĩa 4.1.7. Đạo hàm tại đầu mút là đạo hàm một bên; đoạn `[0, a]` có `a > 0`.
-/
namespace calculus.Chapter04.Section03ExercisesBasicSource
open Set Filter calculus.Chapter04.Section01Derivatives
open scoped Topology


theorem source_closed_differentiableOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOnClosedInterval f a b) : DifferentiableOn ℝ f (Icc a b) := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    obtain ⟨L, hL⟩ := hf.2.1
    have hd : HasDerivWithinAt f L (Ioi a) a := by
      apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).mpr
      simpa only [HasRightDerivativeAt, slope_eq_difference_quotient] using hL
    exact hd.Ici_of_Ioi.differentiableWithinAt.mono Icc_subset_Ici_self
  by_cases hxb : x = b
  · subst x
    obtain ⟨L, hL⟩ := hf.2.2
    have hd : HasDerivWithinAt f L (Iio b) b := by
      apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mpr
      simpa only [HasLeftDerivativeAt, slope_eq_difference_quotient] using hL
    exact hd.Iic_of_Iio.differentiableWithinAt.mono Icc_subset_Iic_self
  exact (hf.1 x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
    lt_of_le_of_ne hx.2 hxb⟩).differentiableWithinAt

/-- Bài 6: đạo hàm đầu mút là đạo hàm một bên, với `a > 0`. -/
theorem source_exponential_weight_witness {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hf : DifferentiableOnClosedInterval f 0 a) (hz : f a = 0) :
    ∃ c ∈ Ioo 0 a, deriv f c = f c * (2024 - 1 / c) :=
  Section03ExercisesBasic.exponential_weight_witness ha (source_closed_differentiableOn hf) hz

end calculus.Chapter04.Section03ExercisesBasicSource
