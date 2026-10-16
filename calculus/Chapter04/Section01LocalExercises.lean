import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Bài 9 và Bài 13(c,d): đạo hàm tại điểm nối

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 501–512, dòng 570–575.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01LocalExercises
open Filter Set
open scoped Topology


theorem hasDerivAt_zero_of_slope_abs_le {f : ℝ → ℝ}
    (hb : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), |(f y - f 0) / y| ≤ |y|) :
    HasDerivAt f 0 0 := by
  have ha : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using (continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {(0 : ℝ)}ᶜ))
  have hn : Tendsto (fun y : ℝ ↦ |(f y - f 0) / y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hb ha
  have ht : Tendsto (fun y : ℝ ↦ (f y - f 0) / y) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using hn)
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient]
  simpa only [sub_zero] using ht


def positiveSquare (x : ℝ) : ℝ := if 0 < x then x ^ 2 else 0


theorem positiveSquare_hasDerivAt_zero : HasDerivAt positiveSquare 0 0 := by
  apply hasDerivAt_zero_of_slope_abs_le
  filter_upwards [self_mem_nhdsWithin] with y hy
  have heq0 : positiveSquare 0 = 0 := by simp [positiveSquare]
  rw [heq0, sub_zero, positiveSquare]
  split_ifs with h
  · have heq : y ^ 2 / y = y := by field_simp
    rw [heq]
  · simp


theorem positiveSquare_hasDerivAt_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt positiveSquare (2 * x) x := by
  have hd : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact if_pos (show 0 < y from hy)


theorem positiveSquare_hasDerivAt_neg (x : ℝ) (hx : x < 0) :
    HasDerivAt positiveSquare 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact if_neg (not_lt.mpr (show y ≤ 0 by exact (show y < 0 from hy).le))

/-- Bài 9(a): đạo hàm bằng `2x` khi `x > 0`, bằng 0 khi `x ≤ 0`. -/
theorem positiveSquare_hasDerivAt (x : ℝ) :
    HasDerivAt positiveSquare (if 0 < x then 2 * x else 0) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simpa only [if_neg (not_lt.mpr hx.le)] using positiveSquare_hasDerivAt_neg x hx
  · subst x
    simpa using positiveSquare_hasDerivAt_zero
  · simpa only [if_pos hx] using positiveSquare_hasDerivAt_pos x hx


theorem positiveSquare_differentiable : Differentiable ℝ positiveSquare :=
  fun x ↦ (positiveSquare_hasDerivAt x).differentiableAt


theorem positiveSquare_derivative (x : ℝ) :
    deriv positiveSquare x = if 0 < x then 2 * x else 0 :=
  (positiveSquare_hasDerivAt x).deriv


theorem positiveSquare_derivative_eq_add_abs : deriv positiveSquare = fun x : ℝ ↦ x + |x| := by
  funext x
  rw [positiveSquare_derivative]
  by_cases hx : 0 < x
  · rw [if_pos hx, abs_of_pos hx]
    ring
  · rw [if_neg hx, abs_of_nonpos (le_of_not_gt hx)]
    ring

/-- Bài 9(b): đạo hàm liên tục trên ℝ. -/
theorem positiveSquare_derivative_continuous : Continuous (deriv positiveSquare) := by
  rw [positiveSquare_derivative_eq_add_abs]
  exact continuous_id.add continuous_abs

/-- Bài 9(b): `f′` không khả vi tại 0. -/
theorem positiveSquare_derivative_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ (deriv positiveSquare) 0 := by
  intro hd
  apply not_differentiableAt_abs_zero
  rw [positiveSquare_derivative_eq_add_abs] at hd
  have hh := hd.sub (hasDerivAt_id (0 : ℝ)).differentiableAt
  exact hh.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
    simp only [Pi.sub_apply, id_eq, add_sub_cancel_left])


theorem positiveSquare_derivative_hasDerivAt_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv positiveSquare) 2 x := by
  have hd : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [positiveSquare_derivative, if_pos (show 0 < y from hy)]


theorem positiveSquare_derivative_hasDerivAt_neg (x : ℝ) (hx : x < 0) :
    HasDerivAt (deriv positiveSquare) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  rw [positiveSquare_derivative, if_neg (not_lt.mpr (show y ≤ 0 by exact (show y < 0 from hy).le))]


theorem positiveSquare_derivative_differentiableAt_iff (x : ℝ) :
    DifferentiableAt ℝ (deriv positiveSquare) x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    exact positiveSquare_derivative_not_differentiableAt_zero h
  · intro hx
    rcases lt_or_gt_of_ne hx with h | h
    · exact (positiveSquare_derivative_hasDerivAt_neg x h).differentiableAt
    · exact (positiveSquare_derivative_hasDerivAt_pos x h).differentiableAt

/-- Bài 13(c): hàm `x|x|` có đạo hàm 0 tại 0. -/
theorem signed_absolute_hasDerivAt_zero : HasDerivAt (fun x : ℝ ↦ x * |x|) 0 0 := by
  apply hasDerivAt_zero_of_slope_abs_le
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [zero_mul, abs_zero, sub_zero]
  have heq : y * |y| / y = |y| := by field_simp [show y ≠ 0 from hy]
  rw [heq, abs_abs]


def rationalSquareIrrationalCube (x : ℝ) : ℝ := by
  classical
  exact if ∃ q : ℚ, (q : ℝ) = x then x ^ 2 else x ^ 3


theorem rationalSquareIrrationalCube_zero : rationalSquareIrrationalCube 0 = 0 := by
  simp [rationalSquareIrrationalCube]

/-- Bài 13(d): hàm có đạo hàm 0 tại 0. -/
theorem rationalSquareIrrationalCube_hasDerivAt_zero :
    HasDerivAt rationalSquareIrrationalCube 0 0 := by
  apply hasDerivAt_zero_of_slope_abs_le
  have hsmall : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), |y| < 1 := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.eventually
        (Iio_mem_nhds (show |(0 : ℝ)| < 1 by norm_num)))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hy hs
  rw [rationalSquareIrrationalCube_zero, sub_zero, rationalSquareIrrationalCube]
  split_ifs with hq
  · have heq : y ^ 2 / y = y := by field_simp
    rw [heq]
  · have heq : y ^ 3 / y = y ^ 2 := by field_simp
    rw [heq, abs_pow]
    nlinarith [abs_nonneg y]

end calculus.Chapter04.Section01LocalExercises
