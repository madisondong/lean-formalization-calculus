import calculus.Chapter04.Section01Derivatives
import calculus.Chapter04.Section01LimitExercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bài 13(a,b): phần nguyên và căn trong hàm lượng giác

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 568–569. Căn bậc hai trong Bài 13(b) áp dụng cho `|x|`.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01LocalFurtherExercises
open Filter Set
open scoped Topology


def floorSineSquare (x : ℝ) : ℝ := (Int.floor x : ℝ) * (Real.sin (Real.pi * x)) ^ 2


theorem floor_abs_le_one_of_abs_lt_one (x : ℝ) (hx : |x| < 1) :
    |(Int.floor x : ℝ)| ≤ 1 := by
  have hb := abs_lt.mp hx
  have hl : (-1 : ℤ) ≤ Int.floor x := by
    apply Int.le_floor.mpr
    simpa using hb.1.le
  have hu : Int.floor x < (1 : ℤ) := by
    apply Int.floor_lt.mpr
    simpa using hb.2
  apply abs_le.mpr
  constructor
  · exact_mod_cast hl
  · exact_mod_cast (show Int.floor x ≤ (1 : ℤ) by omega)


theorem floorSineSquare_quotient_bound (x : ℝ) (hx : x ≠ 0) (hs : |x| < 1) :
    |(floorSineSquare x - floorSineSquare 0) / x| ≤ Real.pi ^ 2 * |x| := by
  have hf := floor_abs_le_one_of_abs_lt_one x hs
  have hsin : |Real.sin (Real.pi * x)| ≤ Real.pi * |x| := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos] using (Real.abs_sin_le_abs (x := Real.pi * x))
  have hsq : |Real.sin (Real.pi * x)| ^ 2 ≤ Real.pi ^ 2 * |x| ^ 2 := by
    nlinarith [abs_nonneg (Real.sin (Real.pi * x)), abs_nonneg x, Real.pi_pos]
  have hprod : |(Int.floor x : ℝ)| * |Real.sin (Real.pi * x)| ^ 2 ≤ Real.pi ^ 2 * |x| ^ 2 := by
    exact (mul_le_mul_of_nonneg_right hf (sq_nonneg _)).trans (by simpa only [one_mul] using hsq)
  have hden : 0 < |x| := abs_pos.mpr hx
  simp only [floorSineSquare, mul_zero, Real.sin_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, abs_div, abs_mul, abs_pow]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Bài 13(a): tích của phần nguyên của `x` với `sin²(πx)` có đạo hàm 0 tại 0. -/
theorem floorSineSquare_hasDerivAt_zero : HasDerivAt floorSineSquare 0 0 := by
  have hb : Tendsto (fun x : ℝ ↦ Real.pi ^ 2 * |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ ↦ |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {(0 : ℝ)}ᶜ))
    simpa only [mul_zero] using (tendsto_const_nhds (x := Real.pi ^ 2)).mul ht
  have hsmall : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), |x| < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.eventually
        (Iio_mem_nhds (show |(0 : ℝ)| < 1 by norm_num)))
  have hbound : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
      |(floorSineSquare x - floorSineSquare 0) / x| ≤ Real.pi ^ 2 * |x| := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hs
    exact floorSineSquare_quotient_bound x hx hs
  have hn : Tendsto (fun x : ℝ ↦ |(floorSineSquare x - floorSineSquare 0) / x|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hb
  have ht : Tendsto (fun x : ℝ ↦ (floorSineSquare x - floorSineSquare 0) / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using hn)
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient]
  simpa only [sub_zero] using ht


def cosineSquareRootAbsolute (x : ℝ) : ℝ := Real.cos (Real.sqrt |x|)


theorem cosineSquareRootAbsolute_zero : cosineSquareRootAbsolute 0 = 1 := by
  simp [cosineSquareRootAbsolute]


theorem cosineSquareRootAbsolute_even (x : ℝ) :
    cosineSquareRootAbsolute (-x) = cosineSquareRootAbsolute x := by
  simp only [cosineSquareRootAbsolute, abs_neg]


theorem cosineSquareRootAbsolute_derivative_zero_of_differentiable
    (hf : DifferentiableAt ℝ cosineSquareRootAbsolute 0) : deriv cosineSquareRootAbsolute 0 = 0 := by
  have hneg : HasDerivAt (fun y : ℝ ↦ cosineSquareRootAbsolute (-y))
      (-deriv cosineSquareRootAbsolute 0) 0 := by
    apply (hf.hasDerivAt.comp_of_eq 0 (hasDerivAt_neg' (0 : ℝ)) (by simp)).congr_deriv
    ring
  have hself : HasDerivAt cosineSquareRootAbsolute (-deriv cosineSquareRootAbsolute 0) 0 := by
    apply hneg.congr_of_eventuallyEq
    exact Eventually.of_forall fun y ↦ (cosineSquareRootAbsolute_even y).symm
  have heq := hf.hasDerivAt.unique hself
  linarith


theorem cosineSquareRootAbsolute_right_quotient_le (x : ℝ) (hx : 0 < x)
    (hs : x ≤ Real.pi ^ 2) :
    (cosineSquareRootAbsolute x - cosineSquareRootAbsolute 0) / x ≤ -2 / Real.pi ^ 2 := by
  have hroot : Real.sqrt |x| ≤ Real.pi := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨Real.pi_pos.le, by simpa only [abs_of_pos hx] using hs⟩
  have hc := Real.cos_le_one_sub_mul_cos_sq
    (show |Real.sqrt (|x|)| ≤ Real.pi by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hroot)
  rw [Real.sq_sqrt (abs_nonneg x), abs_of_pos hx] at hc
  rw [cosineSquareRootAbsolute_zero, cosineSquareRootAbsolute, abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  rw [neg_div]
  linarith

/-- Bài 13(b): đạo hàm hữu hạn hai phía không tồn tại tại 0. -/
theorem cosineSquareRootAbsolute_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ cosineSquareRootAbsolute 0 := by
  intro hf
  have hd0 := cosineSquareRootAbsolute_derivative_zero_of_differentiable hf
  have hlim := calculus.Chapter04.Section01LimitExercises.difference_quotient_limit hf.hasDerivAt
  rw [hd0] at hlim
  have hq : Tendsto (fun n : ℕ ↦
      (cosineSquareRootAbsolute (1 / (n : ℝ)) - cosineSquareRootAbsolute 0) / (1 / (n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, sub_zero] using
      hlim.comp calculus.Chapter04.Section01LimitExercises.reciprocal_natural_tendsto_punctured_zero
  have hrec := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hconst : -1 / Real.pi ^ 2 < (0 : ℝ) :=
    div_neg_of_neg_of_pos (by norm_num) hpi
  have hlow := hq.eventually (Ioi_mem_nhds hconst)
  have hsmall := hrec.eventually (Iio_mem_nhds hpi)
  obtain ⟨n, hn, hlt, hbound⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hlow.and hsmall)).exists
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hupper := cosineSquareRootAbsolute_right_quotient_le (1 / (n : ℝ)) hx
    (show 1 / (n : ℝ) ≤ Real.pi ^ 2 from hbound.le)
  have horder : (-2 : ℝ) / Real.pi ^ 2 < -1 / Real.pi ^ 2 := by
    exact (div_lt_div_iff_of_pos_right hpi).mpr (by norm_num)
  exact (not_lt_of_ge hupper) (horder.trans (show -1 / Real.pi ^ 2 < _ from hlt))

end calculus.Chapter04.Section01LocalFurtherExercises
