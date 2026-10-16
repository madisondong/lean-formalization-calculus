import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Abs
import calculus.Chapter04.Section01ElementaryDerivatives
import calculus.Chapter03.Section01Supplement
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Bài tập §4.1: định nghĩa và tính đạo hàm

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 435–483.
-/

set_option autoImplicit false

noncomputable section

namespace calculus.Chapter04.Section01Exercises

open Filter Set
open calculus.Chapter03.Section01Supplement (realCubeRoot)
open scoped Topology


theorem hasDerivAt_iff_difference_limit (f : ℝ → ℝ) (x d : ℝ) :
    HasDerivAt f d x ↔
      Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[≠] x) (𝓝 d) := by
  have hs : slope f x = fun y ↦ (f y - f x) / (y - x) := by
    funext y
    exact slope_def_field f x y
  rw [hasDerivAt_iff_tendsto_slope, hs]

/-- Bài 1(a): thương sai phân của hàm afin bằng hằng số `a`. -/
theorem affine_difference_limit (a b x : ℝ) :
    Tendsto (fun y : ℝ ↦ ((a * y + b) - (a * x + b)) / (y - x))
      (𝓝[≠] x) (𝓝 a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hy
  field_simp
  ring

/-- Bài 1(a): đạo hàm của `ax + b` bằng `a`. -/
theorem hasDerivAt_affine (a b x : ℝ) : HasDerivAt (fun y : ℝ ↦ a * y + b) a x :=
  (hasDerivAt_iff_difference_limit _ _ _).mpr (affine_difference_limit a b x)

/-- Bài 1(b): thương sai phân của `1/x` bằng `−1/(xy)` khi `x, y ≠ 0` và `x ≠ y`. -/
theorem reciprocal_difference_limit (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun y : ℝ ↦ (1 / y - 1 / x) / (y - x)) (𝓝[≠] x)
      (𝓝 (-(1 / x ^ 2))) := by
  have hid : Tendsto (fun y : ℝ ↦ y) (𝓝[≠] x) (𝓝 x) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun y : ℝ ↦ (-1 : ℝ) / (y * x)) (𝓝[≠] x)
      (𝓝 ((-1 : ℝ) / (x * x))) :=
    tendsto_const_nhds.div (hid.mul tendsto_const_nhds) (mul_ne_zero hx hx)
  have hfinal : Tendsto (fun y : ℝ ↦ (-1 : ℝ) / (y * x)) (𝓝[≠] x)
      (𝓝 (-(1 / x ^ 2))) := by simpa only [sq, neg_div] using hlim
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx] with y hy hy0
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hy
  field_simp
  ring

/-- Bài 1(b): đạo hàm của `1/x` tại `x ≠ 0`. -/
theorem hasDerivAt_reciprocal (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x :=
  (hasDerivAt_iff_difference_limit _ _ _).mpr (reciprocal_difference_limit x hx)

/-- Bài 1(c): giới hạn thương sai phân của căn bậc hai tại `x > 0`. -/
theorem sqrt_difference_limit (x : ℝ) (hx : 0 < x) :
    Tendsto (fun y : ℝ ↦ (√y - √x) / (y - x)) (𝓝[≠] x)
      (𝓝 (1 / (2 * √x))) := by
  have hid : Tendsto (fun y : ℝ ↦ y) (𝓝[≠] x) (𝓝 x) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun y : ℝ ↦ √y) (𝓝[≠] x) (𝓝 (√x)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hid
  have hp : 0 < √x := Real.sqrt_pos.mpr hx
  have hlim : Tendsto (fun y : ℝ ↦ 1 / (√y + √x)) (𝓝[≠] x)
      (𝓝 (1 / (√x + √x))) :=
    tendsto_const_nhds.div (hs.add tendsto_const_nhds)
      (show √x + √x ≠ 0 by positivity)
  have hfinal : Tendsto (fun y : ℝ ↦ 1 / (√y + √x)) (𝓝[≠] x)
      (𝓝 (1 / (2 * √x))) := by simpa only [two_mul] using hlim
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hx)] with y hy hy0
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hy
  have hsum : √y + √x ≠ 0 := by positivity
  have hsx := Real.sq_sqrt hx.le
  have hsy := Real.sq_sqrt (show 0 ≤ y from le_of_lt hy0)
  field_simp
  nlinarith

/-- Bài 1(c): đạo hàm của căn bậc hai tại `x > 0`. -/
theorem hasDerivAt_square_root (x : ℝ) (hx : 0 < x) :
    HasDerivAt Real.sqrt (1 / (2 * √x)) x :=
  (hasDerivAt_iff_difference_limit _ _ _).mpr (sqrt_difference_limit x hx)

/-- Bài 1(d): giới hạn thương sai phân của `√(1 + x²)`. -/
theorem sqrt_one_add_square_difference_limit (x : ℝ) :
    Tendsto (fun y : ℝ ↦ (√(1 + y ^ 2) - √(1 + x ^ 2)) / (y - x))
      (𝓝[≠] x) (𝓝 (x / √(1 + x ^ 2))) := by
  have hid : Tendsto (fun y : ℝ ↦ y) (𝓝[≠] x) (𝓝 x) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun y : ℝ ↦ √(1 + y ^ 2)) (𝓝[≠] x) (𝓝 (√(1 + x ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_const_nhds.add (hid.pow 2))
  have hxrad : 0 < 1 + x ^ 2 := by positivity
  have hp : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr hxrad
  have hlim : Tendsto (fun y : ℝ ↦ (y + x) / (√(1 + y ^ 2) + √(1 + x ^ 2)))
      (𝓝[≠] x) (𝓝 ((x + x) / (√(1 + x ^ 2) + √(1 + x ^ 2)))) :=
    (hid.add tendsto_const_nhds).div (hs.add tendsto_const_nhds)
      (show √(1 + x ^ 2) + √(1 + x ^ 2) ≠ 0 by positivity)
  have hcoeff : (x + x) / (√(1 + x ^ 2) + √(1 + x ^ 2)) = x / √(1 + x ^ 2) := by
    field_simp
  have hfinal : Tendsto (fun y : ℝ ↦ (y + x) / (√(1 + y ^ 2) + √(1 + x ^ 2)))
      (𝓝[≠] x) (𝓝 (x / √(1 + x ^ 2))) := by simpa only [hcoeff] using hlim
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hy
  have hsum : √(1 + y ^ 2) + √(1 + x ^ 2) ≠ 0 := by positivity
  have hsx := Real.sq_sqrt hxrad.le
  have hsy := Real.sq_sqrt (show 0 ≤ 1 + y ^ 2 by positivity)
  field_simp
  nlinarith

/-- Bài 1(d): đạo hàm của `√(1 + x²)`. -/
theorem hasDerivAt_sqrt_one_add_square (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ √(1 + y ^ 2)) (x / √(1 + x ^ 2)) x :=
  (hasDerivAt_iff_difference_limit _ _ _).mpr (sqrt_one_add_square_difference_limit x)

/-- Bài 1(e): giới hạn thương sai phân của logarit. -/
theorem logarithm_definition_solution (x : ℝ) (hx : 0 < x) :
    Tendsto (fun y : ℝ ↦ (Real.log y - Real.log x) / (y - x)) (𝓝[≠] x) (𝓝 (1 / x)) ∧
      HasDerivAt Real.log (1 / x) x := by
  have h : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log hx.ne'
  exact ⟨(hasDerivAt_iff_difference_limit _ _ _).mp h, h⟩

/-- Bài 1(f): giới hạn thương sai phân và giá trị đạo hàm của arctan. -/
theorem arctangent_definition_solution (x : ℝ) :
    Tendsto (fun y : ℝ ↦ (Real.arctan y - Real.arctan x) / (y - x))
      (𝓝[≠] x) (𝓝 (1 / (1 + x ^ 2))) ∧
      HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := by
  have h := Real.hasDerivAt_arctan x
  exact ⟨(hasDerivAt_iff_difference_limit _ _ _).mp h, h⟩

/-- Bài 1(g): giới hạn thương sai phân và đạo hàm của sinh. -/
theorem hyperbolic_sine_definition_solution (x : ℝ) :
    Tendsto (fun y : ℝ ↦ (Real.sinh y - Real.sinh x) / (y - x))
      (𝓝[≠] x) (𝓝 (Real.cosh x)) ∧ HasDerivAt Real.sinh (Real.cosh x) x := by
  have h := Real.hasDerivAt_sinh x
  exact ⟨(hasDerivAt_iff_difference_limit _ _ _).mp h, h⟩

/-- Bài 1(h): giới hạn thương sai phân và đạo hàm của cosh. -/
theorem hyperbolic_cosine_definition_solution (x : ℝ) :
    Tendsto (fun y : ℝ ↦ (Real.cosh y - Real.cosh x) / (y - x))
      (𝓝[≠] x) (𝓝 (Real.sinh x)) ∧ HasDerivAt Real.cosh (Real.sinh x) x := by
  have h := Real.hasDerivAt_cosh x
  exact ⟨(hasDerivAt_iff_difference_limit _ _ _).mp h, h⟩


theorem realCubeRoot_cubed (x : ℝ) : realCubeRoot x ^ 3 = x :=
  calculus.Chapter03.Section01Supplement.real_cube_root_cube x


theorem realCubeRoot_nonnegative_formula (x : ℝ) (hx : 0 ≤ x) :
    realCubeRoot x = x ^ (1 / 3 : ℝ) := by
  apply (calculus.Chapter03.Section01Supplement.real_cube_root_unique x _ _).symm
  simpa only [one_div, Nat.cast_ofNat] using
    (Real.rpow_inv_natCast_pow (n := 3) hx (by norm_num))


theorem realCubeRoot_negative_formula (x : ℝ) (hx : x < 0) :
    realCubeRoot x = -((-x) ^ (1 / 3 : ℝ)) := by
  apply (calculus.Chapter03.Section01Supplement.real_cube_root_unique x _ _).symm
  have hp : 0 ≤ -x := by linarith
  have hpow := Real.rpow_inv_natCast_pow (n := 3) hp (by norm_num)
  simp only [one_div, Nat.cast_ofNat] at hpow ⊢
  rw [neg_pow, hpow]
  norm_num


theorem realCubeRoot_eq_iff (x y : ℝ) : realCubeRoot x = y ↔ y ^ 3 = x := by
  constructor
  · intro h
    rw [← h]
    exact realCubeRoot_cubed x
  · intro h
    apply (show Odd (3 : ℕ) by decide).pow_injective
    change realCubeRoot x ^ 3 = y ^ 3
    rw [realCubeRoot_cubed, h]

/-- Bài 2: căn bậc ba thực không khả vi tại 0. -/
theorem realCubeRoot_not_differentiable_zero : ¬ DifferentiableAt ℝ realCubeRoot 0 := by
  intro h
  have hroot0 : realCubeRoot 0 = 0 := by
    rw [realCubeRoot_nonnegative_formula 0 (by norm_num)]
    norm_num
  have hc := h.hasDerivAt.fun_pow 3
  have heq : (fun x : ℝ ↦ realCubeRoot x ^ 3) = (fun x : ℝ ↦ x) :=
    funext realCubeRoot_cubed
  rw [heq, hroot0] at hc
  norm_num at hc
  have hcontra := hc.unique (hasDerivAt_id (0 : ℝ))
  norm_num at hcontra

/-- Bài 3(a): hàm chẵn khả vi trên ℝ có đạo hàm lẻ. -/
theorem odd_derivative_of_even {f : ℝ → ℝ} (_hf : Differentiable ℝ f) (he : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have heq : (fun y : ℝ ↦ f (-y)) = f := funext he
  have h := deriv_comp_neg f x
  rw [heq] at h
  linarith

/-- Bài 3(b): hàm lẻ khả vi trên ℝ có đạo hàm chẵn. -/
theorem even_derivative_of_odd {f : ℝ → ℝ} (hf : Differentiable ℝ f) (ho : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have heq : (fun y : ℝ ↦ f (-y)) = (fun y : ℝ ↦ -f y) := funext ho
  have h := deriv_comp_neg f x
  have hneg : HasDerivAt (fun y : ℝ ↦ -f y) (-deriv f x) x :=
    (hf x).hasDerivAt.neg.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hn : deriv (fun y : ℝ ↦ -f y) x = -deriv f x := hneg.deriv
  rw [heq, hn] at h
  linarith

/-- Bài 4(i): đạo hàm của tổng. -/
theorem derivative_sum_from_definition {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun y ↦ f y + g y) (deriv f x + deriv g x) x := by
  apply (hasDerivAt_iff_difference_limit _ _ _).mpr
  have hlim := ((hasDerivAt_iff_difference_limit _ _ _).mp hf.hasDerivAt).add
    ((hasDerivAt_iff_difference_limit _ _ _).mp hg.hasDerivAt)
  apply hlim.congr'
  exact Eventually.of_forall fun y ↦ by simp only [← add_div]; congr 1; ring

/-- Bài 4(ii): đạo hàm của tích với hằng số. -/
theorem derivative_scalar_from_definition {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    HasDerivAt (fun y ↦ c * f y) (c * deriv f x) x := by
  apply (hasDerivAt_iff_difference_limit _ _ _).mpr
  have hlim : Tendsto (fun y ↦ c * ((f y - f x) / (y - x))) (𝓝[≠] x)
      (𝓝 (c * deriv f x)) :=
    tendsto_const_nhds.mul ((hasDerivAt_iff_difference_limit _ _ _).mp hf.hasDerivAt)
  apply hlim.congr'
  exact Eventually.of_forall fun y ↦ by simp only [← mul_div_assoc, mul_sub]



theorem realCubeRoot_ne_zero (x : ℝ) (hx : x ≠ 0) : realCubeRoot x ≠ 0 := by
  intro h
  have hc := realCubeRoot_cubed x
  simp only [h, zero_pow (by decide : 3 ≠ 0)] at hc
  exact hx hc.symm


theorem realCubeRoot_differentiableAt (x : ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ realCubeRoot x := by
  rcases hx.lt_or_gt with hn | hp
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    have h := ((hasDerivAt_neg x).rpow_const (p := (1 / 3 : ℝ)) (Or.inl hneg)).neg
    apply (h.congr_of_eventuallyEq _).differentiableAt
    filter_upwards [Iio_mem_nhds hn] with y hy
    change realCubeRoot y = -((-y) ^ (1 / 3 : ℝ))
    exact realCubeRoot_negative_formula y (show y < 0 from hy)
  · have h := (hasDerivAt_id x).rpow_const (p := (1 / 3 : ℝ)) (Or.inl hx)
    apply (h.congr_of_eventuallyEq _).differentiableAt
    filter_upwards [Ioi_mem_nhds hp] with y hy
    change realCubeRoot y = y ^ (1 / 3 : ℝ)
    exact realCubeRoot_nonnegative_formula y (show 0 ≤ y from le_of_lt (show 0 < y from hy))


theorem hasDerivAt_realCubeRoot (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt realCubeRoot (1 / (3 * realCubeRoot x ^ 2)) x := by
  have hd := realCubeRoot_differentiableAt x hx
  have hc := hd.hasDerivAt.fun_pow 3
  have heq : (fun y : ℝ ↦ realCubeRoot y ^ 3) = (fun y : ℝ ↦ y) :=
    funext realCubeRoot_cubed
  rw [heq] at hc
  have hcoeff := hc.unique (hasDerivAt_id x)
  norm_num at hcoeff
  have hden : 3 * realCubeRoot x ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (realCubeRoot_ne_zero x hx))
  apply hd.hasDerivAt.congr_deriv
  apply (eq_div_iff hden).mpr
  nlinarith

/-- Căn bậc `k`: với bậc lẻ, căn cùng dấu với đối số; với bậc chẵn, lấy căn không âm của đối số không âm. -/
def realNthRoot (k : ℕ) (x : ℝ) : ℝ :=
  if Odd k then
    if 0 ≤ x then x ^ ((k : ℝ)⁻¹) else -((-x) ^ ((k : ℝ)⁻¹))
  else x ^ ((k : ℝ)⁻¹)


theorem odd_realNthRoot_power (k : ℕ) (hk : k ≠ 0) (ho : Odd k) (x : ℝ) :
    realNthRoot k x ^ k = x := by
  rw [realNthRoot, if_pos ho]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact Real.rpow_inv_natCast_pow hx hk
  · rw [if_neg hx, ho.neg_pow]
    have hp : 0 ≤ -x := by linarith
    rw [Real.rpow_inv_natCast_pow hp hk]
    ring


theorem even_realNthRoot_spec (k : ℕ) (hk : k ≠ 0) (he : Even k) (x : ℝ) (hx : 0 ≤ x) :
    realNthRoot k x ^ k = x ∧ 0 ≤ realNthRoot k x := by
  have hno : ¬ Odd k := Nat.not_odd_iff_even.mpr he
  rw [realNthRoot, if_neg hno]
  exact ⟨Real.rpow_inv_natCast_pow hx hk, Real.rpow_nonneg hx _⟩


theorem realNthRoot_of_power (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    realNthRoot k (x ^ k) = if Odd k then x else |x| := by
  by_cases ho : Odd k
  · rw [if_pos ho]
    apply ho.pow_injective
    change realNthRoot k (x ^ k) ^ k = x ^ k
    exact odd_realNthRoot_power k hk ho (x ^ k)
  · rw [if_neg ho, realNthRoot, if_neg ho]
    have he : Even k := Nat.not_odd_iff_even.mp ho
    rw [← he.pow_abs x]
    exact Real.pow_rpow_inv_natCast (abs_nonneg x) hk

/-- Bài 6(b): hai thừa số dưới căn đều là `1 − x`. -/
theorem nthRoot_product_same_base (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℝ) :
    realNthRoot (m + n) ((1 - x) ^ m * (1 - x) ^ n) =
      if Odd (m + n) then 1 - x else |1 - x| := by
  rw [← pow_add]
  exact realNthRoot_of_power (m + n) (by omega) (1 - x)

/-- Bài 6(b), bậc lẻ: biểu thức bằng `1 − x` trên toàn ℝ. -/
theorem hasDerivAt_nthRoot_product_odd (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ho : Odd (m + n)) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n)) (-1) x := by
  apply ((hasDerivAt_id x).const_sub 1).congr_of_eventuallyEq
  exact Eventually.of_forall fun y ↦ by
    change realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n) = 1 - y
    rw [nthRoot_product_same_base m n hm hn, if_pos ho]

/-- Bài 6(b), bậc chẵn: đạo hàm bằng −1 khi `x < 1`. -/
theorem hasDerivAt_nthRoot_product_even_left (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (he : Even (m + n)) (x : ℝ) (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n)) (-1) x := by
  apply ((hasDerivAt_id x).const_sub 1).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  change y < 1 at hy
  change realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n) = 1 - y
  rw [nthRoot_product_same_base m n hm hn, if_neg (Nat.not_odd_iff_even.mpr he),
    abs_of_pos (show 0 < 1 - y by linarith)]

/-- Bài 6(b), bậc chẵn: đạo hàm bằng 1 khi `x > 1`. -/
theorem hasDerivAt_nthRoot_product_even_right (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (he : Even (m + n)) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun y : ℝ ↦ realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n)) 1 x := by
  apply ((hasDerivAt_id x).sub_const 1).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  change 1 < y at hy
  change realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n) = y - 1
  rw [nthRoot_product_same_base m n hm hn, if_neg (Nat.not_odd_iff_even.mpr he),
    abs_of_neg (show 1 - y < 0 by linarith)]
  ring


theorem abs_one_sub_not_differentiable_one :
    ¬ DifferentiableAt ℝ (fun y : ℝ ↦ |1 - y|) 1 := by
  intro h
  have hi : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) 0 := (hasDerivAt_id 0).const_sub 1
  have hc := h.hasDerivAt.comp_of_eq 0 hi (by norm_num)
  have hf : (fun y : ℝ ↦ |1 - (1 - y)|) = (abs : ℝ → ℝ) := by
    funext y
    congr 1
    ring
  have hd : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    simpa only [Function.comp_def, hf] using hc.differentiableAt
  exact not_differentiableAt_abs_zero hd

/-- Bài 6(b), bậc chẵn: hàm xác định tại 1 nhưng không khả vi tại đó. -/
theorem nthRoot_product_even_not_differentiable_one (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (he : Even (m + n)) :
    ¬ DifferentiableAt ℝ
      (fun y : ℝ ↦ realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n)) 1 := by
  have hf : (fun y : ℝ ↦ realNthRoot (m + n) ((1 - y) ^ m * (1 - y) ^ n)) =
      (fun y : ℝ ↦ |1 - y|) := by
    funext y
    rw [nthRoot_product_same_base m n hm hn, if_neg (Nat.not_odd_iff_even.mpr he)]
  rw [hf]
  exact abs_one_sub_not_differentiable_one


open calculus.Chapter04.Section01ElementaryDerivatives


theorem hasDerivAt_cubic_ratio (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (fun y : ℝ ↦ (1 + y ^ 3) / (1 - y ^ 3))
      (6 * x ^ 2 / (1 - x ^ 3) ^ 2) x := by
  have hden : 1 - x ^ 3 ≠ 0 := by
    intro h
    have hp : x ^ 3 = 1 ^ 3 := by nlinarith
    exact hx ((show Odd (3 : ℕ) by decide).pow_injective hp)
  have hc := (hasDerivAt_id x).fun_pow 3
  have h := (hc.const_add 1).div (hc.const_sub 1) hden
  apply h.congr_deriv
  congr 1
  norm_num
  ring

/-- Bài 6(a): đạo hàm căn bậc ba thực của `(1+x³)/(1−x³)` trên `x ≠ ±1`. -/
theorem hasDerivAt_cubeRoot_cubic_ratio (x : ℝ) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    HasDerivAt (fun y : ℝ ↦ realCubeRoot ((1 + y ^ 3) / (1 - y ^ 3)))
      (2 * x ^ 2 / ((1 - x ^ 3) ^ 2 * realCubeRoot ((1 + x ^ 3) / (1 - x ^ 3)) ^ 2)) x := by
  have hnum : 1 + x ^ 3 ≠ 0 := by
    intro h
    have hp : x ^ 3 = (-1) ^ 3 := by nlinarith
    exact hxm1 ((show Odd (3 : ℕ) by decide).pow_injective hp)
  have hden : 1 - x ^ 3 ≠ 0 := by
    intro h
    have hp : x ^ 3 = 1 ^ 3 := by nlinarith
    exact hx1 ((show Odd (3 : ℕ) by decide).pow_injective hp)
  have hrat : (1 + x ^ 3) / (1 - x ^ 3) ≠ 0 := div_ne_zero hnum hden
  have h := (hasDerivAt_realCubeRoot _ hrat).comp x (hasDerivAt_cubic_ratio x hx1)
  apply h.congr_deriv
  field_simp
  ring

/-- Bài 6(a): điểm −1 thuộc miền xác định, nhưng hàm không có đạo hàm hữu hạn tại đó. -/
theorem cubeRoot_cubic_ratio_not_differentiable_neg_one :
    ¬ DifferentiableAt ℝ (fun y : ℝ ↦ realCubeRoot ((1 + y ^ 3) / (1 - y ^ 3))) (-1) := by
  intro h
  have hzero : realCubeRoot ((1 + (-1 : ℝ) ^ 3) / (1 - (-1 : ℝ) ^ 3)) = 0 := by
    apply (realCubeRoot_eq_iff _ _).mpr
    norm_num
  have hc := h.hasDerivAt.fun_pow 3
  have heq : (fun y : ℝ ↦ realCubeRoot ((1 + y ^ 3) / (1 - y ^ 3)) ^ 3) =
      (fun y : ℝ ↦ (1 + y ^ 3) / (1 - y ^ 3)) := by
    funext y
    exact realCubeRoot_cubed _
  rw [heq, hzero] at hc
  norm_num at hc
  have hr := hasDerivAt_cubic_ratio (-1) (by norm_num)
  norm_num at hr
  have hfalse := hc.unique hr
  norm_num at hfalse

/-- Bài 6(c): đạo hàm logarit có cơ số biến, với `x > 0`, `x ≠ 1`. -/
theorem hasDerivAt_variable_base_logarithm (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt (fun y : ℝ ↦ Real.logb y 2) (-Real.log 2 / (x * (Real.log x) ^ 2)) x := by
  have hn := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have h := (hasDerivAt_const x (Real.log 2)).div (Real.hasDerivAt_log hx.ne') hn
  have hf : (fun y : ℝ ↦ Real.logb y 2) = (fun y : ℝ ↦ Real.log 2 / Real.log y) := by
    funext y
    rfl
  rw [hf]
  apply h.congr_deriv
  field_simp
  ring

/-- Bài 6(d): đạo hàm tích của đa thức và arctan trên toàn ℝ. -/
theorem hasDerivAt_polynomial_arctangent (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 2 * y ^ 5 * Real.arctan (y + 3))
      (10 * x ^ 4 * Real.arctan (x + 3) + 2 * x ^ 5 / (1 + (x + 3) ^ 2)) x := by
  have hp := ((hasDerivAt_id x).fun_pow 5).const_mul (2 : ℝ)
  have ht := (Real.hasDerivAt_arctan (x + 3)).comp x ((hasDerivAt_id x).add_const 3)
  apply (hp.mul ht).congr_deriv
  norm_num
  ring

/-- Bài 6(e): đạo hàm của `arccos(1/|x|)` trên `|x| > 1`. -/
theorem hasDerivAt_arccos_reciprocal_abs (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt (fun y : ℝ ↦ Real.arccos (1 / |y|)) (1 / (x * √(x ^ 2 - 1))) x := by
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hx
    linarith
  rcases hx0.lt_or_gt with hn | hp
  · have habs : 1 < |-x| := by simpa only [abs_neg] using hx
    have h := (hasDerivAt_arcsecant (-x) habs).comp x (hasDerivAt_neg x)
    have heq : (fun y : ℝ ↦ Real.arccos (1 / |y|)) =ᶠ[𝓝 x] (fun y : ℝ ↦ arcsec (-y)) := by
      filter_upwards [Iio_mem_nhds hn] with y hy
      rw [abs_of_neg (show y < 0 from hy)]
      rfl
    have hh := h.congr_of_eventuallyEq heq
    apply hh.congr_deriv
    simp only [abs_neg, abs_of_neg hn, neg_sq]
    field_simp
  · have h := hasDerivAt_arcsecant x hx
    have heq : (fun y : ℝ ↦ Real.arccos (1 / |y|)) =ᶠ[𝓝 x] arcsec := by
      filter_upwards [Ioi_mem_nhds hp] with y hy
      rw [abs_of_pos (show 0 < y from hy)]
      rfl
    apply (h.congr_of_eventuallyEq heq).congr_deriv
    rw [abs_of_pos hp]

/-- Bài 6(f): đạo hàm của sinh hợp với một đa thức bậc hai. -/
theorem hasDerivAt_hyperbolic_sine_quadratic (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.sinh (3 * y ^ 2 - 2))
      (6 * x * Real.cosh (3 * x ^ 2 - 2)) x := by
  have hp := (((hasDerivAt_id x).fun_pow 2).const_mul (3 : ℝ)).sub_const 2
  apply ((Real.hasDerivAt_sinh (3 * x ^ 2 - 2)).comp x hp).congr_deriv
  norm_num
  ring

/-- Bài 6(g): đạo hàm của `log(arcosh x)` trên `x > 1`. -/
theorem hasDerivAt_logarithm_arcosh (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun y : ℝ ↦ Real.log (Real.arcosh y))
      (1 / (Real.arcosh x * √(x ^ 2 - 1))) x := by
  have hp := Real.arcosh_pos hx
  have h := (hasDerivAt_inverse_hyperbolic_cosine x hx).log hp.ne'
  apply h.congr_deriv
  field_simp

/-- Bài 6(h): đạo hàm trên miền mở `0 < x/a < 1`, với mọi dấu của `a`. -/
theorem hasDerivAt_scaled_arsech_minus_sqrt (a x : ℝ) (ha : a ≠ 0)
    (hx0 : 0 < x / a) (hx1 : x / a < 1) :
    HasDerivAt (fun y : ℝ ↦ a * arsech (y / a) - √(a ^ 2 - y ^ 2))
      (-(1 / ((x / a) * √(1 - (x / a) ^ 2))) + x / √(a ^ 2 - x ^ 2)) x := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hunit : (x / a) ^ 2 < 1 := by nlinarith
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hmul := mul_pos (show 0 < 1 - (x / a) ^ 2 by linarith) ha2
    have hid : (1 - (x / a) ^ 2) * a ^ 2 = a ^ 2 - x ^ 2 := by field_simp
    rwa [hid] at hmul
  have ht := (hasDerivAt_inverse_hyperbolic_secant (x / a) hx0 hx1).comp x
    ((hasDerivAt_id x).div_const a)
  have hp := ((hasDerivAt_id x).fun_pow 2).const_sub (a ^ 2)
  have hs := hp.sqrt hrad.ne'
  have h := (ht.const_mul a).sub hs
  apply h.congr_deriv
  norm_num
  field_simp
  ring

/-- Bài 6(i): đạo hàm trên miền `2 < x < 4`. -/
theorem hasDerivAt_square_root_arcsecant_product (x : ℝ) (hx : x ∈ Ioo (2 : ℝ) 4) :
    HasDerivAt (fun y : ℝ ↦ (√(y ^ 2 - 4) - 2) * arcsec (y / 2))
      (x / √(x ^ 2 - 4) * arcsec (x / 2) +
        (√(x ^ 2 - 4) - 2) / (x * √((x / 2) ^ 2 - 1))) x := by
  have hp : 0 < x ^ 2 - 4 := by nlinarith [hx.1]
  have hx2 : 1 < |x / 2| := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
  have hs := (((hasDerivAt_id x).fun_pow 2).sub_const 4).sqrt hp.ne'
  have ht := (hasDerivAt_arcsecant (x / 2) hx2).comp x ((hasDerivAt_id x).div_const 2)
  apply ((hs.sub_const 2).mul ht).congr_deriv
  norm_num
  rw [abs_of_pos (by linarith [hx.1] : 0 < x / 2)]
  field_simp

/-- Bài 6(j): đạo hàm của biểu thức logarit trên ℝ. -/
theorem hasDerivAt_logarithm_radical_sum (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y + √(1 + y ^ 2))) (1 / √(1 + x ^ 2)) x := by
  have hf : (fun y : ℝ ↦ Real.log (y + √(1 + y ^ 2))) = Real.arsinh := by
    funext y
    rw [arsinh_eq_source_formula, add_comm (1 : ℝ) (y ^ 2)]
  rw [hf]
  simpa only [add_comm (1 : ℝ) (x ^ 2)] using hasDerivAt_inverse_hyperbolic_sine x

/-- Bài 6(l): đạo hàm trên miền `x > 0` của logarit. -/
theorem hasDerivAt_arctangent_square_logarithm (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ Real.arctan (y ^ 2 + Real.log y))
      ((2 * x + 1 / x) / (1 + (x ^ 2 + Real.log x) ^ 2)) x := by
  have hp := ((hasDerivAt_id x).fun_pow 2).add (Real.hasDerivAt_log hx.ne')
  have hsum : HasDerivAt (fun y : ℝ ↦ y ^ 2 + Real.log y) (2 * x + x⁻¹) x := by
    apply (hp.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
    norm_num
  apply ((Real.hasDerivAt_arctan (x ^ 2 + Real.log x)).comp x hsum).congr_deriv
  simp only [one_div]
  ring

/-- Bài 6(m): đạo hàm logarit của `x^x`, với số mũ biến thiên. -/
theorem hasDerivAt_nested_variable_power (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ y ^ (Real.sin (y ^ y)))
      (x ^ (Real.sin (x ^ x)) *
        (Real.sin (x ^ x) / x + Real.log x * Real.cos (x ^ x) * x ^ x * (Real.log x + 1))) x := by
  have hid := hasDerivAt_id x
  have hxx : HasDerivAt (fun y : ℝ ↦ y ^ y)
      (x * x ^ (x - 1) + x ^ x * Real.log x) x := by
    simpa only [id_eq, one_mul] using hid.rpow hid hx
  have hsin := (Real.hasDerivAt_sin (x ^ x)).comp x (h := fun y : ℝ ↦ y ^ y) hxx
  have h := hid.rpow hsin hx
  apply h.congr_deriv
  simp only [id_eq, Function.comp_apply, one_mul]
  rw [Real.rpow_sub_one hx.ne', Real.rpow_sub_one hx.ne']
  field_simp
  ring



theorem power_sine_mem_tangent_domain (x : ℝ) (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    x ^ (Real.sin x) ∈ Ioo 0 (Real.pi / 2) := by
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  refine ⟨Real.rpow_pos_of_pos hx.1 _, ?_⟩
  by_cases hx1 : x < 1
  · exact (Real.rpow_lt_one hx.1.le hx1 hsin).trans_le Real.one_le_pi_div_two
  · have hxge : 1 ≤ x := le_of_not_gt hx1
    have hle : x ^ (Real.sin x) ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hxge (Real.sin_le_one x)
    exact hle.trans_lt hx.2

/-- Bài 6(k), cách đọc 1: đạo hàm của `(tan x)^(sin x)` trên `0 < x < π/2`. -/
theorem hasDerivAt_tangent_power_sine (x : ℝ) (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun y : ℝ ↦ (Real.tan y) ^ (Real.sin y))
      ((Real.tan x) ^ (Real.sin x) *
        (Real.cos x * Real.log (Real.tan x) + Real.sin x / (Real.tan x * Real.cos x ^ 2))) x := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have htan : 0 < Real.tan x := Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2
  have ht := (tangent_derivative_forms x hcos.ne').1
  have h := ht.rpow (Real.hasDerivAt_sin x) htan
  apply h.congr_deriv
  rw [Real.rpow_sub_one htan.ne']
  field_simp
  ring

/-- Bài 6(k), cách đọc 2: đạo hàm của `tan(x^(sin x))` trên `0 < x < π/2`. -/
theorem hasDerivAt_tangent_of_power_sine (x : ℝ) (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun y : ℝ ↦ Real.tan (y ^ (Real.sin y)))
      (x ^ (Real.sin x) * (Real.cos x * Real.log x + Real.sin x / x) /
        Real.cos (x ^ (Real.sin x)) ^ 2) x := by
  have hinner := power_sine_mem_tangent_domain x hx
  have hcos : 0 < Real.cos (x ^ (Real.sin x)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hinner.1, Real.pi_pos], hinner.2⟩
  have hp : HasDerivAt (fun y : ℝ ↦ y ^ (Real.sin y))
      (Real.sin x * x ^ (Real.sin x - 1) + Real.cos x * x ^ (Real.sin x) * Real.log x) x := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id x).rpow (Real.hasDerivAt_sin x) hx.1
  have ht := (tangent_derivative_forms (x ^ (Real.sin x)) hcos.ne').1
  apply (ht.comp x (h := fun y : ℝ ↦ y ^ (Real.sin y)) hp).congr_deriv
  rw [Real.rpow_sub_one hx.1.ne']
  field_simp
  ring

end calculus.Chapter04.Section01Exercises
