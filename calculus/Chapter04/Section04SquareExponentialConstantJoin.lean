import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 6(a): khả vi tại hai điểm ghép ±1

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1728–1736. Nhánh trong nhận cả hai điểm `±1`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04SquareExponentialConstantJoin

def squareExponentialInterior (x : ℝ) : ℝ := x ^ 2 * Real.exp (-(x ^ 2))
def squareExponentialConstantJoin (x : ℝ) : ℝ :=
  if |x| ≤ 1 then x ^ 2 * Real.exp (-(x ^ 2)) else 1 / Real.exp 1
def squareExponentialConstantJoinDerivative (x : ℝ) : ℝ :=
  if |x| ≤ 1 then 2 * x * (1 - x ^ 2) * Real.exp (-(x ^ 2)) else 0


theorem switch_branches_hasDerivAt {p : ℝ → Prop} [DecidablePred p]
    {f g : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a) (hg : HasDerivAt g d a)
    (hv : f a = g a) : HasDerivAt (fun x ↦ if p x then f x else g x) d a := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht := hf.tendsto_slope.if' (p := p) hg.tendsto_slope
  have hcenter : (if p a then f a else g a) = f a := by
    by_cases hp : p a
    · exact if_pos hp
    · exact (if_neg hp).trans hv.symm
  apply ht.congr'
  filter_upwards with x
  simp only [slope_def_field, hcenter]
  by_cases hx : p x
  · simp only [if_pos hx]
  · simp only [if_neg hx, hv]

theorem squareExponentialInterior_hasDerivAt (x : ℝ) :
    HasDerivAt squareExponentialInterior
      (2 * x * (1 - x ^ 2) * Real.exp (-(x ^ 2))) x := by
  have hp : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa using! (hasDerivAt_id x).fun_pow 2
  have ht := hp.fun_mul hp.neg.exp
  apply ht.congr_deriv
  dsimp only [Pi.neg_apply]
  ring

theorem squareExponentialInterior_boundary_value {x : ℝ} (hx : |x| = 1) :
    squareExponentialInterior x = 1 / Real.exp 1 := by
  have hx2 : x ^ 2 = 1 := by nlinarith [sq_abs x]
  simp only [squareExponentialInterior, hx2, one_mul, Real.exp_neg, one_div]

theorem squareExponentialInterior_boundary_hasDerivAt {x : ℝ} (hx : |x| = 1) :
    HasDerivAt squareExponentialInterior 0 x := by
  have hx2 : x ^ 2 = 1 := by nlinarith [sq_abs x]
  simpa only [hx2, sub_self, mul_zero, zero_mul] using squareExponentialInterior_hasDerivAt x

theorem source_square_exponential_join_hasDerivAt (x : ℝ) :
    HasDerivAt squareExponentialConstantJoin (squareExponentialConstantJoinDerivative x) x := by
  rcases lt_trichotomy |x| 1 with hx | hx | hx
  · have ht := squareExponentialInterior_hasDerivAt x
    have he : squareExponentialConstantJoin =ᶠ[𝓝 x] squareExponentialInterior := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
      exact if_pos hy.le
    simpa only [squareExponentialConstantJoinDerivative, if_pos hx.le] using
      ht.congr_of_eventuallyEq he
  · have ht := switch_branches_hasDerivAt
      (p := fun y : ℝ ↦ |y| ≤ 1) (squareExponentialInterior_boundary_hasDerivAt hx)
      (hasDerivAt_const x (1 / Real.exp 1)) (squareExponentialInterior_boundary_value hx)
    have hx2 : x ^ 2 = 1 := by nlinarith [sq_abs x]
    simpa only [squareExponentialConstantJoin, squareExponentialInterior,
      squareExponentialConstantJoinDerivative, hx, hx2, if_pos le_rfl, sub_self, mul_zero, zero_mul] using! ht
  · have he : squareExponentialConstantJoin =ᶠ[𝓝 x] (fun _ : ℝ ↦ 1 / Real.exp 1) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
      exact if_neg (not_le.mpr hy)
    simpa only [squareExponentialConstantJoinDerivative, if_neg (not_le.mpr hx)] using
      (hasDerivAt_const x (1 / Real.exp 1)).congr_of_eventuallyEq he

theorem source_square_exponential_join_differentiable :
    Differentiable ℝ squareExponentialConstantJoin :=
  fun x ↦ (source_square_exponential_join_hasDerivAt x).differentiableAt

theorem source_square_exponential_join_derivative (x : ℝ) :
    deriv squareExponentialConstantJoin x = squareExponentialConstantJoinDerivative x :=
  (source_square_exponential_join_hasDerivAt x).deriv

theorem source_square_exponential_join_boundary_derivatives :
    deriv squareExponentialConstantJoin (-1) = 0 ∧ deriv squareExponentialConstantJoin 1 = 0 := by
  simp only [source_square_exponential_join_derivative, squareExponentialConstantJoinDerivative]
  norm_num

end calculus.Chapter04.Section04SquareExponentialConstantJoin
