import calculus.Chapter03.Section08
import calculus.Chapter03.Section08HeineCantor
import calculus.Chapter03.Section04ExercisesClassification
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# §3.8 — hai bài tập liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex`, Bài tập 3.8.3(a), dòng 3926, và Bài tập 3.8.3(h), dòng 3933.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08PositiveExercises
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08HeineCantor
open calculus.Chapter03.Section04
open calculus.Chapter03.Section04ExercisesClassification

/-- Bài tập 3.8.3(a): x sin(1/x) liên tục đều trên (0,1). -/
theorem oscillatingProduct_nonemptyUniformContinuousOn :
    NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x ↦ x * Real.sin (1 / x)) := by
  have hp : ContinuousOn oscillatingProductPatch univ :=
    (domainContinuousOn_iff_continuousOn (univ_nonempty : (univ : Set ℝ).Nonempty)).mp
      exercise03_product_continuous
  have hEq : oscillatingProductPatch = (fun x : ℝ ↦ x * Real.sin (1 / x)) := by
    funext x
    by_cases hx : x = 0 <;> simp [oscillatingProductPatch, hx]
  have hc : ContinuousOn (fun x : ℝ ↦ x * Real.sin (1 / x)) (Icc (0 : ℝ) 1) := by
    rw [← hEq]
    exact hp.mono (subset_univ _)
  have huc : NonemptyUniformContinuousOn (Icc (0 : ℝ) 1)
      (fun x ↦ x * Real.sin (1 / x)) :=
    continuousOn_closedInterval_nonemptyUniformContinuousOn (nonempty_Icc.mpr (by norm_num)) hc
  apply (nonemptyUniformContinuousOn_iff _ _).mpr
  exact ⟨nonempty_Ioo.mpr (by norm_num),
    ((nonemptyUniformContinuousOn_iff _ _).mp huc).2.mono Ioo_subset_Icc_self⟩


theorem expNegReciprocal_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-(1 / y)))
      (Real.exp (-(1 / x)) * (x ^ 2)⁻¹) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv hx.ne'
  have hn : HasDerivAt (fun y : ℝ ↦ -(1 / y)) ((x ^ 2)⁻¹) x := by
    simpa only [one_div, neg_neg] using HasDerivAt.fun_neg hi
  exact HasDerivAt.exp hn


theorem expNegReciprocal_derivative_norm_le_two {x : ℝ} (hx : 0 < x) :
    ‖Real.exp (-(1 / x)) * (x ^ 2)⁻¹‖ ≤ 2 := by
  have hp : (x⁻¹) ^ 2 / 2 ≤ Real.exp (x⁻¹) := by
    simpa using Real.pow_div_factorial_le_exp (x⁻¹) (inv_nonneg.mpr hx.le) 2
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(x⁻¹))).le
  have he : Real.exp (x⁻¹) * Real.exp (-(x⁻¹)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb : (x⁻¹) ^ 2 * Real.exp (-(x⁻¹)) ≤ 2 := by
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (sq_nonneg x)))]
  simpa only [one_div, inv_pow, mul_comm] using hb

/-- Bài tập 3.8.3(h): hàm liên tục đều trên (0,+∞), với δ=ε/2. -/
theorem expNegReciprocal_nonemptyUniformContinuousOn :
    NonemptyUniformContinuousOn (Ioi (0 : ℝ)) (fun x ↦ Real.exp (-(1 / x))) := by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  intro ε hε
  refine ⟨ε / 2, by linarith, ?_⟩
  intro u hu v hv huv
  have hd : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ ↦ Real.exp (-(1 / y)))
        (Real.exp (-(1 / x)) * (x ^ 2)⁻¹) (Ioi (0 : ℝ)) x :=
    fun x hx ↦ (expNegReciprocal_hasDerivAt hx).hasDerivWithinAt
  have hb : ∀ x ∈ Ioi (0 : ℝ), ‖Real.exp (-(1 / x)) * (x ^ 2)⁻¹‖ ≤ 2 :=
    fun x hx ↦ expNegReciprocal_derivative_norm_le_two hx
  have hm := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb hv hu
  have hab : |Real.exp (-(1 / u)) - Real.exp (-(1 / v))| ≤ 2 * |u - v| := by
    simpa only [Real.norm_eq_abs] using hm
  exact hab.trans_lt (by linarith)

end calculus.Chapter03.Section08PositiveExercises
