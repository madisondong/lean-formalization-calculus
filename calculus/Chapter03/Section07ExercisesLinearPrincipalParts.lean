import calculus.Chapter03.Section07ExercisesDerivativeRatios
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# §3.7 — ba giới hạn từ phần chính tuyến tính

Nguồn: Bài tập 3.7.11(a,o,r), `Ch3_gioihanhamso.tex`, dòng 3680, 3683, 3697, 3700.
-/

set_option autoImplicit false

open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesLinearPrincipalParts

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07ExercisesDerivativeRatios


def polynomialSineRatioDomain : Set ℝ := {x | 2 * x + Real.sin x ^ 8 ≠ 0}


def squareRootSineRatioDomain : Set ℝ :=
  {x | 0 ≤ x + 2 ∧ Real.sin (x ^ 3) + 2 * x ≠ 0}


def trigonometricLogRatioDomain : Set ℝ :=
  {x | 0 < 1 + 3 * x + Real.sin x ^ 2 ∧
    Real.log (1 + 3 * x + Real.sin x ^ 2) + x * Real.exp x ≠ 0}

/-- Bài tập 3.7.11(a): (x+x⁴+x⁸)/(2x+sin⁸x) → 1/2. -/
theorem polynomial_sine_ratio_at_zero :
    DomainLimit polynomialSineRatioDomain
      (fun x ↦ (x + x ^ 4 + x ^ 8) / (2 * x + Real.sin x ^ 8)) 0 (1 / 2) := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hf : HasDerivAt (fun x : ℝ ↦ x + x ^ 4 + x ^ 8) 1 0 := by
    convert! (hi.add (hi.pow 4)).add (hi.pow 8) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ 2 * x + Real.sin x ^ 8) 2 0 := by
    convert! (hi.const_mul 2).add (hi.sin.pow 8) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have ha : AccumulationPointOf polynomialSineRatioDomain 0 :=
    derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  exact domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Bài tập 3.7.11(o): giới hạn bằng 1/(4√2). -/
theorem sqrt_sine_ratio_at_zero :
    DomainLimit squareRootSineRatioDomain
      (fun x ↦ (Real.sin (Real.sqrt (x + 2) - Real.sqrt 2) + x ^ 2 + 3 * x ^ 2) /
        (Real.sin (x ^ 3) + 2 * x)) 0 (1 / (4 * Real.sqrt 2)) := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hs : HasDerivAt (fun x : ℝ ↦ Real.sqrt (x + 2) - Real.sqrt 2)
      (1 / (2 * Real.sqrt 2)) 0 := by
    simpa only [id_eq, zero_add] using
      ((hi.add_const 2).sqrt (by norm_num : (0 : ℝ) + 2 ≠ 0)).sub_const (Real.sqrt 2)
  have hf : HasDerivAt
      (fun x : ℝ ↦ Real.sin (Real.sqrt (x + 2) - Real.sqrt 2) + x ^ 2 + 3 * x ^ 2)
      (1 / (2 * Real.sqrt 2)) 0 := by
    convert! (hs.sin.add (hi.pow 2)).add ((hi.pow 2).const_mul 3) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ Real.sin (x ^ 3) + 2 * x) 2 0 := by
    convert! (hi.pow 3).sin.add (hi.const_mul 2) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have ha0 := derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  have ha : AccumulationPointOf squareRootSineRatioDomain 0 :=
    accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi ha0 (by norm_num : (-2 : ℝ) < 0)) (by
        intro x hx
        exact ⟨by have hxl : (-2 : ℝ) < x := hx.2; linarith, hx.1⟩)
  have hf' : (1 : ℝ) / (2 * Real.sqrt 2) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne')
  have ht := domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by norm_num) (by norm_num) hf' (by norm_num)
  simpa only [div_div, show (2 * Real.sqrt 2) * 2 = 4 * Real.sqrt 2 by ring] using ht

/-- Bài tập 3.7.11(r): giới hạn bằng 2. -/
theorem trigonometric_log_ratio_at_zero :
    DomainLimit trigonometricLogRatioDomain
      (fun x ↦ (Real.sin (2 * x) + 2 * Real.arctan (3 * x) + 3 * x ^ 2) /
        (Real.log (1 + 3 * x + Real.sin x ^ 2) + x * Real.exp x)) 0 2 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hf : HasDerivAt
      (fun x : ℝ ↦ Real.sin (2 * x) + 2 * Real.arctan (3 * x) + 3 * x ^ 2) 8 0 := by
    convert! ((hi.const_mul 2).sin.add ((hi.const_mul 3).arctan.const_mul 2)).add
      ((hi.pow 2).const_mul 3) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + 3 * x + Real.sin x ^ 2) 3 0 := by
    convert! ((hi.const_mul 3).const_add 1).add (hi.sin.pow 2) using 1
    norm_num [id_eq, Pi.add_apply, Pi.pow_apply]
  have hg : HasDerivAt
      (fun x : ℝ ↦ Real.log (1 + 3 * x + Real.sin x ^ 2) + x * Real.exp x) 4 0 := by
    convert! (harg.log (by norm_num : (1 : ℝ) + 3 * 0 + Real.sin 0 ^ 2 ≠ 0)).add
      (hi.mul (Real.hasDerivAt_exp 0)) using 1
    norm_num [id_eq, Pi.add_apply]
  have ha0 := derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  have ha : AccumulationPointOf trigonometricLogRatioDomain 0 :=
    accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi ha0 (by norm_num : (-1 / 3 : ℝ) < 0)) (by
        intro x hx
        refine ⟨?_, hx.1⟩
        have hxl : (-1 / 3 : ℝ) < x := hx.2
        nlinarith [sq_nonneg (Real.sin x)])
  have ht := domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at ht
  exact ht

end calculus.Chapter03.Section07ExercisesLinearPrincipalParts
