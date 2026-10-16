import calculus.Chapter04.Section01Geometry
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.1 — Bài 8: tiếp tuyến của hai đường cong ẩn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 495–496, Bài 4.1.8(a,b).
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter04.Section01ImplicitTangentExercises

open calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section01Geometry


noncomputable def implicitLinearDerivative (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ


theorem implicit_linear_y_invertible (a b : ℝ) (hb : b ≠ 0) :
    (implicitLinearDerivative a b ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  let inverseMap : ℝ →L[ℝ] ℝ := b⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := inverseMap)
  · apply ContinuousLinearMap.ext
    intro t
    simp [implicitLinearDerivative, inverseMap, hb]
  · apply ContinuousLinearMap.ext
    intro t
    simp [implicitLinearDerivative, inverseMap, hb]


theorem implicit_local_graph {F : ℝ × ℝ → ℝ} {x₀ y₀ a b : ℝ}
    (hF : HasStrictFDerivAt F (implicitLinearDerivative a b) (x₀, y₀))
    (hzero : F (x₀, y₀) = 0) (hb : b ≠ 0) :
    ∃ g : ℝ → ℝ, g x₀ = y₀ ∧
      (∀ᶠ p in 𝓝 (x₀, y₀), F p = 0 ↔ g p.1 = p.2) ∧
      (∀ᶠ x in 𝓝 x₀, F (x, g x) = 0) ∧ HasDerivAt g (-a / b) x₀ := by
  have hinv := implicit_linear_y_invertible a b hb
  let g := hF.implicitFunctionOfProdDomain hinv
  have hpoint : g x₀ = y₀ :=
    (hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hcurve : ∀ᶠ p in 𝓝 (x₀, y₀), F p = 0 ↔ g p.1 = p.2 := by
    simpa only [hzero] using hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have hgraph : ∀ᶠ x in 𝓝 x₀, F (x, g x) = 0 := by
    simpa only [hzero] using hF.eventually_apply_implicitFunctionOfProdDomain hinv
  have hinverse :
      (implicitLinearDerivative a b ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse a = a / b := by
    apply hinv.inverse_apply_eq.mpr
    simpa [implicitLinearDerivative] using (mul_div_cancel₀ a hb).symm
  have hderiv := (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
  refine ⟨g, hpoint, hcurve, hgraph, hderiv.congr_deriv ?_⟩
  change -((implicitLinearDerivative a b ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse
    ((implicitLinearDerivative a b ∘L ContinuousLinearMap.inl ℝ ℝ ℝ) 1)) = -a / b
  have hleft : (implicitLinearDerivative a b ∘L ContinuousLinearMap.inl ℝ ℝ ℝ) 1 = a := by
    simp [implicitLinearDerivative]
  rw [hleft, hinverse, neg_div]

/-- Bài 8(a): phương trình đường cong ẩn dưới dạng tập mức 0. -/
noncomputable def firstImplicitCurveEquation (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 * (p.1 ^ 2 + p.2 ^ 2) - p.2 ^ 2

/-- Bài 8(b): phương trình đường cong ẩn dưới dạng tập mức 0. -/
noncomputable def secondImplicitCurveEquation (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) ^ 2 - 4 * p.1 ^ 2 * p.2

/-- Bài 8(a): hoành độ tiếp điểm bằng `√2/2`. -/
noncomputable def firstContactAbscissa : ℝ := Real.sqrt 2 / 2

theorem first_curve_source_equation (p : ℝ × ℝ) :
    firstImplicitCurveEquation p = 0 ↔ p.1 ^ 2 * (p.1 ^ 2 + p.2 ^ 2) = p.2 ^ 2 :=
  sub_eq_zero

theorem second_curve_source_equation (p : ℝ × ℝ) :
    secondImplicitCurveEquation p = 0 ↔ (p.1 ^ 2 + p.2 ^ 2) ^ 2 = 4 * p.1 ^ 2 * p.2 :=
  sub_eq_zero

theorem first_contact_abscissa_square : firstContactAbscissa ^ 2 = (1 / 2 : ℝ) := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [firstContactAbscissa]
  nlinarith

theorem first_contact_abscissa_pos : 0 < firstContactAbscissa :=
  div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)

theorem first_contact_abscissa_ne_zero : firstContactAbscissa ≠ 0 := ne_of_gt first_contact_abscissa_pos

theorem first_curve_contact : firstImplicitCurveEquation (firstContactAbscissa, firstContactAbscissa) = 0 := by
  simp [firstImplicitCurveEquation, first_contact_abscissa_square]
  norm_num

theorem second_curve_contact : secondImplicitCurveEquation (1, 1) = 0 := by
  norm_num [secondImplicitCurveEquation]


theorem first_curve_equation_hasStrictFDerivAt :
    HasStrictFDerivAt firstImplicitCurveEquation
      (implicitLinearDerivative (3 * firstContactAbscissa) (-firstContactAbscissa))
      (firstContactAbscissa, firstContactAbscissa) := by
  have hx : HasStrictFDerivAt (fun p : ℝ × ℝ ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (firstContactAbscissa, firstContactAbscissa) := hasStrictFDerivAt_fst
  have hy : HasStrictFDerivAt (fun p : ℝ × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (firstContactAbscissa, firstContactAbscissa) := hasStrictFDerivAt_snd
  have h := ((hx.pow 2).fun_mul ((hx.pow 2).fun_add (hy.pow 2))).fun_sub (hy.pow 2)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp [implicitLinearDerivative, first_contact_abscissa_square, smul_eq_mul, nsmul_eq_mul]
  ring


theorem second_curve_equation_hasStrictFDerivAt :
    HasStrictFDerivAt secondImplicitCurveEquation (implicitLinearDerivative 0 4) (1, 1) := by
  have hx : HasStrictFDerivAt (fun p : ℝ × ℝ ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 1) := hasStrictFDerivAt_fst
  have hy : HasStrictFDerivAt (fun p : ℝ × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1) := hasStrictFDerivAt_snd
  have h := (((hx.pow 2).fun_add (hy.pow 2)).pow 2).fun_sub
    (((hx.pow 2).const_mul 4).fun_mul hy)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp [implicitLinearDerivative, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Bài 4.1.8(a): tiếp tuyến tại `(√2/2, √2/2)` là `y = 3x − √2`. -/
theorem source_first_implicit_tangent :
    ∃ g : ℝ → ℝ, g firstContactAbscissa = firstContactAbscissa ∧
      (∀ᶠ p in 𝓝 (firstContactAbscissa, firstContactAbscissa),
        p.1 ^ 2 * (p.1 ^ 2 + p.2 ^ 2) = p.2 ^ 2 ↔ g p.1 = p.2) ∧
      (∀ᶠ x in 𝓝 firstContactAbscissa,
        x ^ 2 * (x ^ 2 + g x ^ 2) = g x ^ 2) ∧
      HasDerivAt g 3 firstContactAbscissa ∧ HasDerivativeWithinAt g univ firstContactAbscissa 3 ∧
      (∀ x, tangentLine g firstContactAbscissa 3 x = 3 * x - Real.sqrt 2) ∧
      (∀ y, Tendsto (fun z ↦ secantLine g firstContactAbscissa z y)
        (𝓝[univ \ {firstContactAbscissa}] firstContactAbscissa) (𝓝 (3 * y - Real.sqrt 2))) := by
  obtain ⟨g, hpoint, hcurve, hgraph, hd⟩ := implicit_local_graph
    first_curve_equation_hasStrictFDerivAt first_curve_contact (neg_ne_zero.mpr first_contact_abscissa_ne_zero)
  have hslope : -(3 * firstContactAbscissa) / (-firstContactAbscissa) = (3 : ℝ) := by
    apply (div_eq_iff (neg_ne_zero.mpr first_contact_abscissa_ne_zero)).mpr
    ring
  have hderiv : HasDerivAt g 3 firstContactAbscissa := hd.congr_deriv hslope
  have hsource : HasDerivativeWithinAt g univ firstContactAbscissa 3 :=
    (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g univ isOpen_univ firstContactAbscissa 3 (mem_univ _)).mpr hderiv
  have hline : ∀ x, tangentLine g firstContactAbscissa 3 x = 3 * x - Real.sqrt 2 := by
    intro x
    rw [tangentLine, hpoint]
    dsimp [firstContactAbscissa]
    ring
  refine ⟨g, hpoint, ?_, ?_, hderiv, hsource, hline, ?_⟩
  · filter_upwards [hcurve] with p hp
    exact (first_curve_source_equation p).symm.trans hp
  · filter_upwards [hgraph] with x hx
    exact (first_curve_source_equation (x, g x)).mp hx
  · intro y
    simpa only [hline y] using secantLine_tendsto_tangent hsource y

/-- Bài 4.1.8(b): tiếp tuyến tại `(1, 1)` là `y = 1`. -/
theorem source_second_implicit_tangent :
    ∃ g : ℝ → ℝ, g 1 = 1 ∧
      (∀ᶠ p in 𝓝 ((1 : ℝ), (1 : ℝ)),
        (p.1 ^ 2 + p.2 ^ 2) ^ 2 = 4 * p.1 ^ 2 * p.2 ↔ g p.1 = p.2) ∧
      (∀ᶠ x in 𝓝 (1 : ℝ), (x ^ 2 + g x ^ 2) ^ 2 = 4 * x ^ 2 * g x) ∧
      HasDerivAt g 0 1 ∧ HasDerivativeWithinAt g univ 1 0 ∧
      (∀ x, tangentLine g 1 0 x = 1) ∧
      (∀ y, Tendsto (fun z ↦ secantLine g 1 z y)
        (𝓝[univ \ {(1 : ℝ)}] 1) (𝓝 (1 : ℝ))) := by
  obtain ⟨g, hpoint, hcurve, hgraph, hd⟩ := implicit_local_graph
    second_curve_equation_hasStrictFDerivAt second_curve_contact (by norm_num : (4 : ℝ) ≠ 0)
  have hderiv : HasDerivAt g 0 1 := by simpa only [neg_zero, zero_div] using hd
  have hsource : HasDerivativeWithinAt g univ 1 0 :=
    (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g univ isOpen_univ 1 0 (mem_univ _)).mpr hderiv
  have hline : ∀ x, tangentLine g 1 0 x = 1 := by
    intro x
    simp only [tangentLine, hpoint, zero_mul, add_zero]
  refine ⟨g, hpoint, ?_, ?_, hderiv, hsource, hline, ?_⟩
  · filter_upwards [hcurve] with p hp
    exact (second_curve_source_equation p).symm.trans hp
  · filter_upwards [hgraph] with x hx
    exact (second_curve_source_equation (x, g x)).mp hx
  · intro y
    simpa only [hline y] using secantLine_tendsto_tangent hsource y

end calculus.Chapter04.Section01ImplicitTangentExercises
