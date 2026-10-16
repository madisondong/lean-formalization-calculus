import calculus.Chapter03.Section04
import calculus.Chapter03.Section01Elementary
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# §3.6 — tính liên tục của hàm sơ cấp

Nguồn: định lí dòng 2993–2995.
-/
namespace calculus.Chapter03.Section06
open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section01Elementary
open calculus.Chapter03.Section01Powers calculus.Chapter03.Section01Trigonometric
open calculus.Chapter03.Section01Hyperbolic


theorem real_power_continuousOn_domain (α : ℝ) :
    ContinuousOn (fun x : ℝ => x^α) (realPowerDomain α) := by
  intro x hx
  apply (Real.continuousAt_rpow_const x α ?_).continuousWithinAt
  by_cases hα : 0≤α
  · exact Or.inr hα
  · left
    intro he
    subst x
    exact negative_power_origin_excluded α (lt_of_not_ge hα) hx


theorem artanh_continuous_at_inside {x : ℝ} (hx : x∈Ioo (-1:ℝ) 1) :
    ContinuousAt Real.artanh x := by
  have hden : 1-x≠0 := (sub_pos.mpr hx.2).ne'
  have hratio : 0<(1+x)/(1-x) := div_pos (by linarith [hx.1]) (sub_pos.mpr hx.2)
  change ContinuousAt (fun y : ℝ => Real.log (Real.sqrt ((1+y)/(1-y)))) x
  have hr : ContinuousAt (fun y : ℝ => (1+y)/(1-y)) x :=
    (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  have hs : ContinuousAt (fun y : ℝ => Real.sqrt ((1+y)/(1-y))) x :=
    Real.continuous_sqrt.continuousAt.comp hr
  exact hs.log (Real.sqrt_pos_of_pos hratio).ne'


theorem basic_function_continuous_on_domain (f : BasicFunction) :
    ContinuousOn f.value f.domain := by
  cases f with
  | constant c => exact continuous_const.continuousOn
  | power α => exact real_power_continuousOn_domain α
  | exponential a ha ha1 => exact (Real.continuous_const_rpow ha.ne').continuousOn
  | logarithm a ha ha1 =>
    intro x hx
    exact (Real.continuousAt_logb (ne_of_gt hx)).continuousWithinAt
  | sine => exact Real.continuous_sin.continuousOn
  | cosine => exact Real.continuous_cos.continuousOn
  | tangent =>
    intro x hx
    simpa only [BasicFunction.value,Pi.div_def,←Real.tan_eq_sin_div_cos] using
      (Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt hx).continuousWithinAt
  | cotangent =>
    intro x hx
    exact (Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt hx).continuousWithinAt
  | secant =>
    intro x hx
    exact (continuous_const.continuousAt.div Real.continuous_cos.continuousAt hx).continuousWithinAt
  | cosecant =>
    intro x hx
    exact (continuous_const.continuousAt.div Real.continuous_sin.continuousAt hx).continuousWithinAt
  | arcsine => exact Real.continuous_arcsin.continuousOn
  | arccosine => exact Real.continuous_arccos.continuousOn
  | arctangent => exact Real.continuous_arctan.continuousOn
  | arccotangent => exact (continuous_const.sub Real.continuous_arctan).continuousOn
  | arcsecant =>
    intro x hx
    exact (Real.continuous_arccos.continuousAt.comp
      (continuousAt_inv₀ (outside_open_unit_ne_zero hx))).continuousWithinAt
  | arccosecant =>
    intro x hx
    exact (Real.continuous_arcsin.continuousAt.comp
      (continuousAt_inv₀ (outside_open_unit_ne_zero hx))).continuousWithinAt
  | hyperbolicSine => exact Real.continuous_sinh.continuousOn
  | hyperbolicCosine => exact Real.continuous_cosh.continuousOn
  | hyperbolicTangent =>
    intro x hx
    simpa only [BasicFunction.value,Pi.div_def,←Real.tanh_eq_sinh_div_cosh] using
      (Real.continuous_sinh.continuousAt.div Real.continuous_cosh.continuousAt
        (Real.cosh_pos x).ne').continuousWithinAt
  | hyperbolicCotangent =>
    intro x hx
    exact (Real.continuous_cosh.continuousAt.div Real.continuous_sinh.continuousAt
      (Real.sinh_ne_zero.mpr hx)).continuousWithinAt
  | hyperbolicSecant =>
    intro x hx
    exact (continuous_const.continuousAt.div Real.continuous_cosh.continuousAt
      (Real.cosh_pos x).ne').continuousWithinAt
  | hyperbolicCosecant =>
    intro x hx
    exact (continuous_const.continuousAt.div Real.continuous_sinh.continuousAt
      (Real.sinh_ne_zero.mpr hx)).continuousWithinAt
  | inverseHyperbolicSine => exact Real.continuous_arsinh.continuousOn
  | inverseHyperbolicCosine => exact Real.continuousOn_arcosh
  | inverseHyperbolicTangent =>
    intro x hx
    exact (artanh_continuous_at_inside hx).continuousWithinAt
  | inverseHyperbolicCotangent =>
    intro x hx
    exact ((artanh_continuous_at_inside (inverse_outside_closed_bounds hx).1).comp
      (continuousAt_inv₀ (outside_closed_ne_zero hx))).continuousWithinAt
  | inverseHyperbolicSecant =>
    apply Real.continuousOn_arcosh.comp
    · intro x hx
      exact (continuousAt_inv₀ hx.1.ne').continuousWithinAt
    · intro x hx
      exact (one_le_inv₀ hx.1).mpr hx.2
  | inverseHyperbolicCosecant =>
    intro x hx
    exact (Real.continuous_arsinh.continuousAt.comp
      (continuousAt_inv₀ hx)).continuousWithinAt


theorem elementary_expression_continuous_on_domain (e : ElementaryExpression) :
    ContinuousOn e.value e.domain := by
  induction e with
  | basic f => exact basic_function_continuous_on_domain f
  | add f g ihf ihg =>
    exact (ihf.mono inter_subset_left).add (ihg.mono inter_subset_right)
  | sub f g ihf ihg =>
    exact (ihf.mono inter_subset_left).sub (ihg.mono inter_subset_right)
  | mul f g ihf ihg =>
    exact (ihf.mono inter_subset_left).mul (ihg.mono inter_subset_right)
  | div f g ihf ihg =>
    exact (ihf.mono (fun x hx => hx.1)).div
      (ihg.mono (fun x hx => hx.2.1)) (fun x hx => hx.2.2)
  | comp f g ihf ihg =>
    exact ihf.comp (ihg.mono (fun x hx => hx.1)) (fun x hx => hx.2)

/-- Mục `C03-S06-theorem-001`: hàm sơ cấp liên tục trên miền tự nhiên không rỗng. -/
theorem elementary_expression_domainContinuousOn (e : ElementaryExpression)
    (hD : e.domain.Nonempty) : DomainContinuousOn e.domain e.value :=
  (domainContinuousOn_iff_continuousOn hD).mpr (elementary_expression_continuous_on_domain e)

end calculus.Chapter03.Section06
