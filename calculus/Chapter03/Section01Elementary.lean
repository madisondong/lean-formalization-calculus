import calculus.Chapter03.Section01Powers
import calculus.Chapter03.Section01Trigonometric
import calculus.Chapter03.Section01Hyperbolic

/-!
# §3.1 — hàm sơ cấp

Nguồn: dòng 1193–1217.
-/

namespace calculus.Chapter03.Section01Elementary

open Set
open calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section01Trigonometric


inductive BasicFunction where
  | constant (c : ℝ)
  | power (α : ℝ)
  | exponential (a : ℝ) (ha : 0<a) (ha1 : a≠1)
  | logarithm (a : ℝ) (ha : 0<a) (ha1 : a≠1)
  | sine | cosine | tangent | cotangent | secant | cosecant
  | arcsine | arccosine | arctangent | arccotangent | arcsecant | arccosecant
  | hyperbolicSine | hyperbolicCosine | hyperbolicTangent
  | hyperbolicCotangent | hyperbolicSecant | hyperbolicCosecant
  | inverseHyperbolicSine | inverseHyperbolicCosine | inverseHyperbolicTangent
  | inverseHyperbolicCotangent | inverseHyperbolicSecant | inverseHyperbolicCosecant


noncomputable def BasicFunction.domain : BasicFunction → Set ℝ
  | .constant _ => univ
  | .power α => realPowerDomain α
  | .exponential _ _ _ => univ
  | .logarithm _ _ _ => Ioi 0
  | .sine | .cosine => univ
  | .tangent | .secant => cosineNonzeroDomain
  | .cotangent | .cosecant => sineNonzeroDomain
  | .arcsine | .arccosine => Icc (-1) 1
  | .arctangent | .arccotangent => univ
  | .arcsecant | .arccosecant => outsideOpenUnitInterval
  | .hyperbolicSine | .hyperbolicCosine | .hyperbolicTangent | .hyperbolicSecant => univ
  | .hyperbolicCotangent | .hyperbolicCosecant => {x | x≠0}
  | .inverseHyperbolicSine => univ
  | .inverseHyperbolicCosine => Ici 1
  | .inverseHyperbolicTangent => Ioo (-1) 1
  | .inverseHyperbolicCotangent => (Icc (-1) 1)ᶜ
  | .inverseHyperbolicSecant => Ioc 0 1
  | .inverseHyperbolicCosecant => {x | x≠0}


noncomputable def BasicFunction.value : BasicFunction → ℝ → ℝ
  | .constant c => fun _ => c
  | .power α => fun x => x^α
  | .exponential a _ _ => fun x => a^x
  | .logarithm a _ _ => Real.logb a
  | .sine => Real.sin
  | .cosine => Real.cos
  | .tangent => Real.tan
  | .cotangent => Section01Trigonometric.cotangent
  | .secant => fun x => 1/Real.cos x
  | .cosecant => fun x => 1/Real.sin x
  | .arcsine => Real.arcsin
  | .arccosine => Real.arccos
  | .arctangent => Real.arctan
  | .arccotangent => Section01Trigonometric.arccotangent
  | .arcsecant => fun x => Real.arccos x⁻¹
  | .arccosecant => fun x => Real.arcsin x⁻¹
  | .hyperbolicSine => Real.sinh
  | .hyperbolicCosine => Real.cosh
  | .hyperbolicTangent => Real.tanh
  | .hyperbolicCotangent => Section01Hyperbolic.hyperbolicCotangent
  | .hyperbolicSecant => Section01Hyperbolic.hyperbolicSecant
  | .hyperbolicCosecant => fun x => 1/Real.sinh x
  | .inverseHyperbolicSine => Real.arsinh
  | .inverseHyperbolicCosine => Real.arcosh
  | .inverseHyperbolicTangent => Real.artanh
  | .inverseHyperbolicCotangent => Section01Hyperbolic.inverseHyperbolicCotangent
  | .inverseHyperbolicSecant => fun x => Real.arcosh x⁻¹
  | .inverseHyperbolicCosecant => fun x => Real.arsinh x⁻¹

/-- Mục `C03-S01-definition-014`: biểu thức sơ cấp dùng hữu hạn phép toán. -/
inductive ElementaryExpression where
  | basic (f : BasicFunction)
  | add (f g : ElementaryExpression)
  | sub (f g : ElementaryExpression)
  | mul (f g : ElementaryExpression)
  | div (f g : ElementaryExpression)
  | comp (f g : ElementaryExpression)


noncomputable def ElementaryExpression.value : ElementaryExpression → ℝ → ℝ
  | .basic f => f.value
  | .add f g => fun x => f.value x+g.value x
  | .sub f g => fun x => f.value x-g.value x
  | .mul f g => fun x => f.value x*g.value x
  | .div f g => fun x => f.value x/g.value x
  | .comp f g => fun x => f.value (g.value x)


noncomputable def ElementaryExpression.domain : ElementaryExpression → Set ℝ
  | .basic f => f.domain
  | .add f g | .sub f g | .mul f g => f.domain ∩ g.domain
  | .div f g => {x | x∈f.domain ∧ x∈g.domain ∧ g.value x≠0}
  | .comp f g => {x | x∈g.domain ∧ g.value x∈f.domain}


noncomputable def ElementaryExpression.domainFunction (e : ElementaryExpression) : e.domain → ℝ :=
  fun x => e.value x


def ElementaryExpression.size : ElementaryExpression → ℕ
  | .basic _ => 1
  | .add f g | .sub f g | .mul f g | .div f g | .comp f g => f.size+g.size+1


theorem expression_size_positive (e : ElementaryExpression) : 0<e.size := by
  cases e <;> simp only [ElementaryExpression.size] <;> omega


noncomputable def identityExpression : ElementaryExpression := .basic (.power 1)


theorem identity_expression_domain : identityExpression.domain=univ := by
  change realPowerDomain (1:ℝ)=univ
  simpa using positive_integer_power_domain (1:ℤ) (by norm_num)


theorem identity_expression_value (x : ℝ) : identityExpression.value x=x := by
  change x^(1:ℝ)=x
  exact Real.rpow_one x


noncomputable def naturalPowerExpression : ℕ → ElementaryExpression
  | 0 => .basic (.constant 1)
  | n+1 => .mul (naturalPowerExpression n) identityExpression


theorem natural_power_expression (n : ℕ) :
    (naturalPowerExpression n).domain=univ ∧ ∀ x, (naturalPowerExpression n).value x=x^n := by
  induction n with
  | zero => simp [naturalPowerExpression,ElementaryExpression.domain,ElementaryExpression.value,BasicFunction.domain,BasicFunction.value]
  | succ n ih =>
    constructor
    · simp only [naturalPowerExpression,ElementaryExpression.domain,ih.1,identity_expression_domain,inter_self]
    · intro x
      simpa only [naturalPowerExpression,ElementaryExpression.value,ih.2 x,identity_expression_value] using (pow_succ x n).symm


noncomputable def polynomialExpression (a : ℕ → ℝ) : ℕ → ElementaryExpression
  | 0 => .basic (.constant (a 0))
  | n+1 => .add (polynomialExpression a n) (.mul (.basic (.constant (a (n+1)))) (naturalPowerExpression (n+1)))


theorem polynomial_expression (a : ℕ → ℝ) (n : ℕ) :
    (polynomialExpression a n).domain=univ ∧
      ∀ x, (polynomialExpression a n).value x=∑ i∈Finset.range (n+1),a i*x^i := by
  induction n with
  | zero => simp [polynomialExpression,ElementaryExpression.domain,ElementaryExpression.value,BasicFunction.domain,BasicFunction.value]
  | succ n ih =>
    constructor
    · simp only [polynomialExpression,ElementaryExpression.domain,BasicFunction.domain,ih.1,(natural_power_expression (n+1)).1,inter_self]
    · intro x
      simp only [polynomialExpression,ElementaryExpression.value,BasicFunction.value,ih.2 x,(natural_power_expression (n+1)).2 x,Finset.sum_range_succ]

/-- Mục `C03-S01-example-011` (a): đa thức bậc n≥1 với hệ số dẫn khác 0. -/
theorem polynomial_expression_exists (a : ℕ → ℝ) (n : ℕ) (_hn : 1≤n) (_ha : a n≠0) :
    ∃ e : ElementaryExpression, e.domain=univ ∧ ∀ x, e.value x=∑ i∈Finset.range (n+1),a i*x^i :=
  ⟨polynomialExpression a n,polynomial_expression a n⟩

/-- Mục `C03-S01-example-011` (b): hàm hữu tỉ trên miền mẫu khác 0. -/
theorem rational_expression_exists (a b : ℕ → ℝ) (n m : ℕ)
    (_hn : 1≤n) (_hm : 1≤m) (_ha : a n≠0) (_hb : b m≠0) :
    ∃ e : ElementaryExpression,
      e.domain={x | (∑ i∈Finset.range (m+1),b i*x^i)≠0} ∧
      ∀ x, e.value x=(∑ i∈Finset.range (n+1),a i*x^i)/(∑ i∈Finset.range (m+1),b i*x^i) := by
  refine ⟨.div (polynomialExpression a n) (polynomialExpression b m),?_,?_⟩
  · ext x
    simp only [ElementaryExpression.domain,(polynomial_expression a n).1,(polynomial_expression b m).1,mem_ofPred_eq,mem_univ,true_and,(polynomial_expression b m).2]
  · intro x
    simp only [ElementaryExpression.value,(polynomial_expression a n).2,(polynomial_expression b m).2]



noncomputable def naturalLogarithm : BasicFunction :=
  .logarithm (Real.exp 1) (Real.exp_pos 1) (by
    have h := Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
    rw [Real.exp_zero] at h
    exact ne_of_gt h)


theorem natural_logarithm_domain_value : naturalLogarithm.domain=Ioi 0 ∧
    ∀ x, naturalLogarithm.value x=Real.log x := by
  exact ⟨rfl,fun x => by simp [naturalLogarithm,BasicFunction.value,Real.logb]⟩


noncomputable def mixedExampleExpression : ElementaryExpression :=
  .div
    (.add
      (.sub
        (.add
          (.comp (.basic .arcsine) (.mul (.basic (.constant 2)) identityExpression))
          (.comp (.basic .hyperbolicSine)
            (.mul (.basic (.constant 5)) (naturalPowerExpression 2))))
        (.mul (.basic (.constant 9)) identityExpression))
      (.basic (.constant 7)))
    (.mul (.basic (.exponential 3 (by norm_num) (by norm_num)))
      (.comp (.basic naturalLogarithm) (.mul (.basic (.constant 6)) identityExpression)))


theorem mixed_example_expression_value (x : ℝ) :
    mixedExampleExpression.value x=
      (Real.arcsin (2*x)+Real.sinh (5*x^2)-9*x+7)/(3^x*Real.log (6*x)) := by
  simp only [mixedExampleExpression,ElementaryExpression.value,BasicFunction.value,
    identity_expression_value,(natural_power_expression 2).2,naturalLogarithm,Real.logb,Real.log_exp,div_one]


theorem mixed_example_expression_domain_raw :
    mixedExampleExpression.domain={x | -1≤2*x ∧ 2*x≤1 ∧ 0<6*x ∧ 3^x*Real.log (6*x)≠0} := by
  ext x
  simp only [mixedExampleExpression,ElementaryExpression.domain,BasicFunction.domain,
    identity_expression_domain,(natural_power_expression 2).1,
    ElementaryExpression.value,BasicFunction.value,identity_expression_value,
    naturalLogarithm,Real.logb,Real.log_exp,div_one,
    mem_ofPred_eq,mem_inter_iff,mem_univ,mem_Icc,mem_Ioi,and_true,true_and,and_assoc]

/-- Mục `C03-S01-example-011` (c): miền xác định là (0,1/2]\{1/6}. -/
theorem mixed_example_expression_domain :
    mixedExampleExpression.domain={x | 0<x ∧ x≤1/2 ∧ x≠1/6} := by
  rw [mixed_example_expression_domain_raw]
  ext x
  constructor
  · rintro ⟨hlo,hhi,hpos,hn⟩
    refine ⟨by linarith,by linarith,?_⟩
    intro he
    subst x
    norm_num at hn
  · rintro ⟨hpos,hhi,hn⟩
    refine ⟨by linarith,by linarith,by linarith,mul_ne_zero ?_ ?_⟩
    · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) x).ne'
    · apply Real.log_ne_zero_of_pos_of_ne_one (by linarith)
      intro he
      apply hn
      linarith

/-- Mục `C03-S01-example-011` (c): hàm sơ cấp trên miền tự nhiên. -/
theorem mixed_example_expression_exists :
    ∃ e : ElementaryExpression, e.domain={x | 0<x ∧ x≤1/2 ∧ x≠1/6} ∧
      ∀ x, e.value x=(Real.arcsin (2*x)+Real.sinh (5*x^2)-9*x+7)/(3^x*Real.log (6*x)) :=
  ⟨mixedExampleExpression,mixed_example_expression_domain,mixed_example_expression_value⟩

end calculus.Chapter03.Section01Elementary
