import calculus.Chapter03.Section01Trigonometric
import calculus.Chapter03.Section01Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round

/-!
# §3.1 — bài tập về hàm sơ cấp

Nguồn: dòng 1228–1295. Bài tập 20 dùng phép lặp hàm.
-/
namespace calculus.Chapter03.Section01Exercises

open Set
open calculus.Chapter03.Section01Properties
open calculus.Chapter03.Section01Trigonometric


theorem odd_not_even_of_nonzero {D : Set ℝ} {f : ℝ → ℝ} (hf : OddFunctionOnSymmetricDomain D f)
    {x : ℝ} (hx : x∈D) (hfx : f x≠0) : ¬EvenFunctionOnSymmetricDomain D f := by
  intro he
  have h1 := hf.2 x hx
  have h2 := he.2 x hx
  apply hfx
  linarith

/-- Bài tập 16(a): 2^x+2^(−x) chẵn, không lẻ. -/
theorem exercise16a_even_not_odd :
    EvenFunctionOnSymmetricDomain univ (fun x : ℝ => (2:ℝ)^x+2^(-x)) ∧
      ¬OddFunctionOnSymmetricDomain univ (fun x : ℝ => (2:ℝ)^x+2^(-x)) := by
  constructor
  · exact ⟨fun _ _ => mem_univ _,fun x _ => by simp only [neg_neg,add_comm]⟩
  · intro h
    have he := h.2 0 (mem_univ 0)
    norm_num at he


theorem logarithmic_ratio_domain :
    {x : ℝ | 0<(1-x)/(1+x)}=Ioo (-1) 1 := by
  ext x
  rw [mem_ofPred_eq,mem_Ioo,div_pos_iff]
  constructor
  · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩) <;> constructor <;> linarith
  · rintro ⟨h1,h2⟩
    left
    constructor <;> linarith

/-- Bài tập 16(b): x↦ln((1−x)/(1+x)) lẻ trên miền tự nhiên và không chẵn. -/
theorem exercise16b_odd_not_even :
    OddFunctionOnSymmetricDomain (Ioo (-1) 1) (fun x : ℝ => Real.log ((1-x)/(1+x))) ∧
      ¬EvenFunctionOnSymmetricDomain (Ioo (-1) 1) (fun x : ℝ => Real.log ((1-x)/(1+x))) := by
  have ho : OddFunctionOnSymmetricDomain (Ioo (-1) 1) (fun x : ℝ => Real.log ((1-x)/(1+x))) := by
    refine ⟨fun x hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩,?_⟩
    intro x _
    dsimp only
    rw [sub_neg_eq_add,show (1:ℝ)+(-x)=1-x by ring,←inv_div,Real.log_inv]
  refine ⟨ho,odd_not_even_of_nonzero ho (x := 1/2) (by norm_num) ?_⟩
  apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num

/-- Bài tập 16(c): log(x+√(1+x²)) là hàm lẻ, không chẵn. -/
theorem exercise16c_odd_not_even :
    OddFunctionOnSymmetricDomain univ (fun x : ℝ => Real.log (x+Real.sqrt (1+x^2))) ∧
      ¬EvenFunctionOnSymmetricDomain univ (fun x : ℝ => Real.log (x+Real.sqrt (1+x^2))) := by
  have ho : OddFunctionOnSymmetricDomain univ Real.arsinh :=
    ⟨fun _ _ => mem_univ _,fun x _ => Real.arsinh_neg x⟩
  change OddFunctionOnSymmetricDomain univ Real.arsinh ∧ ¬EvenFunctionOnSymmetricDomain univ Real.arsinh
  refine ⟨ho,odd_not_even_of_nonzero ho (x := 1) (mem_univ 1) ?_⟩
  intro he
  have hs := Real.sinh_arsinh 1
  rw [he,Real.sinh_zero] at hs
  norm_num at hs

/-- Bài tập 16(d): đa thức không chẵn, không lẻ. -/
theorem exercise16d_neither_even_nor_odd :
    ¬EvenFunctionOnSymmetricDomain univ (fun x : ℝ => x^5-2*x^4+3*x) ∧
      ¬OddFunctionOnSymmetricDomain univ (fun x : ℝ => x^5-2*x^4+3*x) := by
  constructor
  · intro h
    have he := h.2 1 (mem_univ 1)
    norm_num at he
  · intro h
    have he := h.2 1 (mem_univ 1)
    norm_num at he

/-- Bài tập 17: tính chẵn lẻ của tích hai hàm trên miền đối xứng. -/
theorem exercise17_product_parities {D : Set ℝ} {f g : ℝ → ℝ} :
    (EvenFunctionOnSymmetricDomain D f → EvenFunctionOnSymmetricDomain D g → EvenFunctionOnSymmetricDomain D (fun x => f x*g x)) ∧
    (OddFunctionOnSymmetricDomain D f → OddFunctionOnSymmetricDomain D g → EvenFunctionOnSymmetricDomain D (fun x => f x*g x)) ∧
    (EvenFunctionOnSymmetricDomain D f → OddFunctionOnSymmetricDomain D g → OddFunctionOnSymmetricDomain D (fun x => f x*g x)) ∧
    (OddFunctionOnSymmetricDomain D f → EvenFunctionOnSymmetricDomain D g → OddFunctionOnSymmetricDomain D (fun x => f x*g x)) := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro hf hg <;>
    refine ⟨hf.1,fun x hx => ?_⟩ <;> dsimp only <;> rw [hf.2 x hx,hg.2 x hx] <;> ring

/-- Bài tập 18(a): hàm hằng 1 có mọi chu kì dương, không có chu kì nhỏ nhất. -/
theorem exercise18a_constant_periods :
    (∀ T : ℝ, 0<T → HasPositiveForwardPeriodOn univ (fun _ : ℝ => 1) T) ∧
      ¬∃ T, HasLeastPositiveForwardPeriodOn univ (fun _ : ℝ => 1) T :=
  constant_has_no_least_positive_forward_period 1

/-- Bài tập 19: x² tăng, −x giảm trên [0,1] nhưng tổng không đơn điệu. -/
theorem exercise19_sum_counterexample :
    MonotoneOn (fun x : ℝ => x^2) (Icc 0 1) ∧
    AntitoneOn (fun x : ℝ => -x) (Icc 0 1) ∧
    ¬MonotoneOn (fun x : ℝ => x^2-x) (Icc 0 1) ∧
    ¬AntitoneOn (fun x : ℝ => x^2-x) (Icc 0 1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    nlinarith [hx.1,hy.1]
  · intro x _ y _ hxy
    exact neg_le_neg hxy
  · intro h
    have he := h (a := 0) (by norm_num) (b := 1/2) (by norm_num) (by norm_num)
    norm_num at he
  · intro h
    have he := h (a := 1/2) (by norm_num) (b := 1) (by norm_num) (by norm_num)
    norm_num at he

/-- Bài tập 20: hàm hằng 0 bác bỏ phát biểu với tính đơn điệu không ngặt. -/
theorem exercise20_composition_claim_counterexample :
    ∃ f : ℝ → ℝ, Monotone (f ∘ f) ∧ Antitone (f ∘ f ∘ f) ∧ ¬StrictAnti f := by
  refine ⟨fun _ => 0,?_,?_,?_⟩
  · intro x y _
    exact le_rfl
  · intro x y _
    exact le_rfl
  · intro h
    have he := h (show (0:ℝ)<1 by norm_num)
    norm_num at he

/-- Bài tập 21(a): hai giá trị của hàm lượng giác ngược. -/
theorem exercise21a_inverse_values : Real.arcsin (1/2)=Real.pi/6 ∧ Real.arccos 0=Real.pi/2 :=
  ⟨arcsine_special_values.1,Real.arccos_zero⟩

/-- Bài tập 21(b): arctan √3=π/3 và arccot(−√3)=5π/6. -/
theorem exercise21b_inverse_values :
    Real.arctan (Real.sqrt 3)=Real.pi/3 ∧ arccotangent (-Real.sqrt 3)=5*Real.pi/6 := by
  refine ⟨Real.arctan_sqrt_three,?_⟩
  rw [arccotangent,Real.arctan_neg,Real.arctan_sqrt_three]
  ring

/-- Bài tập 21(c): giá trị arccos và arcsin tại −1/√2. -/
theorem exercise21c_inverse_values :
    Real.arccos (-Real.sqrt 2)⁻¹=3*Real.pi/4 ∧
      Real.arcsin (-Real.sqrt 2)⁻¹= -Real.pi/4 := by
  have he : (-Real.sqrt 2)⁻¹= -Real.sqrt 2/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hn : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    field_simp
    nlinarith
  rw [he]
  exact ⟨arccosine_special_values.2,arcsine_special_values.2⟩

/-- Bài tập 21(d): giá trị sin(arctan(3/4)) và sec(arcsin(4/5)). -/
theorem exercise21d_inverse_values :
    Real.sin (Real.arctan (3/4))=3/5 ∧ 1/Real.cos (Real.arcsin (4/5))=5/3 := by
  have h25 : Real.sqrt 25=5 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have h16 : Real.sqrt 16=4 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have h9 : Real.sqrt 9=3 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  constructor
  · rw [Real.sin_arctan]
    norm_num
    rw [h25,h16]
    norm_num
  · rw [Real.cos_arcsin]
    norm_num
    rw [h25,h9]

/-- Bài tập 22(a): trên [0,+∞), √x bị chặn dưới nhưng không bị chặn trên. -/
theorem exercise22a_square_root_unbounded :
    FunctionBoundedBelowOn (Ici 0) Real.sqrt ∧ ¬FunctionBoundedAboveOn (Ici 0) Real.sqrt := by
  refine ⟨⟨0,fun x _ => Real.sqrt_nonneg x⟩,?_⟩
  rintro ⟨M,hM⟩
  let L := max M 0+1
  have hL : 0<L := by dsimp [L]; linarith [le_max_right M 0]
  have he := hM (L^2) (sq_nonneg L)
  rw [Real.sqrt_sq_eq_abs,abs_of_pos hL] at he
  dsimp [L] at he
  linarith [le_max_left M 0]

/-- Bài tập 22(b): |x sin(1/x)|≤1 với x≠0. -/
theorem exercise22b_oscillating_bound :
    FunctionBoundedOn {x : ℝ | x≠0} (fun x => x*Real.sin (1/x)) := by
  refine ⟨-1,1,?_⟩
  intro x hx
  have he : |x*Real.sin (1/x)|≤1 := by
    rw [abs_mul]
    calc
      |x| * |Real.sin (1/x)| ≤ |x| * |1/x| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg x)
      _ = 1 := by rw [one_div,abs_inv,mul_inv_cancel₀ (abs_ne_zero.mpr hx)]
  exact abs_le.mp he

/-- Bài tập 22(c): 1/x trên (0,1) bị chặn dưới nhưng không bị chặn trên. -/
theorem exercise22c_reciprocal_unbounded :
    FunctionBoundedBelowOn (Ioo 0 1) (fun x : ℝ => 1/x) ∧
      ¬FunctionBoundedAboveOn (Ioo 0 1) (fun x : ℝ => 1/x) := by
  refine ⟨⟨0,fun x hx => (one_div_pos.mpr hx.1).le⟩,?_⟩
  rintro ⟨M,hM⟩
  let L := max M 1+1
  have hL : 1<L := by dsimp [L]; linarith [le_max_right M 1]
  have hx : L⁻¹∈Ioo (0:ℝ) 1 := ⟨inv_pos.mpr (by linarith), (inv_lt_one₀ (by linarith)).mpr hL⟩
  have he := hM L⁻¹ hx
  change 1/L⁻¹≤M at he
  rw [one_div,inv_inv] at he
  dsimp [L] at he
  linarith [le_max_left M 1]

/-- Bài tập 23(a): arcsin x+arccos x=π/2 trên [−1,1]. -/
theorem exercise23a_inverse_sum (x : Icc (-1:ℝ) 1) :
    Real.arcsin x+Real.arccos x=Real.pi/2 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

/-- Bài tập 23(b): arctan x+arccot x=π/2 trên ℝ. -/
theorem exercise23b_inverse_sum (x : ℝ) : Real.arctan x+arccotangent x=Real.pi/2 := by
  rw [arccotangent]
  ring

/-- Bài tập 23(c): công thức theo dấu của x≠0. -/
theorem exercise23c_inverse_sum (x : ℝ) (hx : x≠0) :
    Real.arctan x+Real.arctan (1/x)=Real.pi/2*SignType.sign x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · rw [one_div,Real.arctan_inv_of_neg hn,sign_neg hn]
    simp only [SignType.coe_neg_one]
    ring
  · rw [one_div,Real.arctan_inv_of_pos hp,sign_pos hp]
    simp only [SignType.coe_one]
    ring



def tangentCotangentDomain : Set ℝ := {x | Real.cos x≠0 ∧ Real.sin x≠0}

/-- Bài tập 18(b): tan x+cot x có chu kì π trên miền xác định. -/
theorem exercise18b_tangent_cotangent_period :
    HasPositiveForwardPeriodOn tangentCotangentDomain (fun x => Real.tan x+cotangent x) Real.pi := by
  refine ⟨Real.pi_pos,?_⟩
  intro x hx
  change Real.cos x≠0 ∧ Real.sin x≠0 at hx
  refine ⟨?_,?_⟩
  · change Real.cos (x+Real.pi)≠0 ∧ Real.sin (x+Real.pi)≠0
    simpa only [Real.cos_add_pi,Real.sin_add_pi,neg_ne_zero] using hx
  · dsimp only
    rw [Real.tan_add_pi,cotangent,Real.cos_add_pi,Real.sin_add_pi,neg_div_neg_eq]
    rfl


noncomputable def distanceToIntegers (x : ℝ) : ℝ := sInf (range (fun n : ℤ => |x-(n:ℝ)|))


theorem distance_to_integers_eq_round (x : ℝ) :
    distanceToIntegers x=|x-(round x:ℝ)| := by
  apply IsLeast.csInf_eq
  refine ⟨⟨round x,rfl⟩,?_⟩
  rintro y ⟨n,rfl⟩
  exact round_le x n


theorem distance_to_integers_zero_iff (x : ℝ) :
    distanceToIntegers x=0 ↔ ∃ n : ℤ, (n:ℝ)=x := by
  rw [distance_to_integers_eq_round,abs_eq_zero,sub_eq_zero]
  constructor
  · intro he
    exact ⟨round x,he.symm⟩
  · rintro ⟨n,rfl⟩
    rw [round_intCast]

/-- Bài tập 18(c): d(x,ℤ) có chu kì 1. -/
theorem exercise18c_integer_distance_period : HasPositiveForwardPeriodOn univ distanceToIntegers 1 := by
  refine ⟨by norm_num,fun x _ => ⟨mem_univ _,?_⟩⟩
  rw [distance_to_integers_eq_round,distance_to_integers_eq_round,round_add_one,Int.cast_add,Int.cast_one]
  congr 1
  ring


theorem exercise18c_integer_distance_least_period : HasLeastPositiveForwardPeriodOn univ distanceToIntegers 1 := by
  refine ⟨exercise18c_integer_distance_period,?_⟩
  intro T hT
  have he := (hT.2 0 (mem_univ 0)).2
  have hzero : distanceToIntegers 0=0 := (distance_to_integers_zero_iff 0).mpr ⟨0,by norm_num⟩
  simp only [zero_add,hzero] at he
  obtain ⟨n,hn⟩ := (distance_to_integers_zero_iff T).mp he
  have hpos : (0:ℤ)<n := by
    have hp : (0:ℝ)<(n:ℝ) := by rw [hn]; exact hT.1
    exact_mod_cast hp
  have hle : (1:ℤ)≤n := by omega
  rw [←hn]
  exact_mod_cast hle


def IsRationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q:ℝ)=x


noncomputable def rationalIndicator (x : ℝ) : ℝ := by
  classical
  exact if IsRationalReal x then 1 else 0


theorem rational_add_rat_iff (x : ℝ) (q : ℚ) :
    IsRationalReal (x+(q:ℝ)) ↔ IsRationalReal x := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r-q,?_⟩
    push_cast
    linarith
  · rintro ⟨r,hr⟩
    refine ⟨r+q,?_⟩
    push_cast
    rw [hr]


theorem rational_indicator_eq_one_iff (x : ℝ) : rationalIndicator x=1 ↔ IsRationalReal x := by
  classical
  simp [rationalIndicator]

/-- Bài tập 18(d): tập các chu kì là các số hữu tỉ dương. -/
theorem exercise18d_dirichlet_periods (T : ℝ) :
    HasPositiveForwardPeriodOn univ rationalIndicator T ↔ 0<T ∧ IsRationalReal T := by
  constructor
  · intro hT
    refine ⟨hT.1,?_⟩
    have he := (hT.2 0 (mem_univ 0)).2
    have h0 : rationalIndicator 0=1 := (rational_indicator_eq_one_iff 0).mpr ⟨0,by norm_num⟩
    simp only [zero_add,h0] at he
    exact (rational_indicator_eq_one_iff T).mp he
  · rintro ⟨hpos,⟨q,rfl⟩⟩
    refine ⟨hpos,fun x _ => ⟨mem_univ _,?_⟩⟩
    by_cases hx : IsRationalReal x
    · have ha := (rational_add_rat_iff x q).mpr hx
      simp only [rationalIndicator,if_pos hx,if_pos ha]
    · have ha : ¬IsRationalReal (x+(q:ℝ)) := fun he => hx ((rational_add_rat_iff x q).mp he)
      simp only [rationalIndicator,if_neg hx,if_neg ha]


theorem exercise18d_dirichlet_no_least :
    HasPositiveForwardPeriodOn univ rationalIndicator 1 ∧ ¬∃ T, HasLeastPositiveForwardPeriodOn univ rationalIndicator T := by
  refine ⟨(exercise18d_dirichlet_periods 1).mpr ⟨by norm_num,1,by norm_num⟩,?_⟩
  rintro ⟨T,hT⟩
  obtain ⟨hpos,q,hq⟩ := (exercise18d_dirichlet_periods T).mp hT.1
  have hp : HasPositiveForwardPeriodOn univ rationalIndicator (T/2) :=
    (exercise18d_dirichlet_periods (T/2)).mpr ⟨by linarith,q/2,by push_cast; rw [hq]⟩
  have hl := hT.2 (T/2) hp
  linarith



theorem logarithmic_arsinh_domain : {x : ℝ | 0<x+Real.sqrt (1+x^2)}=univ := by
  ext x
  simp only [mem_ofPred_eq,mem_univ,iff_true]
  rw [←Real.exp_arsinh]
  exact Real.exp_pos (Real.arsinh x)


/-- Bài tập 24: các đẳng thức hyperbol, với x≠0 cho coth và csch. -/
theorem exercise24_hyperbolic_identities (x y : ℝ) :
    Real.cosh x^2-Real.sinh x^2=1 ∧
    Real.tanh x^2+Section01Hyperbolic.hyperbolicSecant x^2=1 ∧
    (x≠0 → Section01Hyperbolic.hyperbolicCotangent x^2-(1/Real.sinh x)^2=1) ∧
    Real.sinh (x+y)=Real.sinh x*Real.cosh y+Real.cosh x*Real.sinh y ∧
    Real.sinh (x-y)=Real.sinh x*Real.cosh y-Real.cosh x*Real.sinh y ∧
    Real.cosh (x+y)=Real.cosh x*Real.cosh y+Real.sinh x*Real.sinh y ∧
    Real.cosh (x-y)=Real.cosh x*Real.cosh y-Real.sinh x*Real.sinh y ∧
    Real.sinh x^2=(-1+Real.cosh (2*x))/2 ∧
    Real.cosh x^2=(1+Real.cosh (2*x))/2 ∧
    Real.sinh (2*x)=2*Real.sinh x*Real.cosh x ∧
    Real.cosh (2*x)=Real.cosh x^2+Real.sinh x^2 :=
  Section01Hyperbolic.hyperbolic_identities x y


theorem graph_of_subtype_formula {D : Set ℝ} (f : D → ℝ) (g : ℝ → ℝ)
    (h : ∀ x, f x=g x.val) :
    range (fun x : D => (x.val,f x))={p : ℝ×ℝ | p.1∈D ∧ p.2=g p.1} := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.property,h x⟩
  · rintro ⟨hx,hy⟩
    exact ⟨⟨p.1,hx⟩,Prod.ext rfl ((h ⟨p.1,hx⟩).trans hy.symm)⟩


noncomputable def arsinhGraph : Set (ℝ×ℝ) :=
  range (fun x : (univ : Set ℝ) => (x.val,Section01Hyperbolic.sinhInverseEquiv.symm x.val))


noncomputable def arcoshGraph : Set (ℝ×ℝ) :=
  range (fun x : Ici (1:ℝ) => (x.val,(Section01Hyperbolic.coshInverseEquiv.symm x).val))


noncomputable def artanhGraph : Set (ℝ×ℝ) :=
  range (fun x : Ioo (-1:ℝ) 1 => (x.val,Section01Hyperbolic.tanhInverseEquiv.symm x))


noncomputable def arcothGraph : Set (ℝ×ℝ) :=
  range (fun x : Section01Hyperbolic.outsideClosedUnitInterval =>
    (x.val,(Section01Hyperbolic.cothInverseEquiv.symm x).val))


noncomputable def arsechGraph : Set (ℝ×ℝ) :=
  range (fun x : Ioc (0:ℝ) 1 => (x.val,(Section01Hyperbolic.sechInverseEquiv.symm x).val))


noncomputable def arcschGraph : Set (ℝ×ℝ) :=
  range (fun x : Section01Hyperbolic.nonzeroDomain =>
    (x.val,(Section01Hyperbolic.cschInverseEquiv.symm x).val))

/-- Bài tập 25: đồ thị và công thức logarit của sáu hàm hyperbol ngược. -/
theorem exercise25_inverse_hyperbolic_graphs :
    arsinhGraph={p : ℝ×ℝ | p.1∈(univ : Set ℝ) ∧ p.2=Real.log (p.1+Real.sqrt (p.1^2+1))} ∧
    arcoshGraph={p : ℝ×ℝ | p.1∈Ici 1 ∧ p.2=Real.log (p.1+Real.sqrt (p.1^2-1))} ∧
    artanhGraph={p : ℝ×ℝ | p.1∈Ioo (-1) 1 ∧ p.2=1/2*Real.log ((1+p.1)/(1-p.1))} ∧
    arcothGraph={p : ℝ×ℝ | p.1∈Section01Hyperbolic.outsideClosedUnitInterval ∧ p.2=1/2*Real.log ((p.1+1)/(p.1-1))} ∧
    arsechGraph={p : ℝ×ℝ | p.1∈Ioc 0 1 ∧ p.2=Real.log ((1+Real.sqrt (1-p.1^2))/p.1)} ∧
    arcschGraph={p : ℝ×ℝ | p.1∈Section01Hyperbolic.nonzeroDomain ∧ p.2=Real.log (1/p.1+Real.sqrt (1+p.1^2)/|p.1|)} := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact graph_of_subtype_formula (fun x : (univ : Set ℝ) => Section01Hyperbolic.sinhInverseEquiv.symm x.val)
      (fun x => Real.log (x+Real.sqrt (x^2+1))) (fun x => Section01Hyperbolic.arsinh_logarithm_formula x)
  · exact graph_of_subtype_formula (fun x : Ici (1:ℝ) => (Section01Hyperbolic.coshInverseEquiv.symm x).val)
      (fun x => Real.log (x+Real.sqrt (x^2-1))) Section01Hyperbolic.arcosh_logarithm_formula
  · exact graph_of_subtype_formula (fun x : Ioo (-1:ℝ) 1 => Section01Hyperbolic.tanhInverseEquiv.symm x)
      (fun x => 1/2*Real.log ((1+x)/(1-x))) Section01Hyperbolic.artanh_logarithm_formula
  · exact graph_of_subtype_formula (fun x : Section01Hyperbolic.outsideClosedUnitInterval => (Section01Hyperbolic.cothInverseEquiv.symm x).val)
      (fun x => 1/2*Real.log ((x+1)/(x-1))) Section01Hyperbolic.arcoth_logarithm_formula
  · exact graph_of_subtype_formula (fun x : Ioc (0:ℝ) 1 => (Section01Hyperbolic.sechInverseEquiv.symm x).val)
      (fun x => Real.log ((1+Real.sqrt (1-x^2))/x)) Section01Hyperbolic.arsech_logarithm_formula
  · exact graph_of_subtype_formula (fun x : Section01Hyperbolic.nonzeroDomain => (Section01Hyperbolic.cschInverseEquiv.symm x).val)
      (fun x => Real.log (1/x+Real.sqrt (1+x^2)/|x|)) Section01Hyperbolic.arcsch_logarithm_formula


theorem exercise22a_square_root_not_bounded : ¬FunctionBoundedOn (Ici 0) Real.sqrt := by
  rintro ⟨m,M,h⟩
  exact exercise22a_square_root_unbounded.2 ⟨M,fun x hx => (h x hx).2⟩


theorem exercise22c_reciprocal_not_bounded : ¬FunctionBoundedOn (Ioo 0 1) (fun x : ℝ => 1/x) := by
  rintro ⟨m,M,h⟩
  exact exercise22c_reciprocal_unbounded.2 ⟨M,fun x hx => (h x hx).2⟩

end calculus.Chapter03.Section01Exercises
