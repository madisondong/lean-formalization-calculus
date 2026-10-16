import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# 3.1. Hàm số một biến thực

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 18–273.
-/

namespace calculus.Chapter03.Section01

open Set Function


abbrev RealFunction (X Y : Set ℝ) := X → Y


def realRange {X Y : Set ℝ} (f : RealFunction X Y) : Set ℝ :=
  Set.range (fun x : X => (f x : ℝ))


def realGraph {X Y : Set ℝ} (f : RealFunction X Y) : Set (ℝ × ℝ) :=
  {p | ∃ x : X, p = ((x : ℝ), (f x : ℝ))}


theorem mem_realRange {X Y : Set ℝ} (f : RealFunction X Y) (y : ℝ) :
    y ∈ realRange f ↔ ∃ x : X, (f x : ℝ) = y := Iff.rfl


theorem constant_graph (D : Set ℝ) (c : ℝ) :
    {p : ℝ × ℝ | ∃ x : D, p = ((x : ℝ), c)} = {p | p.1 ∈ D ∧ p.2 = c} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.property, rfl⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨p.1, hx⟩, by ext <;> simp [hy]⟩


theorem restricted_constant_graph_counterexample (c : ℝ) :
    (0, c) ∉ {p : ℝ × ℝ | ∃ x : ({1} : Set ℝ), p = ((x : ℝ), c)} := by
  rw [constant_graph]
  norm_num


theorem sign_cases (x : ℝ) :
    (0 < x → Real.sign x = 1) ∧ (x = 0 → Real.sign x = 0) ∧
      (x < 0 → Real.sign x = -1) :=
  ⟨Real.sign_of_pos, fun h => h ▸ Real.sign_zero, Real.sign_of_neg⟩


theorem floor_greatest_integer (x : ℝ) :
    ((⌊x⌋ : ℤ) : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ⌊x⌋ := by
  exact ⟨Int.floor_le x, fun z hz => Int.le_floor.mpr hz⟩


theorem real_function_eq_iff {X Y : Set ℝ} (f g : RealFunction X Y) :
    f = g ↔ ∀ x, f x = g x := funext_iff

/-- Ví dụ |x|=x sgn(x), kể cả x=0. -/
theorem abs_eq_mul_sign (x : ℝ) : |x| = x * Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx, mul_one]


def restrictReal {X Y A : Set ℝ} (f : RealFunction X Y) (h : A ⊆ X) : RealFunction A Y :=
  fun x => f ⟨x, h x.property⟩


theorem sign_restrict_positive (x : Set.Ioi (0 : ℝ)) : Real.sign (x : ℝ) = 1 :=
  Real.sign_of_pos x.property


theorem pointwise_operations (D : Set ℝ) (f g : D → ℝ) (c : ℝ) (x : D) :
    (f + g) x = f x + g x ∧ (f * g) x = f x * g x ∧ (c • f) x = c * f x := by
  exact ⟨rfl, rfl, rfl⟩


def quotientDomain {D : Set ℝ} (g : D → ℝ) := {x : D | g x ≠ 0}


noncomputable def nonzeroDenominatorQuotient {D : Set ℝ} (f g : D → ℝ) (x : quotientDomain g) : ℝ := f x.val / g x.val


theorem zero_product_nonzero_functions :
    ∃ f g : ℝ → ℝ, f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 := by
  classical
  refine ⟨fun x => if x = 0 then 1 else 0, fun x => if x = 0 then 0 else 2, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · intro h
    have := congrFun h 1
    norm_num at this
  · funext x
    by_cases hx : x = 0 <;> simp [hx]


def PointwiseLE {D : Set ℝ} (f g : D → ℝ) : Prop := ∀ x, f x ≤ g x


def PointwiseLT {D : Set ℝ} (f g : D → ℝ) : Prop := ∀ x, f x < g x


theorem sine_le_constant : PointwiseLE (fun x : Set.Icc (0 : ℝ) Real.pi => Real.sin x)
    (fun _ => 1) := fun x => Real.sin_le_one x


theorem real_composition_apply {X Y Z : Set ℝ} (f : RealFunction X Y) (g : RealFunction Y Z)
    (x : X) : (g ∘ f) x = g (f x) := rfl


theorem affine_cos_compositions (x : ℝ) :
    ((fun t : ℝ => 2*t-3) ∘ Real.cos) x = 2*Real.cos x-3 ∧
      (Real.cos ∘ (fun t : ℝ => 2*t-3)) x = Real.cos (2*x-3) := ⟨rfl, rfl⟩


theorem affine_cos_compositions_ne :
    ((fun t : ℝ => 2*t-3) ∘ Real.cos) ≠ (Real.cos ∘ (fun t : ℝ => 2*t-3)) := by
  intro h
  have he := congrFun h Real.pi
  have hb := Real.neg_one_le_cos (2*Real.pi-3)
  norm_num [Function.comp_apply, Real.cos_pi] at he hb
  linarith


noncomputable def bijectiveInverse {X Y : Set ℝ} (f : RealFunction X Y) (hf : Bijective f) :
    RealFunction Y X := (Equiv.ofBijective f hf).symm


theorem bijectiveInverse_identities {X Y : Set ℝ} (f : RealFunction X Y) (hf : Bijective f) :
    (∀ x, bijectiveInverse f hf (f x) = x) ∧ (∀ y, f (bijectiveInverse f hf y) = y) :=
  ⟨(Equiv.ofBijective f hf).symm_apply_apply, (Equiv.ofBijective f hf).apply_symm_apply⟩


theorem inverse_graph_coordinate_swap {X Y : Set ℝ} (e : X ≃ Y) (x y : ℝ) :
    (x,y) ∈ realGraph e ↔ (y,x) ∈ realGraph e.symm := by
  constructor
  · rintro ⟨a, h⟩
    refine ⟨e a, ?_⟩
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change x = (a:ℝ) at hx
    change y = (e a:ℝ) at hy
    change (y,x) = ((e a:ℝ),(e.symm (e a):ℝ))
    rw [e.symm_apply_apply]
    exact Prod.ext hy hx
  · rintro ⟨b, h⟩
    refine ⟨e.symm b, ?_⟩
    have hy := congrArg Prod.fst h
    have hx := congrArg Prod.snd h
    change y = (b:ℝ) at hy
    change x = (e.symm b:ℝ) at hx
    change (x,y) = ((e.symm b:ℝ),(e (e.symm b):ℝ))
    rw [e.apply_symm_apply]
    exact Prod.ext hx hy

/-- Bài tập 1(a): khai triển hai biểu thức chứa x²+7. -/
theorem quadratic_substitution_a (a : ℝ) :
    (2*a-1)^2+7 = 4*a^2-4*a+8 ∧ (2*a)^2+7-1 = 4*a^2+6 := by
  constructor <;> ring

/-- Bài tập 1(b): khai triển hai biểu thức chứa exp(3b). -/
theorem quadratic_substitution_b (b : ℝ) :
    (1-Real.exp (3*b))^2+7 = Real.exp (3*b)^2-2*Real.exp (3*b)+8 ∧
      (1:ℝ)^2+7-(Real.exp (3*b)^2+7) = 1-Real.exp (3*b)^2 := by
  constructor <;> ring

/-- Bài tập 1(c): thương sai phân của x²+7, với Δx≠0. -/
theorem quadratic_difference_quotient (x d : ℝ) (hd : d ≠ 0) :
    ((x+d)^2+7-(x^2+7))/d = 2*x+d := by
  field_simp
  ring

/-- Bài tập 2(a): miền xác định là (−∞,−1)∪[1,+∞). -/
theorem rational_radical_domain (x : ℝ) :
    (x+1 ≠ 0 ∧ 0 ≤ (x-1)/(x+1)) ↔ x < -1 ∨ 1 ≤ x := by
  constructor
  · rintro ⟨hne, h⟩
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact Or.inl (by linarith)
    · rcases div_nonneg_iff.mp h with ⟨hnum, _⟩ | ⟨_, hd⟩
      · exact Or.inr (by linarith)
      · linarith
  · rintro (hx | hx)
    · have hd : x+1 < 0 := by linarith
      exact ⟨ne_of_lt hd, div_nonneg_iff.mpr (Or.inr ⟨by linarith, hd.le⟩)⟩
    · exact ⟨by linarith, div_nonneg (by linarith) (by linarith)⟩

/-- Bài tập 2(b): miền xác định gồm các x thỏa cos(x²)≥0. -/
theorem cosine_radical_domain (x : ℝ) :
    x ∈ (fun t : ℝ => Real.cos (t^2)) ⁻¹' Set.Ici 0 ↔ 0 ≤ Real.cos (x^2) := Iff.rfl

/-- Bài tập 2(b): cos(x²)≥0 khi và chỉ khi trị tuyệt đối của góc chính của x² không vượt quá π/2. -/
theorem cosine_radical_domain_principal_phase (x : ℝ) :
    0 ≤ Real.cos (x^2) ↔ |((x^2 : ℝ) : Real.Angle).toReal| ≤ Real.pi/2 := by
  rw [←Real.Angle.cos_coe, Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two]

/-- Bài tập 3(a): miền xác định của căn là [−1,2]. -/
theorem quadratic_radical_domain (x : ℝ) :
    0 ≤ -x^2+x+2 ↔ x ∈ Set.Icc (-1:ℝ) 2 := by
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (x+1)]
    · nlinarith [sq_nonneg (x-2)]
  · rintro ⟨hl, hu⟩
    have := mul_nonneg (show 0 ≤ x+1 by linarith) (show 0 ≤ 2-x by linarith)
    nlinarith

/-- Bài tập 3(a): miền giá trị là [0,3/2]. -/
theorem quadratic_radical_range :
    Set.range (fun x : {x : ℝ | 0 ≤ -x^2+x+2} => Real.sqrt (-(x:ℝ)^2+x+2)) =
      Set.Icc (0:ℝ) (3/2) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩⟩
    nlinarith [sq_nonneg ((x:ℝ)-1/2)]
  · rintro ⟨hy, hu⟩
    have hr : 0 ≤ (9/4:ℝ)-y^2 := by nlinarith
    have hs := Real.sq_sqrt hr
    let x := (1/2:ℝ)+Real.sqrt ((9/4:ℝ)-y^2)
    have he : -x^2+x+2 = y^2 := by dsimp [x]; nlinarith
    refine ⟨⟨x, by change 0 ≤ -x^2+x+2; rw [he]; exact sq_nonneg _⟩, ?_⟩
    change Real.sqrt (-x^2+x+2) = y
    rw [he, Real.sqrt_sq hy]

/-- Bài tập 3(b): miền giá trị là [0,1] trên miền sin(x²)≥0. -/
theorem sine_radical_range :
    Set.range (fun x : {x : ℝ | 0 ≤ Real.sin (x^2)} => Real.sqrt (Real.sin ((x:ℝ)^2))) =
      Set.Icc (0:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (Real.sin_le_one _)⟩
  · rintro ⟨hy, hu⟩
    have hs : y^2 ≤ 1 := by nlinarith
    have ha : 0 ≤ Real.arcsin (y^2) := Real.arcsin_nonneg.mpr (sq_nonneg y)
    have he : Real.sin ((Real.sqrt (Real.arcsin (y^2)))^2) = y^2 := by
      rw [Real.sq_sqrt ha, Real.sin_arcsin (by nlinarith [sq_nonneg y]) hs]
    refine ⟨⟨Real.sqrt (Real.arcsin (y^2)), by change 0 ≤ Real.sin ((Real.sqrt (Real.arcsin (y^2)))^2); rw [he]; exact sq_nonneg _⟩, ?_⟩
    change Real.sqrt (Real.sin ((Real.sqrt (Real.arcsin (y^2)))^2)) = y
    rw [he, Real.sqrt_sq hy]

/-- Bài tập 5(a): phương trình hàm vô nghiệm. -/
theorem sine_functional_equation_no_solution :
    ¬∃ f : ℝ → ℝ, ∀ x, f x * f (x^2-1) = Real.sin x := by
  rintro ⟨f, hf⟩
  have hzero := hf 0
  have hone := hf 1
  have hneg := hf (-1)
  norm_num at hzero hone hneg
  have hs : 0 < Real.sin (1:ℝ) := Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.two_le_pi])
  rcases hzero with hz | hz
  · rw [hz] at hone
    linarith
  · rw [hz] at hneg
    linarith

/-- Bài tập 5(b): nghiệm duy nhất là hàm hằng 0. -/
theorem quadratic_functional_equation_iff_zero (f : ℝ → ℝ) :
    (∀ x y, f (x+y^2) = f (x^2) + f y) ↔ f = 0 := by
  constructor
  · intro h
    have hzero : f 0 = 0 := by
      have hh := h 0 0
      norm_num at hh
      linarith
    have hsq : ∀ x, f (x^2) = f x := by
      intro x
      have hh := h x 0
      simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, hzero] using hh.symm
    have hadd_nonneg : ∀ x y, 0 ≤ y → f (x+y) = f x + f y := by
      intro x y hy
      have hh := h x (Real.sqrt y)
      have hs := hsq (Real.sqrt y)
      rw [Real.sq_sqrt hy] at hh hs
      rw [hsq x, hs.symm] at hh
      exact hh
    have hadd : ∀ x y, f (x+y) = f x + f y := by
      intro x y
      by_cases hy : 0 ≤ y
      · exact hadd_nonneg x y hy
      · have hm : 0 ≤ -y := by linarith
        have hh := hadd_nonneg (x+y) (-y) hm
        have hz := hadd_nonneg y (-y) hm
        simp only [add_neg_cancel, hzero] at hz
        have he : x+y+-y = x := by ring
        rw [he] at hh
        linarith
    funext x
    change f x = 0
    have hsum := hadd (x^2) (x+x+1)
    have hsum2 := hadd (x+x) 1
    have htwo := hadd x x
    have hs := hsq (x+1)
    have hx := hsq x
    have hplus := hadd x 1
    rw [show (x+1)^2 = x^2+(x+x+1) by ring] at hs
    linarith
  · rintro rfl
    simp


noncomputable def piecewiseRoot (x : ℝ) : ℝ := if x < 1 then 1-x else Real.sqrt (x-1)

/-- Bài tập 4: miền giá trị là [0,+∞). -/
theorem piecewise_root_range : Set.range piecewiseRoot = Set.Ici 0 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    unfold piecewiseRoot
    split_ifs with hx
    · change 0 ≤ 1-x
      linarith
    · exact Real.sqrt_nonneg _
  · intro hy
    refine ⟨y^2+1, ?_⟩
    have hx : ¬y^2+1 < 1 := by nlinarith [sq_nonneg y]
    simp [piecewiseRoot, hx, Real.sqrt_sq hy]


def positivePart {D : Type*} (f : D → ℝ) : D → ℝ := fun x => max (f x) 0

/-- Phần âm của giáo trình là f⁻=min(f,0). -/
def signedNegativePart {D : Type*} (f : D → ℝ) : D → ℝ := fun x => min (f x) 0

/-- Bài tập 6(a): phần dương và phần âm của hàm trị tuyệt đối. -/
theorem absolute_positive_signed_negative_parts :
    positivePart (fun x : Set.Icc (-2:ℝ) 2 => |(x:ℝ)+1|) = (fun x : Set.Icc (-2:ℝ) 2 => |(x:ℝ)+1|) ∧
      signedNegativePart (fun x : Set.Icc (-2:ℝ) 2 => |(x:ℝ)+1|) = 0 := by
  constructor <;> funext x
  · exact max_eq_left (abs_nonneg _)
  · change min |(x:ℝ)+1| 0 = 0
    exact min_eq_right (abs_nonneg _)

/-- Bài tập 6(b): hai phần có điểm chuyển nhánh x=1/2. -/
theorem affine_positive_signed_negative_parts (x : ℝ) :
    positivePart (fun t : ℝ => 1-2*t) x = (if x ≤ 1/2 then 1-2*x else 0) ∧
      signedNegativePart (fun t : ℝ => 1-2*t) x = (if x ≤ 1/2 then 0 else 1-2*x) := by
  by_cases hx : x ≤ 1/2
  · simp only [positivePart, signedNegativePart, if_pos hx]
    exact ⟨max_eq_left (by linarith), min_eq_right (by linarith)⟩
  · simp only [positivePart, signedNegativePart, if_neg hx]
    exact ⟨max_eq_right (by linarith), min_eq_left (by linarith)⟩

/-- Bài tập 7(a): hàm hằng −1 bác bỏ công thức với f⁻=min(f,0). -/
theorem signed_negative_part_subtraction_false :
    ¬∀ f : ℝ → ℝ, f = positivePart f - signedNegativePart f := by
  intro h
  have := congrFun (h (fun _ => -1)) 0
  norm_num [positivePart, signedNegativePart] at this

/-- Bài tập 7(a): f=f⁺+f⁻. -/
theorem signed_parts_add_corrected {D : Type*} (f : D → ℝ) :
    f = positivePart f + signedNegativePart f := by
  funext x
  change f x = max (f x) 0 + min (f x) 0
  rw [max_add_min, add_zero]

/-- Bài tập 7(b): f=−2≤g=−1 nhưng g⁻≰f⁻. -/
theorem signed_negative_part_order_reversal_false :
    ¬∀ f g : ℝ → ℝ, (∀ x, f x ≤ g x) ↔
      ((∀ x, positivePart f x ≤ positivePart g x) ∧ (∀ x, signedNegativePart g x ≤ signedNegativePart f x)) := by
  intro h
  have hh := (h (fun _ => -2) (fun _ => -1)).mp (fun _ => by norm_num)
  have := hh.2 0
  norm_num [signedNegativePart] at this

/-- Bài tập 7(b): f≤g suy ra f⁺≤g⁺ và f⁻≤g⁻. -/
theorem signed_parts_order_corrected {D : Type*} (f g : D → ℝ) :
    (∀ x, f x ≤ g x) ↔
      ((∀ x, positivePart f x ≤ positivePart g x) ∧ (∀ x, signedNegativePart f x ≤ signedNegativePart g x)) := by
  constructor
  · intro h
    exact ⟨fun x => max_le_max (h x) le_rfl, fun x => min_le_min (h x) le_rfl⟩
  · rintro ⟨hp, hn⟩ x
    have hfx := congrFun (signed_parts_add_corrected f) x
    have hgx := congrFun (signed_parts_add_corrected g) x
    change f x = positivePart f x + signedNegativePart f x at hfx
    change g x = positivePart g x + signedNegativePart g x at hgx
    rw [hfx, hgx]
    exact add_le_add (hp x) (hn x)

/-- Bài tập 8: f≤g và f≠g không suy ra f(x)<g(x) tại mọi x. -/
theorem nonstrict_distinct_not_pointwise_strict :
    ∃ f g : Set.univ → ℝ, PointwiseLE f g ∧ f ≠ g ∧ ¬PointwiseLT f g := by
  refine ⟨fun _ => 0, fun x => (x:ℝ)^2, fun x => sq_nonneg _, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨1, Set.mem_univ _⟩
    norm_num at this
  · intro h
    have := h ⟨0, Set.mem_univ _⟩
    norm_num at this

/-- Bài tập 9(a): bốn hàm hợp của hàm dấu và trị tuyệt đối. -/
theorem sign_absolute_compositions (x : ℝ) :
    Real.sign (Real.sign x) = Real.sign x ∧
      Real.sign |x| = (if x = 0 then 0 else 1) ∧
      |(|x|)| = |x| ∧ |Real.sign x| = (if x = 0 then 0 else 1) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hne : x ≠ 0 := ne_of_lt hx
    have ha : 0 < |x| := abs_pos.mpr hne
    rw [Real.sign_of_neg hx, Real.sign_of_pos ha]
    norm_num [Real.sign, hne]
  · simp
  · have hne : x ≠ 0 := ne_of_gt hx
    simp [Real.sign_of_pos hx, abs_of_pos hx, hne]


noncomputable def minWithZero (x : ℝ) : ℝ := min x 0
noncomputable def negSquareOfMinWithZero (x : ℝ) : ℝ := -(min x 0)^2


theorem nonpositive_function_branches (x : ℝ) :
    minWithZero x = (if 0 ≤ x then 0 else x) ∧
      negSquareOfMinWithZero x = (if 0 ≤ x then 0 else -x^2) := by
  by_cases hx : 0 ≤ x
  · simp [minWithZero, negSquareOfMinWithZero, hx]
  · simp [minWithZero, negSquareOfMinWithZero, min_eq_left (le_of_not_ge hx), hx]

/-- Bài tập 9(b): bốn hàm hợp, kể cả tại 0. -/
theorem nonpositive_function_compositions (x : ℝ) :
    minWithZero (minWithZero x) = minWithZero x ∧
      minWithZero (negSquareOfMinWithZero x) = negSquareOfMinWithZero x ∧
      negSquareOfMinWithZero (negSquareOfMinWithZero x) = -(min x 0)^4 ∧
      negSquareOfMinWithZero (minWithZero x) = negSquareOfMinWithZero x := by
  have hf : min x 0 ≤ 0 := min_le_right _ _
  have hg : -(min x 0)^2 ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
  simp only [minWithZero, negSquareOfMinWithZero, min_eq_left hf, min_eq_left hg]
  constructor
  · trivial
  constructor
  · trivial
  constructor
  · ring
  · trivial

/-- Bài tập 10(a): √x và x² là hai hàm ngược trên [0,+∞). -/
noncomputable def sqrtNonnegativeEquiv : Set.Ici (0 : ℝ) ≃ Set.Ici (0 : ℝ) where
  toFun x := ⟨Real.sqrt x, Real.sqrt_nonneg _⟩
  invFun y := ⟨(y:ℝ)^2, by change 0 ≤ (y:ℝ)^2; exact sq_nonneg _⟩
  left_inv x := Subtype.ext (Real.sq_sqrt x.property)
  right_inv y := Subtype.ext (Real.sqrt_sq y.property)

/-- Với tập đích ℝ, hàm căn không toàn ánh vì không nhận giá trị −1. -/
theorem sqrt_not_surjective_real :
    ¬Surjective (fun x : Set.Ici (0 : ℝ) => Real.sqrt (x:ℝ)) := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  change Real.sqrt (x:ℝ) = -1 at hx
  have := Real.sqrt_nonneg (x:ℝ)
  rw [hx] at this
  linarith


theorem fractional_linear_preserves_domain (x : ℝ) (hx : x ≠ 1) :
    (x+1)/(x-1) ≠ 1 := by
  have hd : x-1 ≠ 0 := sub_ne_zero.mpr hx
  intro h
  have := (div_eq_iff hd).mp h
  linarith

/-- Bài tập 10(b): phân thức là hàm tự nghịch đảo trên ℝ\{1}. -/
theorem fractional_linear_involutive (x : ℝ) (hx : x ≠ 1) :
    (((x+1)/(x-1))+1)/(((x+1)/(x-1))-1) = x := by
  have hd : x-1 ≠ 0 := sub_ne_zero.mpr hx
  have he : (x+1)/(x-1)-1 ≠ 0 := sub_ne_zero.mpr (fractional_linear_preserves_domain x hx)
  field_simp
  ring


noncomputable def fractionalLinearEquiv : {x : ℝ | x ≠ 1} ≃ {x : ℝ | x ≠ 1} where
  toFun x := ⟨((x:ℝ)+1)/((x:ℝ)-1), fractional_linear_preserves_domain x x.property⟩
  invFun x := ⟨((x:ℝ)+1)/((x:ℝ)-1), fractional_linear_preserves_domain x x.property⟩
  left_inv x := Subtype.ext (fractional_linear_involutive x x.property)
  right_inv x := Subtype.ext (fractional_linear_involutive x x.property)

/-- Với tập đích ℝ, phân thức không toàn ánh vì không nhận giá trị 1. -/
theorem fractional_linear_not_surjective_real :
    ¬Surjective (fun x : {x : ℝ | x ≠ 1} => ((x:ℝ)+1)/((x:ℝ)-1)) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  exact fractional_linear_preserves_domain x x.property hx

end calculus.Chapter03.Section01
