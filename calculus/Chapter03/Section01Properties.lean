import calculus.Chapter03.Section01
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FunProp

/-!
# 3.1. Tính chẵn lẻ, tuần hoàn, đơn điệu và bị chặn

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 274–417.
-/

namespace calculus.Chapter03.Section01Properties

open Set Function


def SymmetricDomain (D : Set ℝ) : Prop := ∀ x ∈ D, -x ∈ D


def EvenFunctionOnSymmetricDomain (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  SymmetricDomain D ∧ ∀ x ∈ D, f (-x) = f x


def OddFunctionOnSymmetricDomain (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  SymmetricDomain D ∧ ∀ x ∈ D, f (-x) = -f x


theorem natural_power_parity (n : ℕ) (_hn : 1 ≤ n) :
    (Even n → EvenFunctionOnSymmetricDomain univ (fun x : ℝ => x^n)) ∧
      (Odd n → OddFunctionOnSymmetricDomain univ (fun x : ℝ => x^n)) := by
  constructor
  · intro hn
    exact ⟨fun _ _ => mem_univ _, fun x _ => hn.neg_pow x⟩
  · intro hn
    exact ⟨fun _ _ => mem_univ _, fun x _ => hn.neg_pow x⟩


theorem affine_shift_neither_even_nor_odd :
    ¬EvenFunctionOnSymmetricDomain univ (fun x : ℝ => x+2) ∧ ¬OddFunctionOnSymmetricDomain univ (fun x : ℝ => x+2) := by
  constructor
  · intro h
    have := h.2 1 (mem_univ _)
    norm_num at this
  · intro h
    have := h.2 0 (mem_univ _)
    norm_num at this


def functionGraph (D : Set ℝ) (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ D ∧ p.2 = f p.1}


theorem even_graph_reflection {D : Set ℝ} {f : ℝ → ℝ} (hf : EvenFunctionOnSymmetricDomain D f) (x y : ℝ) :
    (x,y) ∈ functionGraph D f ↔ (-x,y) ∈ functionGraph D f := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hf.1 x hx, hy.trans (hf.2 x hx).symm⟩
  · rintro ⟨hx, hy⟩
    have hx' := hf.1 (-x) hx
    simp only [neg_neg] at hx'
    exact ⟨hx', hy.trans (hf.2 x hx')⟩


theorem odd_graph_reflection {D : Set ℝ} {f : ℝ → ℝ} (hf : OddFunctionOnSymmetricDomain D f) (x y : ℝ) :
    (x,y) ∈ functionGraph D f ↔ (-x,-y) ∈ functionGraph D f := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hf.1 x hx, by change -y = f (-x); change y = f x at hy; rw [hy, hf.2 x hx]⟩
  · rintro ⟨hx, hy⟩
    have hx' := hf.1 (-x) hx
    simp only [neg_neg] at hx'
    refine ⟨hx', ?_⟩
    rw [hf.2 x hx'] at hy
    exact neg_injective hy


def HasPositiveForwardPeriodOn (D : Set ℝ) (f : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ ∀ x ∈ D, x+T ∈ D ∧ f (x+T) = f x


def HasPositiveForwardPeriod (D : Set ℝ) (f : ℝ → ℝ) : Prop := ∃ T, HasPositiveForwardPeriodOn D f T


def HasLeastPositiveForwardPeriodOn (D : Set ℝ) (f : ℝ → ℝ) (T : ℝ) : Prop :=
  HasPositiveForwardPeriodOn D f T ∧ ∀ S, HasPositiveForwardPeriodOn D f S → T ≤ S


theorem sine_cosine_positive_forward_period :
    HasPositiveForwardPeriodOn univ Real.sin (2*Real.pi) ∧ HasPositiveForwardPeriodOn univ Real.cos (2*Real.pi) := by
  exact ⟨⟨by positivity, fun x _ => ⟨mem_univ _, Real.sin_add_two_pi x⟩⟩,
    ⟨by positivity, fun x _ => ⟨mem_univ _, Real.cos_add_two_pi x⟩⟩⟩


theorem positive_cosine_one_period_bound {S : ℝ} (hS : 0 < S) (hcos : Real.cos S = 1) :
    2*Real.pi ≤ S := by
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff S).mp hcos
  have hkpos : (0:ℝ) < (k:ℝ) := by nlinarith [Real.pi_pos]
  have hkint : (0:ℤ) < k := by exact_mod_cast hkpos
  have hkone : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
  nlinarith [Real.pi_pos]


theorem sine_cosine_least_positive_forward_period :
    HasLeastPositiveForwardPeriodOn univ Real.sin (2*Real.pi) ∧
      HasLeastPositiveForwardPeriodOn univ Real.cos (2*Real.pi) := by
  constructor
  · refine ⟨sine_cosine_positive_forward_period.1, ?_⟩
    intro S hS
    apply positive_cosine_one_period_bound hS.1
    have he := (hS.2 (Real.pi/2) (mem_univ _)).2
    simpa [Real.sin_add] using he
  · refine ⟨sine_cosine_positive_forward_period.2, ?_⟩
    intro S hS
    apply positive_cosine_one_period_bound hS.1
    have he := (hS.2 0 (mem_univ _)).2
    simpa using he


theorem affine_shift_not_periodic : ¬HasPositiveForwardPeriod univ (fun x : ℝ => x+2) := by
  rintro ⟨T,hT⟩
  have he := (hT.2 0 (mem_univ _)).2
  dsimp at he
  linarith [hT.1]


theorem positive_forward_period_operations {D : Set ℝ} {f g : ℝ → ℝ} {T : ℝ}
    (hf : HasPositiveForwardPeriodOn D f T) (hg : HasPositiveForwardPeriodOn D g T) (c : ℝ) :
    HasPositiveForwardPeriodOn D (fun x => f x+g x) T ∧
      HasPositiveForwardPeriodOn D (fun x => c*f x) T ∧ HasPositiveForwardPeriodOn D (fun x => f x*g x) T := by
  refine ⟨⟨hf.1, ?_⟩, ⟨hf.1, ?_⟩, ⟨hf.1, ?_⟩⟩ <;> intro x hx
  · exact ⟨(hf.2 x hx).1, by dsimp only; rw [(hf.2 x hx).2, (hg.2 x hx).2]⟩
  · exact ⟨(hf.2 x hx).1, by dsimp only; rw [(hf.2 x hx).2]⟩
  · exact ⟨(hf.2 x hx).1, by dsimp only; rw [(hf.2 x hx).2, (hg.2 x hx).2]⟩


theorem positive_forward_period_reciprocal {D : Set ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hf : HasPositiveForwardPeriodOn D f T) (_hzero : ∀ x ∈ D, f x ≠ 0) :
    HasPositiveForwardPeriodOn D (fun x => 1/f x) T := by
  refine ⟨hf.1, ?_⟩
  intro x hx
  exact ⟨(hf.2 x hx).1, by dsimp only; rw [(hf.2 x hx).2]⟩


structure IntervalDomain where
  carrier : Set ℝ
  interval : Set.OrdConnected carrier


def FunctionIncreasing (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ D.carrier, ∀ y ∈ D.carrier, x < y → f x ≤ f y


def FunctionDecreasing (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ D.carrier, ∀ y ∈ D.carrier, x < y → f y ≤ f x


def FunctionStrictlyIncreasing (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ D.carrier, ∀ y ∈ D.carrier, x < y → f x < f y


def FunctionStrictlyDecreasing (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ D.carrier, ∀ y ∈ D.carrier, x < y → f y < f x


def FunctionMonotonic (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  FunctionIncreasing D f ∨ FunctionDecreasing D f


def FunctionStrictlyMonotonic (D : IntervalDomain) (f : ℝ → ℝ) : Prop :=
  FunctionStrictlyIncreasing D f ∨ FunctionStrictlyDecreasing D f


theorem function_increasing_iff_monotoneOn (D : IntervalDomain) (f : ℝ → ℝ) :
    FunctionIncreasing D f ↔ MonotoneOn f D.carrier := by
  constructor
  · intro h x hx y hy hxy
    rcases hxy.eq_or_lt with he | he
    · exact he ▸ le_rfl
    · exact h x hx y hy he
  · intro h x hx y hy hxy
    exact h hx hy hxy.le


theorem function_decreasing_iff_antitoneOn (D : IntervalDomain) (f : ℝ → ℝ) :
    FunctionDecreasing D f ↔ AntitoneOn f D.carrier := by
  constructor
  · intro h x hx y hy hxy
    rcases hxy.eq_or_lt with he | he
    · exact he ▸ le_rfl
    · exact h x hx y hy he
  · intro h x hx y hy hxy
    exact h hx hy hxy.le


theorem square_and_half_power_monotonicity :
    MonotoneOn (fun x : ℝ => x^2) (Set.Ici 0) ∧ Antitone (fun x : ℝ => (1/2:ℝ)^x) := by
  constructor
  · intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    change x^2 ≤ y^2
    nlinarith
  · exact (Real.strictAnti_rpow_of_base_lt_one (by norm_num) (by norm_num)).antitone


theorem square_not_monotone : ¬Monotone (fun x : ℝ => x^2) ∧ ¬Antitone (fun x : ℝ => x^2) := by
  constructor
  · intro h
    have := h (show (-1:ℝ) ≤ 0 by norm_num)
    norm_num at this
  · intro h
    have := h (show (0:ℝ) ≤ 1 by norm_num)
    norm_num at this


theorem function_increasing_add {D : IntervalDomain} {f g : ℝ → ℝ}
    (hf : FunctionIncreasing D f) (hg : FunctionIncreasing D g) :
    FunctionIncreasing D (fun x => f x+g x) := by
  intro x hx y hy hxy
  exact add_le_add (hf x hx y hy hxy) (hg x hx y hy hxy)


theorem function_increasing_neg {D : IntervalDomain} {f : ℝ → ℝ}
    (hf : FunctionIncreasing D f) : FunctionDecreasing D (fun x => -f x) := by
  intro x hx y hy hxy
  exact neg_le_neg (hf x hx y hy hxy)


theorem function_increasing_nonnegative_mul {D : IntervalDomain} {f g : ℝ → ℝ}
    (hf : FunctionIncreasing D f) (hg : FunctionIncreasing D g)
    (hf0 : ∀ x ∈ D.carrier, 0 ≤ f x) (hg0 : ∀ x ∈ D.carrier, 0 ≤ g x) :
    FunctionIncreasing D (fun x => f x*g x) := by
  intro x hx y hy hxy
  exact mul_le_mul (hf x hx y hy hxy) (hg x hx y hy hxy) (hg0 x hx) (hf0 y hy)


def FunctionBoundedAboveOn (D : Set ℝ) (f : ℝ → ℝ) : Prop := ∃ M, ∀ x ∈ D, f x ≤ M


def FunctionBoundedBelowOn (D : Set ℝ) (f : ℝ → ℝ) : Prop := ∃ m, ∀ x ∈ D, m ≤ f x


def FunctionBoundedOn (D : Set ℝ) (f : ℝ → ℝ) : Prop := ∃ m M, ∀ x ∈ D, m ≤ f x ∧ f x ≤ M


theorem constant_functionBoundedOn (D : Set ℝ) (c : ℝ) : FunctionBoundedOn D (fun _ => c) :=
  ⟨c,c,fun _ _ => ⟨le_rfl,le_rfl⟩⟩


theorem identity_not_bounded : ¬FunctionBoundedAboveOn univ (fun x : ℝ => x) ∧
    ¬FunctionBoundedOn univ (fun x : ℝ => x) := by
  have hh : ¬FunctionBoundedAboveOn univ (fun x : ℝ => x) := by
    rintro ⟨M,hM⟩
    have := hM (M+1) (mem_univ _)
    linarith
  refine ⟨hh, ?_⟩
  rintro ⟨m,M,h⟩
  exact hh ⟨M,fun x hx => (h x hx).2⟩


theorem functionBoundedOn_iff_absolute_bound (D : Set ℝ) (f : ℝ → ℝ) :
    FunctionBoundedOn D f ↔ ∃ M, 0 < M ∧ ∀ x ∈ D, |f x| ≤ M := by
  constructor
  · rintro ⟨m,M,h⟩
    let A := max |m| |M|+1
    have hA : 0 < A := by dsimp [A]; linarith [le_max_left |m| |M|, abs_nonneg m]
    refine ⟨A,hA,?_⟩
    intro x hx
    rw [abs_le]
    have hb := h x hx
    have hm := neg_abs_le m
    have hM := le_abs_self M
    have ha := le_max_left |m| |M|
    have hB := le_max_right |m| |M|
    dsimp [A]
    constructor <;> linarith
  · rintro ⟨M,hM,h⟩
    exact ⟨-M,M,fun x hx => (abs_le.mp (h x hx))⟩


theorem functionBoundedAboveOn_add {D : Set ℝ} {f g : ℝ → ℝ}
    (hf : FunctionBoundedAboveOn D f) (hg : FunctionBoundedAboveOn D g) :
    FunctionBoundedAboveOn D (fun x => f x+g x) := by
  rcases hf with ⟨M,hM⟩
  rcases hg with ⟨N,hN⟩
  exact ⟨M+N,fun x hx => add_le_add (hM x hx) (hN x hx)⟩


theorem functionBoundedAboveOn_nonnegative_mul {D : Set ℝ} {f g : ℝ → ℝ}
    (hf : FunctionBoundedAboveOn D f) (hg : FunctionBoundedAboveOn D g)
    (_hf0 : ∀ x ∈ D, 0 ≤ f x) (hg0 : ∀ x ∈ D, 0 ≤ g x) :
    FunctionBoundedAboveOn D (fun x => f x*g x) := by
  rcases hf with ⟨M,hM⟩
  rcases hg with ⟨N,hN⟩
  refine ⟨max M 0*max N 0,?_⟩
  intro x hx
  exact mul_le_mul ((hM x hx).trans (le_max_left _ _)) ((hN x hx).trans (le_max_left _ _))
    (hg0 x hx) (le_max_right _ _)

/-- Bài tập 12(a): đa thức là hàm lẻ. -/
theorem exercise12a_odd : OddFunctionOnSymmetricDomain univ (fun x : ℝ => x^5-2*x^3) := by
  refine ⟨fun _ _ => mem_univ _, ?_⟩
  intro x _
  ring

/-- Bài tập 12(b): đa thức là hàm chẵn. -/
theorem exercise12b_even : EvenFunctionOnSymmetricDomain univ (fun x : ℝ => -x^6-2*x^2+7) := by
  refine ⟨fun _ _ => mem_univ _, ?_⟩
  intro x _
  ring

/-- Bài tập 12(c): hàm không chẵn, không lẻ. -/
theorem exercise12c_neither :
    ¬EvenFunctionOnSymmetricDomain univ (fun x : ℝ => x^8-x^7+x^6-2*x^3+9) ∧
      ¬OddFunctionOnSymmetricDomain univ (fun x : ℝ => x^8-x^7+x^6-2*x^3+9) := by
  constructor
  · intro h
    have := h.2 1 (mem_univ _)
    norm_num at this
  · intro h
    have := h.2 0 (mem_univ _)
    norm_num at this

/-- Bài tập 12(d): hàm chứa trị tuyệt đối vẫn không chẵn. -/
theorem exercise12d_neither :
    ¬EvenFunctionOnSymmetricDomain univ (fun x : ℝ => |x^7-3*x^2+1|) ∧
      ¬OddFunctionOnSymmetricDomain univ (fun x : ℝ => |x^7-3*x^2+1|) := by
  constructor
  · intro h
    have := h.2 1 (mem_univ _)
    norm_num at this
  · intro h
    have := h.2 0 (mem_univ _)
    norm_num at this

/-- Bài tập 12(e): hàm chẵn. -/
theorem exercise12e_even : EvenFunctionOnSymmetricDomain univ (fun x : ℝ => |x|^9-x^8+3*|x|) := by
  refine ⟨fun _ _ => mem_univ _, ?_⟩
  intro x _
  dsimp only
  rw [abs_neg]
  ring

/-- Bài tập 13 và 15: hàm 1/x được gán giá trị 0 tại x=0. -/
noncomputable def realReciprocal (x : ℝ) : ℝ := if x ≠ 0 then 1/x else 0


theorem real_reciprocal_eq (x : ℝ) : realReciprocal x = x⁻¹ := by
  by_cases hx : x=0 <;> simp [realReciprocal, hx, one_div]

/-- Bài tập 13(a): hàm nghịch đảo mở rộng tại 0 không đơn điệu trên ℝ. -/
theorem exercise13a_not_monotone : ¬Monotone realReciprocal ∧ ¬Antitone realReciprocal := by
  constructor
  · intro h
    have := h (show (1:ℝ) ≤ 2 by norm_num)
    norm_num [realReciprocal] at this
  · intro h
    have := h (show (0:ℝ) ≤ 1 by norm_num)
    norm_num [realReciprocal] at this

/-- Bài tập 13(b): phần thập phân không đơn điệu trên ℝ. -/
theorem exercise13b_not_monotone :
    ¬Monotone (fun x : ℝ => Int.fract x) ∧ ¬Antitone (fun x : ℝ => Int.fract x) := by
  constructor
  · intro h
    have := h (show (1/2:ℝ) ≤ 1 by norm_num)
    norm_num [Int.fract] at this
  · intro h
    have := h (show (0:ℝ) ≤ 1/2 by norm_num)
    norm_num [Int.fract] at this

/-- Bài tập 14(a): hàm phần nguyên không tuần hoàn. -/
theorem exercise14a_floor_not_periodic :
    ¬HasPositiveForwardPeriod univ (fun x : ℝ => (⌊x⌋ : ℝ)) := by
  rintro ⟨T,hT⟩
  have he := (hT.2 (-T/2) (mem_univ _)).2
  have hneg : (⌊-T/2⌋ : ℝ) < 0 := lt_of_le_of_lt (Int.floor_le (-T/2)) (by linarith [hT.1])
  have hnonneg : (0:ℝ) ≤ (⌊-T/2+T⌋ : ℝ) := by
    exact_mod_cast (Int.floor_nonneg.mpr (show (0:ℝ) ≤ -T/2+T by linarith [hT.1]))
  linarith

/-- Bài tập 14(b): phần thập phân có chu kì 1. -/
theorem exercise14b_fractional_period : HasPositiveForwardPeriodOn univ (fun x : ℝ => Int.fract x) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro x _
  exact ⟨mem_univ _, Int.fract_add_one x⟩


theorem fractional_least_period : HasLeastPositiveForwardPeriodOn univ (fun x : ℝ => Int.fract x) 1 := by
  refine ⟨exercise14b_fractional_period, ?_⟩
  intro T hT
  have he := (hT.2 0 (mem_univ _)).2
  change Int.fract (0+T) = Int.fract (0:ℝ) at he
  rw [zero_add, Int.fract_zero] at he
  have hfloor : (⌊T⌋ : ℝ) = T := by change T-(⌊T⌋:ℝ)=0 at he; linarith
  have hp : (0:ℤ) < ⌊T⌋ := by exact_mod_cast (show (0:ℝ) < (⌊T⌋ : ℝ) by linarith [hT.1])
  have hone : (1:ℝ) ≤ (⌊T⌋ : ℝ) := by exact_mod_cast (show (1:ℤ) ≤ ⌊T⌋ by omega)
  linarith


theorem exercise15a_not_boundedAbove : ¬FunctionBoundedAboveOn univ realReciprocal := by
  rintro ⟨M,hM⟩
  let A := max M 0+1
  have he : realReciprocal A⁻¹ = A := by rw [real_reciprocal_eq, inv_inv]
  have h := hM A⁻¹ (mem_univ _)
  rw [he] at h
  dsimp [A] at h
  linarith [le_max_left M 0]


theorem exercise15a_not_boundedBelow : ¬FunctionBoundedBelowOn univ realReciprocal := by
  rintro ⟨m,hm⟩
  let A := max (-m) 0+1
  have h := hm (-A⁻¹) (mem_univ _)
  rw [real_reciprocal_eq, inv_neg, inv_inv] at h
  dsimp [A] at h
  linarith [le_max_left (-m) 0]

/-- Bài tập 15(a): hàm không bị chặn. -/
theorem exercise15a_not_bounded : ¬FunctionBoundedOn univ realReciprocal := by
  rintro ⟨m,M,h⟩
  exact exercise15a_not_boundedAbove ⟨M,fun x hx => (h x hx).2⟩

/-- Bài tập 15(b): phần thập phân thuộc [0,1). -/
theorem exercise15b_fractional_bounded : FunctionBoundedOn univ (fun x : ℝ => Int.fract x) :=
  ⟨0,1,fun x _ => ⟨Int.fract_nonneg x,(Int.fract_lt_one x).le⟩⟩


theorem exercise15c_min_quadratics_boundedBelow :
    FunctionBoundedBelowOn univ (fun x : ℝ => min (x^2-3*x+2) (x^2-5*x+6)) := by
  refine ⟨-1/4, ?_⟩
  intro x _
  apply le_min <;> nlinarith [sq_nonneg (x-3/2), sq_nonneg (x-5/2)]


theorem exercise15c_min_quadratics_not_boundedAbove :
    ¬FunctionBoundedAboveOn univ (fun x : ℝ => min (x^2-3*x+2) (x^2-5*x+6)) := by
  rintro ⟨M,hM⟩
  have h := hM (|M|+8) (mem_univ _)
  have h1 : M < (|M|+8)^2-3*(|M|+8)+2 := by nlinarith [sq_nonneg |M|,le_abs_self M,abs_nonneg M]
  have h2 : M < (|M|+8)^2-5*(|M|+8)+6 := by nlinarith [sq_nonneg |M|,le_abs_self M,abs_nonneg M]
  have hh := lt_min h1 h2
  exact (not_lt_of_ge h) hh

/-- Bài tập 15(c): hàm không bị chặn. -/
theorem exercise15c_min_quadratics_not_bounded :
    ¬FunctionBoundedOn univ (fun x : ℝ => min (x^2-3*x+2) (x^2-5*x+6)) := by
  rintro ⟨m,M,h⟩
  exact exercise15c_min_quadratics_not_boundedAbove ⟨M,fun x hx => (h x hx).2⟩


theorem constant_has_no_least_positive_forward_period (c : ℝ) :
    (∀ T, 0 < T → HasPositiveForwardPeriodOn univ (fun _ : ℝ => c) T) ∧
      ¬∃ T, HasLeastPositiveForwardPeriodOn univ (fun _ : ℝ => c) T := by
  constructor
  · intro T hT
    exact ⟨hT, fun _ _ => ⟨mem_univ _,rfl⟩⟩
  · rintro ⟨T,hT⟩
    have hp : HasPositiveForwardPeriodOn univ (fun _ : ℝ => c) (T/2) :=
      ⟨by linarith [hT.1.1],fun _ _ => ⟨mem_univ _,rfl⟩⟩
    have := hT.2 (T/2) hp
    linarith [hT.1.1]

/-- sin và −sin có chu kì dương nhỏ nhất; tổng của chúng không có chu kì dương nhỏ nhất. -/
theorem least_period_sum_claim_counterexample :
    HasLeastPositiveForwardPeriodOn univ Real.sin (2*Real.pi) ∧
      HasLeastPositiveForwardPeriodOn univ (fun x => -Real.sin x) (2*Real.pi) ∧
      ¬∃ T, HasLeastPositiveForwardPeriodOn univ (fun x => Real.sin x + -Real.sin x) T := by
  refine ⟨sine_cosine_least_positive_forward_period.1, ?_, ?_⟩
  · refine ⟨⟨by positivity, fun x _ => ⟨mem_univ _, by dsimp only; rw [Real.sin_add_two_pi]⟩⟩,?_⟩
    intro T hT
    apply sine_cosine_least_positive_forward_period.1.2 T
    exact ⟨hT.1,fun x hx => ⟨(hT.2 x hx).1,neg_injective (hT.2 x hx).2⟩⟩
  · simpa only [add_neg_cancel] using (constant_has_no_least_positive_forward_period 0).2


def realIntervalDomain : IntervalDomain := ⟨univ, Set.ordConnected_univ⟩


theorem functionMonotonic_real_iff (f : ℝ → ℝ) :
    FunctionMonotonic realIntervalDomain f ↔ Monotone f ∨ Antitone f := by
  change (FunctionIncreasing realIntervalDomain f ∨ FunctionDecreasing realIntervalDomain f) ↔ _
  rw [function_increasing_iff_monotoneOn, function_decreasing_iff_antitoneOn]
  simp only [realIntervalDomain, monotoneOn_univ, antitoneOn_univ]

/-- Ví dụ hàm bình phương và Bài tập 13: hàm không đơn điệu trên ℝ. -/
theorem global_function_nonmonotonicity_examples :
    ¬FunctionMonotonic realIntervalDomain (fun x : ℝ => x^2) ∧
      ¬FunctionMonotonic realIntervalDomain realReciprocal ∧
      ¬FunctionMonotonic realIntervalDomain (fun x : ℝ => Int.fract x) := by
  refine ⟨?_,?_,?_⟩ <;> rw [functionMonotonic_real_iff] <;> rintro (h|h)
  · exact square_not_monotone.1 h
  · exact square_not_monotone.2 h
  · exact exercise13a_not_monotone.1 h
  · exact exercise13a_not_monotone.2 h
  · exact exercise13b_not_monotone.1 h
  · exact exercise13b_not_monotone.2 h


theorem functionBoundedOn_iff_abs_boundedAbove (D : Set ℝ) (f : ℝ → ℝ) :
    FunctionBoundedOn D f ↔ FunctionBoundedAboveOn D (fun x => |f x|) := by
  rw [functionBoundedOn_iff_absolute_bound]
  constructor
  · rintro ⟨M,_,hM⟩
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    refine ⟨max M 0+1, by linarith [le_max_right M 0], ?_⟩
    intro x hx
    exact (hM x hx).trans (by linarith [le_max_left M 0])


theorem least_positive_forward_period_reciprocal {D : Set ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hf : HasLeastPositiveForwardPeriodOn D f T) (hzero : ∀ x ∈ D, f x ≠ 0) :
    HasLeastPositiveForwardPeriodOn D (fun x => 1/f x) T := by
  refine ⟨positive_forward_period_reciprocal hf.1 hzero,?_⟩
  intro S hS
  apply hf.2 S
  refine ⟨hS.1,?_⟩
  intro x hx
  refine ⟨(hS.2 x hx).1,?_⟩
  have he := congrArg (fun y : ℝ => y⁻¹) (hS.2 x hx).2
  simpa only [one_div,inv_inv] using he

end calculus.Chapter03.Section01Properties
