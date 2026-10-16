import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# 2.1. Số thực: đại số, thứ tự và tính đầy đủ

Nguồn: `source/Ch2_dayso.tex`, dòng 14–588.
-/

open scoped Pointwise

namespace calculus.Chapter02.Section01

/-! ## Các tính chất trường và thứ tự (A1–A9, O1–O4) -/

/-- A1: tính kết hợp của phép cộng. -/
theorem addition_assoc (a b c : ℝ) : a + (b + c) = (a + b) + c :=
  (add_assoc a b c).symm

/-- A2: tính giao hoán của phép cộng. -/
theorem addition_comm (a b : ℝ) : a + b = b + a := add_comm a b

/-- A3: tồn tại duy nhất phần tử trung hòa của phép cộng. -/
theorem existsUnique_additive_identity : ∃! z : ℝ, ∀ a : ℝ, a + z = a := by
  refine ⟨0, fun a ↦ add_zero a, ?_⟩
  intro z hz
  simpa using hz 0

/-- A4: mỗi số thực có duy nhất một số đối. -/
theorem existsUnique_additive_inverse (a : ℝ) : ∃! x : ℝ, a + x = 0 := by
  refine ⟨-a, add_neg_cancel a, ?_⟩
  intro x hx
  linarith

/-- A5: tính kết hợp của phép nhân. -/
theorem multiplication_assoc (a b c : ℝ) : a * (b * c) = (a * b) * c :=
  (mul_assoc a b c).symm

/-- A6: tính giao hoán của phép nhân. -/
theorem multiplication_comm (a b : ℝ) : a * b = b * a := mul_comm a b

/-- A7: tồn tại duy nhất phần tử trung hòa khác không của phép nhân. -/
theorem existsUnique_multiplicative_identity :
    ∃! u : ℝ, u ≠ 0 ∧ ∀ a : ℝ, u * a = a := by
  refine ⟨1, ⟨one_ne_zero, fun a ↦ one_mul a⟩, ?_⟩
  intro u hu
  simpa using hu.2 1

/-- A8: mỗi số thực khác 0 có duy nhất một nghịch đảo. -/
theorem existsUnique_multiplicative_inverse (a : ℝ) (ha : a ≠ 0) :
    ∃! x : ℝ, a * x = 1 := by
  refine ⟨a⁻¹, mul_inv_cancel₀ ha, ?_⟩
  intro x hx
  exact (mul_left_cancel₀ ha (hx.trans (mul_inv_cancel₀ ha).symm))

/-- A9: phân phối của phép nhân qua phép cộng. -/
theorem multiplication_distributes (a b c : ℝ) : a * (b + c) = a * b + a * c :=
  mul_add a b c

/-- O1: hai số thực thỏa đúng một trong ba quan hệ <, =, >. -/
theorem order_trichotomy (a b : ℝ) : a < b ∨ a = b ∨ b < a := lt_trichotomy a b

/-- O2: tính bắc cầu của thứ tự ngặt. -/
theorem order_transitivity {a b c : ℝ} (hab : a < b) (hbc : b < c) : a < c :=
  lt_trans hab hbc

/-- O3: cộng cùng một số bảo toàn bất đẳng thức ngặt. -/
theorem add_preserves_lt {a b : ℝ} (hab : a < b) (c : ℝ) : a + c < b + c :=
  by simpa only [add_comm c] using add_lt_add_right hab c

/-- O4: nhân với số dương bảo toàn bất đẳng thức ngặt. -/
theorem positive_mul_preserves_lt {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := mul_lt_mul_of_pos_right hab hc

/-! ## Giá trị tuyệt đối, khoảng và cận -/

/-- Định nghĩa 2.1.1: |x|=x khi x≥0, |x|=−x khi x<0. -/
theorem abs_eq_piecewise (x : ℝ) : |x| = if 0 ≤ x then x else -x := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_neg (lt_of_not_ge h)

/-- Mệnh đề 2.1.2(i): |x|≥0. -/
theorem absoluteValue_nonneg (x : ℝ) : 0 ≤ |x| := abs_nonneg x

/-- Mệnh đề 2.1.2(ii): |x|=0 khi và chỉ khi x=0. -/
theorem absoluteValue_eq_zero_iff (x : ℝ) : |x| = 0 ↔ x = 0 := abs_eq_zero

/-- Mệnh đề 2.1.2(iii): |−x|=|x|. -/
theorem absoluteValue_neg (x : ℝ) : |-x| = |x| := abs_neg x

/-- Mệnh đề 2.1.2(iv): |x|²=x². -/
theorem absoluteValue_sq (x : ℝ) : |x| ^ 2 = x ^ 2 := sq_abs x

/-- Mệnh đề 2.1.2(v): −|x|≤x≤|x|. -/
theorem absoluteValue_bounds (x : ℝ) : -|x| ≤ x ∧ x ≤ |x| :=
  ⟨neg_abs_le x, le_abs_self x⟩

/-- Mệnh đề 2.1.2(vi): |xy|=|x||y|. -/
theorem absoluteValue_mul (x y : ℝ) : |x * y| = |x| * |y| := abs_mul x y

/-- Mệnh đề 2.1.2(vii): |x/y|=|x|/|y|, với y≠0. -/
theorem absoluteValue_div (x y : ℝ) (_hy : y ≠ 0) : |x / y| = |x| / |y| :=
  abs_div x y

/-- Mệnh đề 2.1.2(viii): |x|≤M khi và chỉ khi −M≤x≤M, với M>0. -/
theorem absoluteValue_le_iff (x M : ℝ) (_hM : 0 < M) :
    |x| ≤ M ↔ -M ≤ x ∧ x ≤ M := abs_le

/-- Mệnh đề 2.1.2(ix): |x|≥M khi và chỉ khi x≤−M hoặc x≥M, với M>0. -/
theorem le_absoluteValue_iff (x M : ℝ) (_hM : 0 < M) :
    M ≤ |x| ↔ x ≤ -M ∨ M ≤ x := by
  rw [le_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl h

/-- Định lí 2.1.3(i), Bài tập 2.1.1: bất đẳng thức tam giác. -/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y

/-- Định lí 2.1.3(ii): bất đẳng thức tam giác ngược. -/
theorem reverse_triangle_inequality (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| :=
  abs_abs_sub_abs_le_abs_sub x y

/-- Điều kiện dấu bằng của bất đẳng thức tam giác trong Định lí 2.1.3. -/
theorem triangle_equality_iff (x y : ℝ) : |x + y| = |x| + |y| ↔ 0 ≤ x * y := by
  rw [abs_add_eq_add_abs_iff]
  constructor
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact mul_nonneg hx hy
    · exact mul_nonneg_of_nonpos_of_nonpos hx hy
  · intro h
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · exact Or.inl ⟨hx, hy⟩
      · have hx0 : x = 0 := by nlinarith
        exact Or.inr ⟨hx0.le, le_of_not_ge hy⟩
    · have hy : y ≤ 0 := by nlinarith
      exact Or.inr ⟨le_of_not_ge hx, hy⟩

/-- Định lí 2.1.3: điều kiện dấu bằng của bất đẳng thức tam giác ngược. -/
theorem reverse_triangle_equality_iff (x y : ℝ) :
    |(|x| - |y|)| = |x - y| ↔ 0 ≤ x * y := by
  constructor
  · intro h
    have hsq := congrArg (fun z : ℝ ↦ z ^ 2) h
    rw [sq_abs, sq_abs] at hsq
    have hx := sq_abs x
    have hy := sq_abs y
    have hxy := mul_nonneg (abs_nonneg x) (abs_nonneg y)
    nlinarith
  · intro h
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · rw [abs_of_nonneg hx, abs_of_nonneg hy]
      · have hx0 : x = 0 := by nlinarith
        subst x
        simp
    · have hy : y ≤ 0 := by nlinarith
      rw [abs_of_nonpos (le_of_not_ge hx), abs_of_nonpos hy]
      simp only [neg_sub_neg, abs_sub_comm]

/-- Nhận xét 2.1.4: ba tính chất khoảng cách trên trục số. -/
theorem real_distance_properties (x y z : ℝ) :
    0 ≤ |x - y| ∧ (|x - y| = 0 ↔ x = y) ∧
      |x - z| ≤ |x - y| + |y - z| := by
  refine ⟨abs_nonneg _, ?_, ?_⟩
  · rw [abs_eq_zero, sub_eq_zero]
  ·
    have h := abs_add_le (x - y) (y - z)
    simpa only [sub_add_sub_cancel] using h

/-- Nhận xét 2.1.5: khoảng đóng tâm `a` và bán kính không âm. -/
theorem abs_sub_le_iff_interval (x a ε : ℝ) (_hε : 0 ≤ ε) :
    |x - a| ≤ ε ↔ a - ε ≤ x ∧ x ≤ a + ε := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Định nghĩa 2.1.6: chín loại khoảng trên trục số. -/
theorem interval_membership (a b x : ℝ) (_hab : a < b) :
    (x ∈ Set.Ioo a b ↔ a < x ∧ x < b) ∧
    (x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b) ∧
    (x ∈ Set.Ioc a b ↔ a < x ∧ x ≤ b) ∧
    (x ∈ Set.Ico a b ↔ a ≤ x ∧ x < b) ∧
    (x ∈ Set.Ioi a ↔ a < x) ∧ (x ∈ Set.Ici a ↔ a ≤ x) ∧
    (x ∈ Set.Iio b ↔ x < b) ∧ (x ∈ Set.Iic b ↔ x ≤ b) ∧
    x ∈ (Set.univ : Set ℝ) := by simp

/-- Định nghĩa 2.1.7: cận trên, cận dưới và tính bị chặn. -/
theorem bounds_definitions (A : Set ℝ) (m M : ℝ) :
    (M ∈ upperBounds A ↔ ∀ x ∈ A, x ≤ M) ∧
    (m ∈ lowerBounds A ↔ ∀ x ∈ A, m ≤ x) ∧
    (BddAbove A ↔ ∃ M, ∀ x ∈ A, x ≤ M) ∧
    (BddBelow A ↔ ∃ m, ∀ x ∈ A, m ≤ x) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Ví dụ 2.1.8: `(0,1)` có cận trên 2 và cận dưới 0. -/
theorem openUnitInterval_bounds :
    (2 : ℝ) ∈ upperBounds (Set.Ioo 0 1) ∧
    (0 : ℝ) ∈ lowerBounds (Set.Ioo 0 1) ∧
    BddAbove (Set.Ioo (0 : ℝ) 1) ∧ BddBelow (Set.Ioo (0 : ℝ) 1) := by
  have hupper : (2 : ℝ) ∈ upperBounds (Set.Ioo 0 1) := by
    intro x hx
    linarith [hx.2]
  have hlower : (0 : ℝ) ∈ lowerBounds (Set.Ioo 0 1) := fun _ hx ↦ hx.1.le
  exact ⟨hupper, hlower, ⟨2, hupper⟩, ⟨0, hlower⟩⟩

/-- Nhận xét 2.1.9(i): nới một cận bảo toàn tính chất là cận. -/
theorem weaken_bounds {A : Set ℝ} {m m' M M' : ℝ}
    (hM : M ∈ upperBounds A) (hm : m ∈ lowerBounds A)
    (hMM' : M ≤ M') (hm'm : m' ≤ m) :
    M' ∈ upperBounds A ∧ m' ∈ lowerBounds A :=
  ⟨fun _ hx ↦ le_trans (hM hx) hMM', fun _ hx ↦ le_trans hm'm (hm hx)⟩

/-- Nhận xét 2.1.9(i): tăng một cận trên vẫn được cận trên. -/
theorem weaken_upper_bound {A : Set ℝ} {M M' : ℝ}
    (hM : M ∈ upperBounds A) (hMM' : M ≤ M') : M' ∈ upperBounds A :=
  fun _ hx ↦ le_trans (hM hx) hMM'

/-- Nhận xét 2.1.9(i): giảm một cận dưới vẫn được cận dưới. -/
theorem weaken_lower_bound {A : Set ℝ} {m m' : ℝ}
    (hm : m ∈ lowerBounds A) (hm'm : m' ≤ m) : m' ∈ lowerBounds A :=
  fun _ hx ↦ le_trans hm'm (hm hx)

/-- Nhận xét 2.1.9(ii): hai cận tương đương một cận dương cho trị tuyệt đối. -/
theorem bounded_iff_absoluteValue_bounded (A : Set ℝ) :
    (BddAbove A ∧ BddBelow A) ↔ ∃ M : ℝ, 0 < M ∧ ∀ x ∈ A, |x| ≤ M := by
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨l, hl⟩⟩
    refine ⟨|u| + |l| + 1, by linarith [abs_nonneg u, abs_nonneg l], ?_⟩
    intro x hx
    apply abs_le.mpr
    constructor <;> linarith [hu hx, hl hx, le_abs_self u, neg_abs_le l,
      abs_nonneg u, abs_nonneg l]
  · rintro ⟨M, _, hM⟩
    exact ⟨⟨M, fun x hx ↦ (abs_le.mp (hM x hx)).2⟩,
      ⟨-M, fun x hx ↦ (abs_le.mp (hM x hx)).1⟩⟩

/-- Nhận xét 2.1.9(ii): một cặp cận dùng chung cho mọi x trong tập. -/
theorem bounded_iff_two_bounds (A : Set ℝ) :
    (BddAbove A ∧ BddBelow A) ↔ ∃ m M : ℝ, ∀ x ∈ A, m ≤ x ∧ x ≤ M := by
  constructor
  · rintro ⟨⟨M, hM⟩, ⟨m, hm⟩⟩
    exact ⟨m, M, fun _ hx ↦ ⟨hm hx, hM hx⟩⟩
  · rintro ⟨m, M, h⟩
    exact ⟨⟨M, fun x hx ↦ (h x hx).2⟩, ⟨m, fun x hx ↦ (h x hx).1⟩⟩

/-- Định nghĩa 2.1.10: phần tử lớn nhất và phần tử nhỏ nhất đều phải thuộc tập. -/
theorem extrema_definitions (A : Set ℝ) (m M : ℝ) :
    (IsGreatest A M ↔ M ∈ A ∧ ∀ x ∈ A, x ≤ M) ∧
    (IsLeast A m ↔ m ∈ A ∧ ∀ x ∈ A, m ≤ x) := ⟨Iff.rfl, Iff.rfl⟩

/-- Ví dụ 2.1.11: đoạn `[0,1]` có cả phần tử nhỏ nhất và lớn nhất. -/
theorem closedUnitInterval_extrema :
    IsLeast (Set.Icc (0 : ℝ) 1) 0 ∧ IsGreatest (Set.Icc (0 : ℝ) 1) 1 :=
  ⟨isLeast_Icc zero_le_one, isGreatest_Icc zero_le_one⟩

/-- Định nghĩa 2.1.12: α là cận trên của A và α≤M với mọi cận trên M. -/
theorem leastUpperBound_definition (A : Set ℝ) (α : ℝ) :
    IsLUB A α ↔ (∀ x ∈ A, x ≤ α) ∧ ∀ M, (∀ x ∈ A, x ≤ M) → α ≤ M := Iff.rfl

/-- Định nghĩa 2.1.14: β là cận dưới của A và m≤β với mọi cận dưới m. -/
theorem greatestLowerBound_definition (A : Set ℝ) (β : ℝ) :
    IsGLB A β ↔ (∀ x ∈ A, β ≤ x) ∧ ∀ m, (∀ x ∈ A, m ≤ x) → m ≤ β := Iff.rfl

/-- Mệnh đề 2.1.13: đặc trưng ε của cận trên bé nhất. -/
theorem leastUpperBound_iff_epsilon (A : Set ℝ) (α : ℝ)
    (_hne : A.Nonempty) (_hbdd : BddAbove A) :
    IsLUB A α ↔ (∀ x ∈ A, x ≤ α) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x ∈ A, α - ε < x := by
  constructor
  · intro h
    exact ⟨fun _ hx ↦ h.1 hx, fun ε hε ↦ (lt_isLUB_iff h).mp (by linarith)⟩
  · rintro ⟨hupper, happrox⟩
    refine ⟨hupper, ?_⟩
    intro M hM
    by_contra h
    have hε : 0 < α - M := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x, hx, hlarge⟩ := happrox (α - M) hε
    linarith [hM hx]

/-- Mệnh đề 2.1.15: đặc trưng ε của cận dưới lớn nhất. -/
theorem greatestLowerBound_iff_epsilon (A : Set ℝ) (β : ℝ)
    (_hne : A.Nonempty) (_hbdd : BddBelow A) :
    IsGLB A β ↔ (∀ x ∈ A, β ≤ x) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x ∈ A, x < β + ε := by
  constructor
  · intro h
    exact ⟨fun _ hx ↦ h.1 hx, fun ε hε ↦ (isGLB_lt_iff h).mp (by linarith)⟩
  · rintro ⟨hlower, happrox⟩
    refine ⟨hlower, ?_⟩
    intro m hm
    by_contra h
    have hε : 0 < m - β := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x, hx, hsmall⟩ := happrox (m - β) hε
    linarith [hm hx]

/-- Tiên đề đầy đủ: tập thực khác rỗng bị chặn trên có cận trên bé nhất. -/
theorem real_completeness {A : Set ℝ} (hne : A.Nonempty) (hbdd : BddAbove A) :
    ∃ α : ℝ, IsLUB A α := Real.exists_isLUB hne hbdd

/-- Định lí 2.1.16: tồn tại cận dưới lớn nhất cho tập khác rỗng bị chặn dưới. -/
theorem exists_greatestLowerBound {A : Set ℝ} (hne : A.Nonempty) (hbdd : BddBelow A) :
    ∃ β : ℝ, IsGLB A β := Real.exists_isGLB hne hbdd

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S01-remark-004: quy tắc lấy đối và bao hàm cho cận trên bé nhất, cận dưới lớn nhất. -/
theorem real_bounded_sup_inf_rules (A B : Set ℝ)
    (hA : A.Nonempty) (hAu : BddAbove A) (hAl : BddBelow A)
    (hBu : BddAbove B) (hBl : BddBelow B) (hAB : A ⊆ B) :
    sSup (-A) = -sInf A ∧ sInf (-A) = -sSup A ∧
      sSup A ≤ sSup B ∧ sInf B ≤ sInf A := by
  exact ⟨csSup_neg hA hAl, csInf_neg hA hAu,
    csSup_le_csSup hBu hA hAB, csInf_le_csInf hBl hA hAB⟩

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S01-remark-004, dòng 237–241: công thức gốc về đổi dấu và bao hàm cho sup, inf. -/
theorem source_sup_inf_rules (A B : Set ℝ)
    (hA : A.Nonempty) (hAB : A ⊆ B) :
    sSup (-A) = -sInf A ∧ sInf (-A) = -sSup A ∧
      sSup A ≤ sSup B ∧ sInf B ≤ sInf A ∧
      sInf (∅ : Set EReal) = ⊤ ∧ sSup (∅ : Set EReal) = ⊥ := by
  sorry

/-- Định lí 2.1.18: chọn số tự nhiên dương lớn hơn một số thực bất kỳ. -/
theorem exists_positive_nat_gt (x : ℝ) : ∃ n : ℕ, 0 < n ∧ x < (n : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  have hcast : (n : ℝ) < (n + 1 : ℕ) := by simp
  exact hn.trans hcast

/-- Mệnh đề 2.1.19(i): các số tự nhiên dương không bị chặn trên trong `ℝ`. -/
theorem positive_naturals_not_bddAbove :
    ¬ BddAbove {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = n} := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, hlarge⟩ := exists_positive_nat_gt M
  exact (not_le.mpr hlarge) (hM ⟨n, hn, rfl⟩)

/-- Mệnh đề 2.1.19(ii): nghịch đảo số tự nhiên dương nhỏ hơn ε đã cho. -/
theorem exists_positive_nat_reciprocal_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n + 1, Nat.succ_pos _, by simpa only [Nat.cast_add, Nat.cast_one] using hn⟩

/-- Mệnh đề 2.1.19(iii): bội tự nhiên của một số dương vượt mọi số thực. -/
theorem exists_positive_nat_mul_gt {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ n : ℕ, 0 < n ∧ b < (n : ℝ) * a := by
  obtain ⟨n, hn, hlarge⟩ := exists_positive_nat_gt (b / a)
  exact ⟨n, hn, (div_lt_iff₀ ha).mp hlarge⟩

/-- Ví dụ 2.1.22: cận trên bé nhất và cận dưới lớn nhất của khoảng mở, không có phần tử lớn nhất/nhỏ nhất. -/
theorem openUnitInterval_extrema :
    IsLUB (Set.Ioo (0 : ℝ) 1) 1 ∧ IsGLB (Set.Ioo (0 : ℝ) 1) 0 ∧
    (¬ ∃ x, IsGreatest (Set.Ioo (0 : ℝ) 1) x) ∧
    (¬ ∃ x, IsLeast (Set.Ioo (0 : ℝ) 1) x) := by
  refine ⟨isLUB_Ioo zero_lt_one, isGLB_Ioo zero_lt_one, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have heq := hx.isLUB.unique (isLUB_Ioo (show (0 : ℝ) < 1 from zero_lt_one))
    exact (ne_of_lt hx.1.2) heq
  · rintro ⟨x, hx⟩
    have heq := hx.isGLB.unique (isGLB_Ioo (show (0 : ℝ) < 1 from zero_lt_one))
    exact (ne_of_gt hx.1.1) heq

/-- Định lí 2.1.23: sắp thứ tự tốt cho tập số nguyên bị chặn dưới. -/
theorem integers_have_least {S : Set ℤ} (hne : S.Nonempty) (hbdd : BddBelow S) :
    ∃ m, IsLeast S m := Int.exists_least_of_bdd hbdd hne

/-- Khẳng định không đánh số, dòng 339: tập số nguyên khác rỗng bị chặn trên có phần tử lớn nhất. -/
theorem integers_have_greatest {S : Set ℤ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ M, IsGreatest S M := Int.exists_greatest_of_bdd hbdd hne

/-- Định lí 2.1.25: quy nạp từ 1. -/
theorem induction_from_one (P : ℕ → Prop) (hbase : P 1)
    (hstep : ∀ k : ℕ, 1 ≤ k → P k → P (k + 1)) : ∀ n : ℕ, 1 ≤ n → P n :=
  Nat.le_induction hbase hstep

/-- Định lí 2.1.24: tập con các số tự nhiên dương chứa 1 và đóng dưới phép kế tiếp. -/
theorem positive_naturals_induction_set (E : Set ℕ)
    (hpositive : E ⊆ {n | 1 ≤ n}) (hbase : 1 ∈ E)
    (hstep : ∀ n : ℕ, 1 ≤ n → n ∈ E → n + 1 ∈ E) : E = {n | 1 ≤ n} := by
  apply Set.Subset.antisymm hpositive
  exact induction_from_one (fun n ↦ n ∈ E) hbase hstep

/-- Định lí 2.1.26: quy nạp từ chỉ số ban đầu lớn hơn 1. -/
theorem induction_from_start (P : ℕ → Prop) (n₀ : ℕ) (_hn₀ : 1 < n₀)
    (hbase : P n₀) (hstep : ∀ k : ℕ, n₀ ≤ k → P k → P (k + 1)) :
    ∀ n : ℕ, n₀ ≤ n → P n := Nat.le_induction hbase hstep

/-- Định lí 2.1.27: quy nạp mạnh trên khoảng chỉ số từ `n₀` đến `k`. -/
theorem strong_induction_from_start (P : ℕ → Prop) (n₀ : ℕ) (_hn₀ : 0 < n₀)
    (hbase : P n₀)
    (hstep : ∀ k : ℕ, n₀ ≤ k → (∀ j : ℕ, n₀ ≤ j → j ≤ k → P j) → P (k + 1)) :
    ∀ n : ℕ, n₀ ≤ n → P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases heq : n = n₀
    · simpa only [heq] using hbase
    · have hlt : n₀ < n := lt_of_le_of_ne hn (Ne.symm heq)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
      apply hstep k (Nat.le_of_lt_succ hlt)
      intro j hj hjk
      exact ih j (Nat.lt_succ_of_le hjk) hj

/-- Định lí 2.1.29: tồn tại số hữu tỉ giữa hai số thực khác nhau. -/
theorem rational_between {a b : ℝ} (hab : a < b) :
    ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b := exists_rat_btwn hab

/-- Định lí 2.1.31, phần tồn tại: giữa hai số thực phân biệt có một số vô tỉ. -/
theorem irrational_between {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, Irrational x ∧ a < x ∧ x < b := exists_irrational_btwn hab

/-! ## Các bài tập so sánh và phần nguyên -/

/-- Bài tập 2.1.2(a): nếu |x|<ε với mọi ε>0 thì x=0. -/
theorem eq_zero_of_abs_lt_every_positive (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → |x| < ε) : x = 0 := by
  by_contra hx
  have hpos : 0 < |x| := abs_pos.mpr hx
  exact (lt_irrefl |x|) (h |x| hpos)

/-- Bài tập 2.1.2(b): đặc trưng thứ tự bằng mọi ε dương. -/
theorem le_iff_lt_add_every_positive (x y : ℝ) :
    x ≤ y ↔ ∀ ε : ℝ, 0 < ε → x < y + ε := by
  constructor
  · intro h ε hε
    linarith
  · intro h
    by_contra hxy
    have hε : 0 < x - y := sub_pos.mpr (lt_of_not_ge hxy)
    have := h (x - y) hε
    linarith

/-- Bài tập 2.1.3: nếu a<x với mọi x>b thì a≤b. -/
theorem le_of_lt_every_larger (a b : ℝ) (h : ∀ x : ℝ, b < x → a < x) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  exact (lt_irrefl a) (h a hba)

/-- Bài tập 2.1.4(a): một số thực là số nguyên khi và chỉ khi bằng phần nguyên của nó. -/
theorem integer_iff_floor_eq (x : ℝ) :
    x ∈ Set.range (Int.cast : ℤ → ℝ) ↔ (⌊x⌋ : ℝ) = x := by
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro h
    exact ⟨⌊x⌋, h⟩

/-- Bài tập 2.1.4(b): phần nguyên có kiểu số nguyên và hai bất đẳng thức đặc trưng. -/
theorem floor_bounds (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/-- Bài tập 2.1.4(c): cộng số nguyên trước hoặc sau khi lấy phần nguyên. -/
theorem floor_add_integer (x : ℝ) (n : ℤ) : ⌊x + (n : ℝ)⌋ = ⌊x⌋ + n :=
  Int.floor_add_intCast x n

/-- Bài tập 2.1.4(d): sai số cộng phần nguyên không vượt 1. -/
theorem floor_add_bounds (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
  refine ⟨Int.le_floor_add x y, ?_⟩
  have h := Int.le_floor_add_floor x y
  omega

end calculus.Chapter02.Section01
