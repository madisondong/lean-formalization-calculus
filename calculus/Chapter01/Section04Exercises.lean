import calculus.Chapter01.Section04
import Mathlib.Data.Set.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# 1.4. Số, lượng từ, tích Descartes và quan hệ

Nguồn: `source/Ch1_taphop.tex`, dòng 734–1513.
-/

namespace calculus.Chapter01.Section04Exercises

open Set Function

variable {X Y Z V : Type*}

/-- Bài tập số hữu tỉ/vô tỉ (a): cộng một số hữu tỉ giữ tính vô tỉ. -/
theorem rational_add_irrational (q : ℚ) (x : ℝ) (hx : Irrational x) :
    Irrational ((q : ℝ) + x) := hx.ratCast_add q

/-- Bài tập số hữu tỉ/vô tỉ (b): điều kiện q≠0 là bắt buộc. -/
theorem rational_mul_irrational (q : ℚ) (hq : q ≠ 0) (x : ℝ) (hx : Irrational x) :
    Irrational ((q : ℝ) * x) := hx.ratCast_mul hq

/-- Bài tập (c): hai số vô tỉ có thể có tổng hữu tỉ. -/
theorem irrational_sum_can_be_rational :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ x + y = (0 : ℚ) := by
  exact ⟨√2, -√2, irrational_sqrt_two, irrational_sqrt_two.neg, by simp⟩

/-- Bài tập (c): hai số vô tỉ có thể có tích hữu tỉ. -/
theorem irrational_product_can_be_rational :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ x * y = (2 : ℚ) := by
  refine ⟨√2, √2, irrational_sqrt_two, irrational_sqrt_two, ?_⟩
  exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- Mệnh đề 1.4.17: không có số hữu tỉ có bình phương bằng 2. -/
theorem rational_square_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro h
  have hr : (q : ℝ) ^ 2 = 2 := by exact_mod_cast h
  have ha : |(q : ℝ)| = √2 := by
    rw [← Real.sqrt_sq_eq_abs, hr]
  have hi : Irrational (|(q : ℝ)|) := ha.symm ▸ irrational_sqrt_two
  exact (Rat.not_irrational |q|) (by simpa only [Rat.cast_abs] using hi)

/-- Giữa hai số hữu tỉ phân biệt có một số hữu tỉ. -/
theorem rational_between (a b : ℚ) (hab : a < b) : ∃ q : ℚ, a < q ∧ q < b := by
  refine ⟨(a + b) / 2, ?_, ?_⟩ <;> linarith

/-- Có vô hạn số hữu tỉ trong mỗi khoảng mở có hai đầu mút hữu tỉ phân biệt. -/
theorem infinitely_many_rationals_between (a b : ℚ) (hab : a < b) :
    (Ioo a b).Infinite := Set.Ioo_infinite hab

/-- Định lí cơ bản số học: tồn tại phân tích thành nguyên tố; duy nhất đến hoán vị. -/
theorem prime_factorization_exists_unique (n : ℕ+) (hn : 1 < (n : ℕ)) :
    ∃ l : List ℕ, l.prod = n ∧ (∀ p ∈ l, Nat.Prime p) ∧
      ∀ l' : List ℕ, l'.prod = n → (∀ p ∈ l', Nat.Prime p) → l'.Perm l := by
  refine ⟨(n : ℕ).primeFactorsList, Nat.prod_primeFactorsList (by omega), ?_, ?_⟩
  · exact fun p hp ↦ Nat.prime_of_mem_primeFactorsList hp
  · exact fun l' hp hpr ↦ Nat.primeFactorsList_unique hp hpr

/-- Bài tập 2: mười phân số cụ thể (876+i)/1000 đều nằm giữa 7/8 và 8/9. -/
theorem ten_positive_rationals_between :
    Injective (fun i : Fin 10 ↦ (876 + (i.val : ℚ)) / 1000) ∧
      ∀ i : Fin 10, 0 < (876 + (i.val : ℚ)) / 1000 ∧
        7 / 8 < (876 + (i.val : ℚ)) / 1000 ∧
        (876 + (i.val : ℚ)) / 1000 < 8 / 9 := by
  constructor
  · intro i j h
    apply Fin.ext
    have he : (i.val : ℚ) = j.val := by linarith
    exact_mod_cast he
  · intro i
    have hi0 : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
    have hi9 : (i.val : ℚ) ≤ 9 := by exact_mod_cast (show i.val ≤ 9 by omega)
    constructor
    · linarith
    · constructor <;> linarith

/-- Bài tập 3(b): 1 và √2 độc lập tuyến tính trên ℚ. -/
theorem rational_linear_sqrt_two (m n : ℚ) (h : (m : ℝ) + n * √2 = 0) :
    m = 0 ∧ n = 0 := by
  have hn : n = 0 := by
    by_contra hn
    have hi := irrational_sqrt_two.ratCast_mul hn
    have he : (n : ℝ) * √2 = (-m : ℚ) := by push_cast; linarith
    exact (Rat.not_irrational (-m)) (he ▸ hi)
  constructor
  · have hm : (m : ℝ) = 0 := by simpa [hn] using h
    exact_mod_cast hm
  · exact hn

/-- Căn của số tự nhiên dương không chính phương là số vô tỉ. -/
theorem positive_nonsquare_sqrt_irrational (n : ℕ+) (hn : ¬ IsSquare (n : ℕ)) :
    Irrational (√(n : ℕ)) := irrational_sqrt_natCast_iff.mpr hn

/-- Lượng từ: bình phương thực không âm; nhưng số nguyên không luôn không âm. -/
theorem squares_nonnegative_and_integers_not_all_nonnegative :
    (∀ x : ℝ, 0 ≤ x ^ 2) ∧ ¬ (∀ n : ℤ, 0 ≤ n) := by
  refine ⟨sq_nonneg, ?_⟩
  intro h
  have hn := h (-1)
  norm_num at hn

/-- Các luật phủ định lượng từ. -/
theorem quantified_negations (P : X → Prop) :
    (¬ (∀ x, P x) ↔ ∃ x, ¬ P x) ∧ (¬ (∃ x, P x) ↔ ∀ x, ¬ P x) := by
  classical
  simp

/-- Ví dụ đổi thứ tự lượng từ: mỗi x có đối, nhưng không có đối chung. -/
theorem integer_quantifier_order :
    (∀ x : ℤ, ∃ y : ℤ, x + y = 0) ∧ ¬ (∃ y : ℤ, ∀ x : ℤ, x + y = 0) := by
  constructor
  · intro x; exact ⟨-x, by simp⟩
  · rintro ⟨y, hy⟩
    have h0 := hy 0
    have h1 := hy 1
    omega

/-- Nhân chứng dùng chung cho mọi x cũng là nhân chứng cho từng x. -/
theorem exists_forall_implies_forall_exists (P : X → Y → Prop) :
    (∃ y, ∀ x, P x y) → ∀ x, ∃ y, P x y := by
  rintro ⟨y, hy⟩ x
  exact ⟨y, hy x⟩

/-- Bài tập lượng từ (a): “mọi bình phương dương” sai tại 0; phủ định là ≤0. -/
theorem not_all_squares_positive :
    ¬ (∀ x : ℝ, 0 < x ^ 2) ∧
    (¬ (∀ x : ℝ, 0 < x ^ 2) ↔ ∃ x : ℝ, x ^ 2 ≤ 0) := by
  constructor
  · intro h; simpa using h 0
  · push Not; rfl

/-- Bài tập lượng từ (b): tồn tại bình phương dương, chọn 1. -/
theorem exists_positive_square :
    (∃ x : ℝ, 0 < x ^ 2) ∧
    (¬ (∃ x : ℝ, 0 < x ^ 2) ↔ ∀ x : ℝ, x ^ 2 ≤ 0) := by
  constructor
  · exact ⟨1, by norm_num⟩
  · push Not; rfl

/-- Bài tập lượng từ (c): x²<x tại x=1/2; phủ định đảo bất đẳng thức. -/
theorem exists_square_lt_self :
    (∃ x : ℝ, x ^ 2 < x) ∧
    (¬ (∃ x : ℝ, x ^ 2 < x) ↔ ∀ x : ℝ, x ≤ x ^ 2) := by
  constructor
  · exact ⟨1 / 2, by norm_num⟩
  · push Not; rfl

/-- Bài tập lượng từ (d): y=−x/2 phụ thuộc x. -/
theorem forall_exists_linear_zero :
    (∀ x : ℝ, ∃ y : ℝ, x + 2 * y = 0) ∧
    (¬ (∀ x : ℝ, ∃ y : ℝ, x + 2 * y = 0) ↔
      ∃ x : ℝ, ∀ y : ℝ, x + 2 * y ≠ 0) := by
  constructor
  · intro x; exact ⟨-x / 2, by ring⟩
  · push Not; rfl

/-- Bài tập lượng từ (e): không có y dùng chung cho mọi x. -/
theorem no_common_linear_zero :
    ¬ (∃ y : ℝ, ∀ x : ℝ, x + 2 * y = 0) ∧
    (¬ (∃ y : ℝ, ∀ x : ℝ, x + 2 * y = 0) ↔
      ∀ y : ℝ, ∃ x : ℝ, x + 2 * y ≠ 0) := by
  constructor
  · rintro ⟨y, hy⟩; linarith [hy 0, hy 1]
  · push Not; rfl

/-- Bài tập lượng từ (f): y=0 làm xy=0 với mọi x. -/
theorem forall_exists_product_zero :
    (∀ x : ℝ, ∃ y : ℝ, x * y = 0) ∧
    (¬ (∀ x : ℝ, ∃ y : ℝ, x * y = 0) ↔
      ∃ x : ℝ, ∀ y : ℝ, x * y ≠ 0) := by
  constructor
  · intro x; exact ⟨0, by simp⟩
  · push Not; rfl

/-- Bài tập lượng từ (g): x=0 không có nghịch đảo nhân. -/
theorem not_all_have_multiplicative_inverse :
    ¬ (∀ x : ℝ, ∃ y : ℝ, x * y = 1) ∧
    (¬ (∀ x : ℝ, ∃ y : ℝ, x * y = 1) ↔
      ∃ x : ℝ, ∀ y : ℝ, x * y ≠ 1) := by
  constructor
  · intro h; simpa using h 0
  · push Not; rfl

/-- Bài tập lượng từ (h): cũng không có nghịch đảo chung. -/
theorem no_common_multiplicative_inverse :
    ¬ (∃ y : ℝ, ∀ x : ℝ, x * y = 1) ∧
    (¬ (∃ y : ℝ, ∀ x : ℝ, x * y = 1) ↔
      ∀ y : ℝ, ∃ x : ℝ, x * y ≠ 1) := by
  constructor
  · rintro ⟨y, hy⟩; simpa using hy 0
  · push Not; rfl

/-- Bài tập lượng từ (i): chọn y=1. -/
theorem forall_exists_product_self :
    (∀ x : ℝ, ∃ y : ℝ, x * y = x) ∧
    (¬ (∀ x : ℝ, ∃ y : ℝ, x * y = x) ↔
      ∃ x : ℝ, ∀ y : ℝ, x * y ≠ x) := by
  constructor
  · intro x; exact ⟨1, by simp⟩
  · push Not; rfl

/-- Bài ba lượng từ (a): x=0, z=y. -/
theorem exists_forall_exists_add :
    (∃ x : ℝ, ∀ y : ℝ, ∃ z : ℝ, x + y = z) ∧
    (¬ (∃ x : ℝ, ∀ y : ℝ, ∃ z : ℝ, x + y = z) ↔
      ∀ x : ℝ, ∃ y : ℝ, ∀ z : ℝ, x + y ≠ z) := by
  constructor
  · exact ⟨0, fun y ↦ ⟨y, by simp⟩⟩
  · push Not; rfl

/-- Bài ba lượng từ (b): một tổng cố định không thể bằng mọi z. -/
theorem no_fixed_sum_equal_everything :
    ¬ (∃ x y : ℝ, ∀ z : ℝ, x + y = z) ∧
    (¬ (∃ x y : ℝ, ∀ z : ℝ, x + y = z) ↔
      ∀ x y : ℝ, ∃ z : ℝ, x + y ≠ z) := by
  constructor
  · rintro ⟨x, y, hz⟩; linarith [hz 0, hz 1]
  · push Not; rfl

/-- Bài ba lượng từ (c): z=y−x. -/
theorem forall_forall_exists_sub :
    (∀ x y : ℝ, ∃ z : ℝ, y - z = x) ∧
    (¬ (∀ x y : ℝ, ∃ z : ℝ, y - z = x) ↔
      ∃ x y : ℝ, ∀ z : ℝ, y - z ≠ x) := by
  constructor
  · intro x y; exact ⟨y - x, by ring⟩
  · push Not; rfl

/-- Bài ba lượng từ (d): x=0,y=1 là phản ví dụ. -/
theorem not_all_division_equations_solvable :
    ¬ (∀ x y : ℝ, ∃ z : ℝ, x * z = y) ∧
    (¬ (∀ x y : ℝ, ∃ z : ℝ, x * z = y) ↔
      ∃ x y : ℝ, ∀ z : ℝ, x * z ≠ y) := by
  constructor
  · intro h; simpa using h 0 1
  · push Not; rfl

/-- Bài ba lượng từ (e): tồn tại x=0 và phép kéo theo đúng. -/
theorem exists_universal_order_shift :
    (∃ x : ℝ, ∀ y z : ℝ, y < z → x + y < z) ∧
    (¬ (∃ x : ℝ, ∀ y z : ℝ, y < z → x + y < z) ↔
      ∀ x : ℝ, ∃ y z : ℝ, y < z ∧ z ≤ x + y) := by
  constructor
  · exact ⟨0, fun y z h ↦ by simpa using h⟩
  · push Not; rfl

/-- Bài ba lượng từ (f): y=z=0 làm tiền đề sai nên kéo theo đúng. -/
theorem forall_exists_order_implication :
    (∀ x : ℝ, ∃ y z : ℝ, y < z → x + y < z) ∧
    (¬ (∀ x : ℝ, ∃ y z : ℝ, y < z → x + y < z) ↔
      ∃ x : ℝ, ∀ y z : ℝ, y < z ∧ z ≤ x + y) := by
  constructor
  · intro x; exact ⟨0, 0, fun h ↦ (lt_irrefl 0 h).elim⟩
  · push Not; rfl

/-- Bài viết định nghĩa (a): không đơn ánh khi có hai điểm phân biệt cùng ảnh. -/
theorem not_injective_iff (f : X → Y) :
    ¬ Injective f ↔ ∃ x y, f x = f y ∧ x ≠ y := by
  classical
  unfold Injective
  push Not
  rfl

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- Phép lấy đối trên miền đối xứng. -/
def domainNeg (D : Set ℝ) (hD : ∀ x ∈ D, -x ∈ D) (x : D) : D :=
  ⟨-x, hD x x.property⟩

/-- C01-S04-exercise-016.p02: phủ định tính chẵn trên miền đối xứng. -/
theorem symmetric_domain_even_negation (D : Set ℝ)
    (hD : ∀ x ∈ D, -x ∈ D) (f : D → ℝ) :
    ¬ (∀ x : D, f (domainNeg D hD x) = f x) ↔
      ∃ x : D, f (domainNeg D hD x) ≠ f x := by
  classical
  push Not
  rfl

end calculus.SourceCorrectionsChapter12

namespace calculus.Chapter01.Section04Exercises

open Set Function

variable {X Y Z V : Type*}

/-- Bài viết định nghĩa (b): hàm chẵn trên miền D. -/
theorem source_even_criterion_and_negation (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∀ x ∈ D, f (-x) = f x) ↔ ∃ x ∈ D, f (-x) ≠ f x := by
  classical
  push Not
  rfl

end calculus.Chapter01.Section04Exercises

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C01-S04-exercise-016.p02, dòng 1090: phủ định điều kiện chẵn của hàm trên ℝ. -/
theorem source_even_criterion_and_negation (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∀ x ∈ D, f (-x) = f x) ↔ ∃ x ∈ D, f (-x) ≠ f x := by
  sorry

/-- Bài viết định nghĩa (c): tăng không ngặt là `MonotoneOn`. -/
theorem monotoneOn_criterion_and_negation (D : Set ℝ) (f : ℝ → ℝ) :
    (MonotoneOn f D ↔ ∀ x ∈ D, ∀ y ∈ D, x ≤ y → f x ≤ f y) ∧
    (¬ MonotoneOn f D ↔ ∃ x ∈ D, ∃ y ∈ D, x ≤ y ∧ f y < f x) := by
  classical
  constructor
  · rfl
  · unfold MonotoneOn
    push Not
    rfl

/-- Bài viết định nghĩa (d): tăng ngặt là `StrictMonoOn`. -/
theorem strictMonoOn_criterion_and_negation (D : Set ℝ) (f : ℝ → ℝ) :
    (StrictMonoOn f D ↔ ∀ x ∈ D, ∀ y ∈ D, x < y → f x < f y) ∧
    (¬ StrictMonoOn f D ↔ ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f y ≤ f x) := by
  classical
  constructor
  · rfl
  · unfold StrictMonoOn
    push Not
    rfl

/-- Bài viết định nghĩa (e): không bị chặn; với mỗi M chọn một x. -/
theorem not_abs_bounded_on_iff (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∃ M : ℝ, ∀ x ∈ D, |f x| ≤ M) ↔
      ∀ M : ℝ, ∃ x ∈ D, M < |f x| := by
  classical
  push Not
  rfl

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C01-S04-exercise-016.p06: phủ định điều kiện Lipschitz với hệ số không âm. -/
theorem standard_lipschitz_negation (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ D, ∀ y ∈ D,
      |f x - f y| ≤ L * |x - y|) ↔
      ∀ L : ℝ, 0 ≤ L → ∃ x ∈ D, ∃ y ∈ D,
        L * |x - y| < |f x - f y| := by
  classical
  push Not
  rfl

end calculus.SourceCorrectionsChapter12

namespace calculus.Chapter01.Section04Exercises

open Set Function

variable {X Y Z V : Type*}

/-- Bài viết định nghĩa (f): công thức in thiếu |x−y|, nên chỉ mô tả dao động bị chặn, không phải điều kiện Lipschitz. -/
theorem not_source_bounded_oscillation_iff (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∃ L : ℝ, ∀ x ∈ D, ∀ y ∈ D, |f x - f y| ≤ L) ↔
      ∀ L : ℝ, ∃ x ∈ D, ∃ y ∈ D, L < |f x - f y| := by
  classical
  push Not
  rfl

end calculus.Chapter01.Section04Exercises

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C01-S04-exercise-016.p06, dòng 1094: phủ định công thức đã in cho điều kiện Lipschitz. -/
theorem not_source_bounded_oscillation_iff (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ (∃ L : ℝ, ∀ x ∈ D, ∀ y ∈ D, |f x - f y| ≤ L) ↔
      ∀ L : ℝ, ∃ x ∈ D, ∃ y ∈ D, L < |f x - f y| := by
  sorry

/-- Bài viết định nghĩa (g): liên tục trên miền D. -/
theorem continuousWithinAt_real_criterion (D : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) (_hx₀ : x₀ ∈ D) :
    ContinuousWithinAt f D x₀ ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - x₀| < δ → |f x - f x₀| < ε := by
  simpa only [Real.dist_eq] using (Metric.continuousWithinAt_iff (f := f) (s := D) (a := x₀))

/-- Phủ định liên tục trong miền, ε cố định trước mọi δ. -/
theorem not_continuousWithinAt_real_iff (D : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ D) :
    ¬ ContinuousWithinAt f D x₀ ↔
      ∃ ε > 0, ∀ δ > 0, ∃ x ∈ D, |x - x₀| < δ ∧ ε ≤ |f x - f x₀| := by
  classical
  rw [continuousWithinAt_real_criterion D f x₀ hx₀]
  push Not
  rfl

/-- Bài viết định nghĩa (h): cùng δ cho mọi cặp điểm trong D. -/
theorem uniformContinuousOn_real_criterion (D : Set ℝ) (f : ℝ → ℝ) :
    UniformContinuousOn f D ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, ∀ y ∈ D, |x - y| < δ → |f x - f y| < ε := by
  simpa only [Real.dist_eq] using (Metric.uniformContinuousOn_iff (f := f) (s := D))

/-- Phủ định liên tục đều: cặp điểm được chọn sau δ. -/
theorem not_uniformContinuousOn_real_iff (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ UniformContinuousOn f D ↔
      ∃ ε > 0, ∀ δ > 0, ∃ x ∈ D, ∃ y ∈ D,
        |x - y| < δ ∧ ε ≤ |f x - f y| := by
  classical
  rw [uniformContinuousOn_real_criterion]
  push Not
  rfl

/-- Bài viết định nghĩa (i): phủ định giới hạn với 0<|x−x₀|. -/
theorem not_punctured_limit_formula_iff (D : Set ℝ) (f : ℝ → ℝ) (x₀ L : ℝ) :
    ¬ (∀ ε > 0, ∃ δ > 0, ∀ x ∈ D,
      0 < |x - x₀| ∧ |x - x₀| < δ → |f x - L| < ε) ↔
      ∃ ε > 0, ∀ δ > 0, ∃ x ∈ D,
        (0 < |x - x₀| ∧ |x - x₀| < δ) ∧ ε ≤ |f x - L| := by
  classical
  push Not
  rfl

/-- Cặp Kuratowski: {{a},{a,b}}. -/
def kuratowskiPair (a b : X) : Set (Set X) := {{a}, {a, b}}

/-- Định lí 1.4.18: hai cặp Kuratowski bằng nhau khi các thành phần tương ứng bằng nhau. -/
theorem kuratowskiPair_eq_iff (a b x y : X) :
    kuratowskiPair a b = kuratowskiPair x y ↔ a = x ∧ b = y := by
  classical
  constructor
  · intro h
    rcases Set.pair_eq_pair_iff.mp h with ⟨hax, hab⟩ | ⟨hay, hbx⟩
    · have hax' : a = x := Set.singleton_eq_singleton_iff.mp hax
      subst x
      refine ⟨rfl, ?_⟩
      rcases Set.pair_eq_pair_iff.mp hab with ⟨_, hby⟩ | ⟨hay, hba⟩
      · exact hby
      · exact hba.trans hay
    · have hba : b = a := by
        have hb : b ∈ ({x} : Set X) := hbx ▸ (by simp : b ∈ ({a, b} : Set X))
        have ha : a ∈ ({x} : Set X) := hbx ▸ (by simp : a ∈ ({a, b} : Set X))
        exact (Set.mem_singleton_iff.mp hb).trans (Set.mem_singleton_iff.mp ha).symm
      subst b
      have hax : a = x := by simpa using hbx
      subst x
      have hya : y = a := by
        have hy : y ∈ ({a} : Set X) := hay.symm ▸ (by simp : y ∈ ({a, y} : Set X))
        exact Set.mem_singleton_iff.mp hy
      exact ⟨rfl, hya.symm⟩
  · rintro ⟨rfl, rfl⟩; rfl


theorem kuratowskiPair_eq_iff_prod_eq (a b x y : X) :
    kuratowskiPair a b = kuratowskiPair x y ↔ (a, b) = (x, y) := by
  rw [kuratowskiPair_eq_iff, Prod.mk.injEq]

/-- Định nghĩa 1.4.19: thuộc tích Descartes gồm hai điều kiện thuộc. -/
theorem cartesian_membership (A : Set X) (B : Set Y) (p : X × Y) :
    p ∈ A ×ˢ B ↔ p.1 ∈ A ∧ p.2 ∈ B := Iff.rfl

/-- Dạng có lượng từ của định nghĩa tích Descartes. -/
theorem cartesian_membership_exists (A : Set X) (B : Set Y) (p : X × Y) :
    p ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, p = (a, b) := by
  constructor
  · intro h; exact ⟨p.1, h.1, p.2, h.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨ha, hb⟩

/-- Ví dụ tích (c): tích hai đoạn đóng là hình chữ nhật. -/
theorem rectangle_membership (p : ℝ × ℝ) :
    p ∈ Icc (-1) 2 ×ˢ Icc 0 3 ↔
      (-1 ≤ p.1 ∧ p.1 ≤ 2) ∧ (0 ≤ p.2 ∧ p.2 ≤ 3) := Iff.rfl

/-- Mệnh đề tích (i): tích phân phối qua giao. -/
theorem cartesian_inter (A : Set X) (B C : Set Y) :
    A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := Set.prod_inter

/-- Mệnh đề tích (ii): tích phân phối qua hợp. -/
theorem cartesian_union (A : Set X) (B C : Set Y) :
    A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := Set.prod_union

/-- Mệnh đề tích (iii): giao hai tích bằng tích hai giao. -/
theorem cartesian_inter_cartesian (A C : Set X) (B D : Set Y) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := Set.prod_inter_prod

/-- Mệnh đề tích (iv): tích của hai hợp chứa hợp của hai tích. -/
theorem cartesian_union_subset (A C : Set X) (B D : Set Y) :
    (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D) := by
  rintro p (hp | hp)
  · exact ⟨Or.inl hp.1, Or.inl hp.2⟩
  · exact ⟨Or.inr hp.1, Or.inr hp.2⟩

/-- Đồ thị của quan hệ là tập các cặp liên hệ. -/
def relationGraph (R : X → Y → Prop) : Set (X × Y) := {p | R p.1 p.2}


theorem relationGraph_subset (R : X → Y → Prop) :
    relationGraph R ⊆ (univ : Set X) ×ˢ (univ : Set Y) := by
  intro p hp; exact ⟨mem_univ _, mem_univ _⟩


theorem relationGraph_membership (R : X → Y → Prop) (x : X) (y : Y) :
    (x, y) ∈ relationGraph R ↔ R x y := Iff.rfl

/-- Miền xác định của quan hệ gồm các phần tử có liên hệ với ít nhất một phần tử đích. -/
def relationDomain (R : X → Y → Prop) : Set X := {x | ∃ y, R x y}

/-- Tập giá trị Ran(R) gồm các phần tử có ít nhất một tiền ảnh. -/
def relationRange (R : X → Y → Prop) : Set Y := {y | ∃ x, R x y}

/-- Quan hệ ngược đổi chỗ hai thành phần của mỗi cặp. -/
theorem inverse_membership (R : X → Y → Prop) (y : Y) (x : X) :
    swap R y x ↔ R x y := Iff.rfl

/-- Hợp thành S∘R tương ứng với `Relation.Comp R S`. -/
theorem relation_composition_membership (R : X → Y → Prop) (S : Y → Z → Prop)
    (x : X) (z : Z) : Relation.Comp R S x z ↔ ∃ y, R x y ∧ S y z := Iff.rfl

/-- Định lí quan hệ (i): đảo hai lần về quan hệ gốc. -/
theorem relation_inverse_inverse (R : X → Y → Prop) : swap (swap R) = R := rfl

/-- Định lí quan hệ (ii): miền xác định của quan hệ ngược là tập giá trị của quan hệ ban đầu. -/
theorem relation_inverse_domain (R : X → Y → Prop) :
    relationDomain (swap R) = relationRange R := rfl

/-- Định lí quan hệ (iii): tập giá trị của quan hệ ngược là miền xác định của quan hệ ban đầu. -/
theorem relation_inverse_range (R : X → Y → Prop) :
    relationRange (swap R) = relationDomain R := rfl

/-- Định lí quan hệ (iv): tính kết hợp của hợp thành quan hệ. -/
theorem relation_composition_assoc (R : X → Y → Prop) (S : Y → Z → Prop)
    (T : Z → V → Prop) :
    Relation.Comp (Relation.Comp R S) T = Relation.Comp R (Relation.Comp S T) :=
  Relation.comp_assoc

/-- Định lí quan hệ (v): đảo hợp thành đảo thứ tự hai quan hệ. -/
theorem relation_inverse_composition (R : X → Y → Prop) (S : Y → Z → Prop) :
    swap (Relation.Comp R S) = Relation.Comp (swap S) (swap R) := by
  funext z x
  apply propext
  exact exists_congr fun y ↦ and_comm

/-- Định nghĩa lớp tương đương: phần tử y liên hệ với đại diện x. -/
def equivalenceClass (R : X → X → Prop) (x : X) : Set X := {y | R y x}

/-- Mệnh đề các lớp (i): mỗi phần tử thuộc lớp của nó. -/
theorem mem_own_equivalenceClass (R : X → X → Prop) (hR : Equivalence R) (x : X) :
    x ∈ equivalenceClass R x := hR.refl x

/-- Mệnh đề các lớp (ii): liên hệ khi và chỉ khi hai lớp bằng nhau. -/
theorem related_iff_equivalenceClass_eq (R : X → X → Prop) (hR : Equivalence R) (x y : X) :
    R x y ↔ equivalenceClass R x = equivalenceClass R y := by
  constructor
  · intro hxy; ext z
    exact ⟨fun hzx ↦ hR.trans hzx hxy, fun hzy ↦ hR.trans hzy (hR.symm hxy)⟩
  · intro heq
    have hx := mem_own_equivalenceClass R hR x
    rw [heq] at hx
    exact hx

/-- Mệnh đề các lớp (iii): bằng nhau hoặc giao rỗng. -/
theorem equivalenceClasses_eq_or_disjoint (R : X → X → Prop) (hR : Equivalence R) (x y : X) :
    equivalenceClass R x = equivalenceClass R y ∨
      equivalenceClass R x ∩ equivalenceClass R y = ∅ := by
  classical
  by_cases hxy : R x y
  · exact Or.inl ((related_iff_equivalenceClass_eq R hR x y).mp hxy)
  · right; apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hzx, hzy⟩
    exact hxy (hR.trans (hR.symm hzx) hzy)

/-- Phân hoạch của X≠∅: các phần khác rỗng, phủ X và đôi một rời nhau. -/
def IsNonemptyPartition (C : Set (Set X)) : Prop :=
  Nonempty X ∧ (∀ A ∈ C, A.Nonempty) ∧ (∀ x : X, ∃ A ∈ C, x ∈ A) ∧
    ∀ A ∈ C, ∀ B ∈ C, A = B ∨ A ∩ B = ∅

/-- Các lớp của quan hệ tương đương phân hoạch nguồn khác rỗng. -/
theorem equivalenceClasses_partition [Nonempty X] (R : X → X → Prop) (hR : Equivalence R) :
    IsNonemptyPartition (range (equivalenceClass R)) := by
  refine ⟨inferInstance, ?_⟩
  constructor
  · rintro A ⟨x, rfl⟩; exact ⟨x, mem_own_equivalenceClass R hR x⟩
  · constructor
    · intro x; exact ⟨equivalenceClass R x, ⟨x, rfl⟩, mem_own_equivalenceClass R hR x⟩
    · rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩
      exact equivalenceClasses_eq_or_disjoint R hR x y

/-- Bài tập quan hệ (a): ≤ trên ℝ không đối xứng, nên không tương đương. -/
theorem real_le_not_equivalence : ¬ Equivalence (fun x y : ℝ ↦ x ≤ y) := by
  intro h
  have := h.symm (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at this


theorem function_kernel_equivalence (f : X → Y) : Equivalence (fun x y ↦ f x = f y) :=
  ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Bài tập quan hệ (b): hai số có cùng trị tuyệt đối. -/
theorem real_abs_equivalence : Equivalence (fun x y : ℝ ↦ |x| = |y|) :=
  function_kernel_equivalence abs

/-- Bài tập quan hệ (c): 1 là ước của 2, nhưng 2 không là ước của 1. -/
theorem integer_dvd_not_equivalence : ¬ Equivalence (fun x y : ℤ ↦ x ∣ y) := by
  intro h
  have := h.symm (show (1 : ℤ) ∣ 2 by norm_num)
  norm_num at this

/-- Bài tập quan hệ (d): hai số có cùng bình phương. -/
theorem real_square_equivalence : Equivalence (fun x y : ℝ ↦ x ^ 2 = y ^ 2) :=
  function_kernel_equivalence (fun x ↦ x ^ 2)

/-- Bài tập quan hệ 2: tổng chẵn chính là cùng phần dư theo môđun 2. -/
theorem even_sum_iff_same_residue (x y : ℤ) :
    (2 : ℤ) ∣ x + y ↔ x % 2 = y % 2 := by omega

/-- Bài tập quan hệ 2(a): năm số phân biệt liên hệ với 2. -/
theorem five_integers_related_to_two :
    ({0, 2, 4, 6, 8} : Set ℤ).ncard = 5 ∧
      ∀ x ∈ ({0, 2, 4, 6, 8} : Set ℤ), (2 : ℤ) ∣ x + 2 := by
  constructor
  · simp [Set.ncard_insert_of_notMem]
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Bài tập quan hệ 2(b): lớp [1] chính xác gồm các số có dư 1 theo môđun 2. -/
theorem even_sum_class_one :
    equivalenceClass (fun x y : ℤ ↦ (2 : ℤ) ∣ x + y) 1 = {x : ℤ | x % 2 = 1} := by
  ext x
  simp only [equivalenceClass, mem_ofPred_eq, even_sum_iff_same_residue]
  norm_num

/-- Bài tập quan hệ 2(c): tương đương, không cần hạn chế dấu của số nguyên. -/
theorem even_sum_equivalence : Equivalence (fun x y : ℤ ↦ (2 : ℤ) ∣ x + y) := by
  simpa only [even_sum_iff_same_residue] using
    function_kernel_equivalence (fun x : ℤ ↦ x % 2)


theorem equivalenceClass_family_eq_pair (R : X → X → Prop) (hR : Equivalence R)
    (a b : X) (hcover : ∀ x, R x a ∨ R x b) :
    range (equivalenceClass R) = {equivalenceClass R a, equivalenceClass R b} := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    rcases hcover x with hx | hx
    · exact mem_insert_iff.mpr (Or.inl ((related_iff_equivalenceClass_eq R hR x a).mp hx))
    · exact mem_insert_iff.mpr (Or.inr ((related_iff_equivalenceClass_eq R hR x b).mp hx))
  · intro h
    rcases mem_insert_iff.mp h with h | h
    · exact ⟨a, h.symm⟩
    · exact ⟨b, (mem_singleton_iff.mp h).symm⟩

/-- Bài tập quan hệ 2(d): tập thương gồm lớp các số chẵn và lớp các số lẻ. -/
theorem even_sum_quotient_classes :
    range (equivalenceClass (fun x y : ℤ ↦ (2 : ℤ) ∣ x + y)) =
      {equivalenceClass (fun x y : ℤ ↦ (2 : ℤ) ∣ x + y) 0,
       equivalenceClass (fun x y : ℤ ↦ (2 : ℤ) ∣ x + y) 1} := by
  apply equivalenceClass_family_eq_pair _ even_sum_equivalence
  intro x
  simp only [even_sum_iff_same_residue]
  omega

/-- Bài tập quan hệ 3: hiệu hai số hữu tỉ là số nguyên. -/
def rationalIntegerDifference (a b : ℚ) : Prop := ∃ m : ℤ, a - b = m

/-- Bài tập quan hệ 3(a): hiệu hai số hữu tỉ là số nguyên xác định một quan hệ tương đương. -/
theorem rationalIntegerDifference_equivalence : Equivalence rationalIntegerDifference := by
  constructor
  · intro a; exact ⟨0, by simp⟩
  · rintro a b ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast
    linarith
  · rintro a b c ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    push_cast
    linarith


theorem rationalIntegerDifference_class (a : ℚ) :
    equivalenceClass rationalIntegerDifference a = range (fun m : ℤ ↦ (m : ℚ) + a) := by
  ext x
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by linarith⟩
  · rintro ⟨m, rfl⟩; exact ⟨m, by ring⟩

/-- Bài tập quan hệ 3(b): công thức lớp [5/7]. -/
theorem rationalIntegerDifference_class_five_sevenths :
    equivalenceClass rationalIntegerDifference (5 / 7) =
      range (fun m : ℤ ↦ (m : ℚ) + 5 / 7) := rationalIntegerDifference_class _

/-- Bài tập quan hệ 3(c): lớp của một số nguyên là toàn bộ các số nguyên. -/
theorem rationalIntegerDifference_integer_class (a : ℤ) :
    equivalenceClass rationalIntegerDifference (a : ℚ) = range ((↑) : ℤ → ℚ) := by
  ext x
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + a, ?_⟩
    push_cast
    linarith
  · rintro ⟨m, rfl⟩
    refine ⟨m - a, ?_⟩
    push_cast
    rfl

/-- Bài tập quan hệ 4: hiệu hai số thực là số hữu tỉ. -/
def realRationalDifference (x y : ℝ) : Prop := ∃ q : ℚ, x - y = q

/-- Bài tập quan hệ 4(a): quan hệ tương đương theo môđun các số hữu tỉ. -/
theorem realRationalDifference_equivalence : Equivalence realRationalDifference := by
  constructor
  · intro x; exact ⟨0, by simp⟩
  · rintro x y ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    push_cast
    linarith
  · rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
    refine ⟨q + r, ?_⟩
    push_cast
    linarith

/-- Bài tập quan hệ 4(b): dịch √2 bởi 0,1,2,3,4 cho năm phần tử khác nhau. -/
theorem five_realRationalDifference_representatives :
    Injective (fun i : Fin 5 ↦ (i : ℝ) + √2) ∧
      ∀ i : Fin 5, realRationalDifference ((i : ℝ) + √2) (√2) := by
  constructor
  · intro i j h
    apply Fin.ext
    have hcast : (i.val : ℝ) = j.val := by linarith
    exact_mod_cast hcast
  · intro i
    exact ⟨i.val, by simp⟩


theorem realRationalDifference_class (a : ℝ) :
    equivalenceClass realRationalDifference a = range (fun q : ℚ ↦ (q : ℝ) + a) := by
  ext x
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by linarith⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by ring⟩

/-- Bài tập quan hệ 4(c): lớp của một số hữu tỉ là toàn bộ các số hữu tỉ. -/
theorem realRationalDifference_rational_class (a : ℚ) :
    equivalenceClass realRationalDifference (a : ℝ) = range ((↑) : ℚ → ℝ) := by
  ext x
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q + a, ?_⟩
    push_cast
    linarith
  · rintro ⟨q, rfl⟩
    refine ⟨q - a, ?_⟩
    push_cast
    rfl

/-- Bài tập quan hệ 4(d): lớp của √2 là {√2+q : q∈ℚ}. -/
theorem realRationalDifference_sqrt_two_class :
    equivalenceClass realRationalDifference (√2) = range (fun q : ℚ ↦ (q : ℝ) + √2) :=
  realRationalDifference_class _

/-- Bài tập trên ℝ²(a): cùng giá trị b−a² là quan hệ tương đương. -/
theorem parabola_equivalence :
    Equivalence (fun p q : ℝ × ℝ ↦ p.2 - p.1 ^ 2 = q.2 - q.1 ^ 2) :=
  function_kernel_equivalence (fun p : ℝ × ℝ ↦ p.2 - p.1 ^ 2)

/-- Bài tập trên ℝ²(b): lớp (0,0) và (1,2) là hai parabol cụ thể. -/
theorem parabola_classes :
    equivalenceClass (fun p q : ℝ × ℝ ↦ p.2 - p.1 ^ 2 = q.2 - q.1 ^ 2) (0, 0) =
      {p | p.2 = p.1 ^ 2} ∧
    equivalenceClass (fun p q : ℝ × ℝ ↦ p.2 - p.1 ^ 2 = q.2 - q.1 ^ 2) (1, 2) =
      {p | p.2 = p.1 ^ 2 + 1} := by
  constructor <;> ext p <;> simp only [equivalenceClass, mem_ofPred_eq]
  all_goals norm_num
  all_goals constructor <;> intro h <;> linarith

/-- Quan hệ bằng nhau là quan hệ tương đương. -/
theorem identity_relation_equivalence [Nonempty X] : Equivalence (fun x y : X ↦ x = y) :=
  function_kernel_equivalence id

/-- Đồng dư theo môđun m: hiệu hai số là bội nguyên của m. -/
def integerCongruence (m x y : ℤ) : Prop := ∃ k : ℤ, x - y = k * m


theorem integerCongruence_iff_modEq (m x y : ℤ) :
    integerCongruence m x y ↔ Int.ModEq m x y := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨-k, by nlinarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by nlinarith⟩

/-- Ví dụ đồng dư: quan hệ tương đương với m>1. -/
theorem integerCongruence_equivalence (m : ℤ) (_hm : 1 < m) :
    Equivalence (integerCongruence m) := by
  constructor
  · intro x; exact ⟨0, by ring⟩
  · rintro x y ⟨k, hk⟩; exact ⟨-k, by nlinarith⟩
  · rintro x y z ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    calc
      x - z = (x - y) + (y - z) := by ring
      _ = k * m + l * m := by rw [hk, hl]
      _ = (k + l) * m := by ring

/-- Ví dụ |x−y|≤1: phản xạ và đối xứng, nhưng không bắc cầu. -/
theorem nearby_integers_relation_properties :
    (∀ x : ℤ, |x - x| ≤ 1) ∧
    (∀ x y : ℤ, |x - y| ≤ 1 → |y - x| ≤ 1) ∧
    ¬ (∀ x y z : ℤ, |x - y| ≤ 1 → |y - z| ≤ 1 → |x - z| ≤ 1) := by
  constructor
  · intro x; simp
  · constructor
    · intro x y h; simpa only [abs_sub_comm] using h
    · intro h
      have hn := h 0 1 2 (by norm_num) (by norm_num)
      norm_num at hn

/-- Các lớp đồng dư gồm đúng các số mk+a. -/
theorem integerCongruence_class (m a : ℤ) :
    equivalenceClass (integerCongruence m) a = range (fun k : ℤ ↦ m * k + a) := by
  ext x
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by nlinarith⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩

/-- Tập thương theo môđun m>1 có đại diện 0≤r<m. -/
theorem integerCongruence_quotient_classes (m : ℤ) (hm : 1 < m) :
    range (equivalenceClass (integerCongruence m)) =
      {A | ∃ r : ℤ, 0 ≤ r ∧ r < m ∧ A = equivalenceClass (integerCongruence m) r} := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x % m, Int.emod_nonneg x (by omega), Int.emod_lt_of_pos x (by omega), ?_⟩
    apply (related_iff_equivalenceClass_eq _ (integerCongruence_equivalence m hm) x (x % m)).mp
    apply (integerCongruence_iff_modEq m x (x % m)).mpr
    show x % m = (x % m) % m
    simp
  · rintro ⟨r, hr0, hrm, rfl⟩
    exact ⟨r, rfl⟩

/-- Ví dụ theo môđun 5: năm lớp 0,1,2,3,4 cho toàn bộ họ lớp. -/
theorem integerCongruence_five_classes :
    range (equivalenceClass (integerCongruence 5)) =
      {equivalenceClass (integerCongruence 5) 0, equivalenceClass (integerCongruence 5) 1,
       equivalenceClass (integerCongruence 5) 2, equivalenceClass (integerCongruence 5) 3,
       equivalenceClass (integerCongruence 5) 4} := by
  rw [integerCongruence_quotient_classes 5 (by norm_num)]
  ext A
  constructor
  · rintro ⟨r, hr0, hr5, rfl⟩
    interval_cases r <;> simp
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by norm_num, by norm_num, h⟩
    · exact ⟨1, by norm_num, by norm_num, h⟩
    · exact ⟨2, by norm_num, by norm_num, h⟩
    · exact ⟨3, by norm_num, by norm_num, h⟩
    · exact ⟨4, by norm_num, by norm_num, h⟩

/-- Ví dụ theo môđun 5: dịch bởi bội m không đổi lớp. -/
theorem integerCongruence_class_periodic (m a k : ℤ) (hm : 1 < m) :
    equivalenceClass (integerCongruence m) a = equivalenceClass (integerCongruence m) (a + m * k) := by
  apply (related_iff_equivalenceClass_eq _ (integerCongruence_equivalence m hm) a (a + m * k)).mp
  exact ⟨-k, by ring⟩

/-- Ví dụ theo môđun 5 gồm cả tính phân hoạch và đẳng thức hợp năm lớp bằng ℤ. -/
theorem integerCongruence_five_partition_and_cover :
    IsNonemptyPartition
      {equivalenceClass (integerCongruence 5) 0, equivalenceClass (integerCongruence 5) 1,
       equivalenceClass (integerCongruence 5) 2, equivalenceClass (integerCongruence 5) 3,
       equivalenceClass (integerCongruence 5) 4} ∧
    equivalenceClass (integerCongruence 5) 0 ∪ equivalenceClass (integerCongruence 5) 1 ∪
      equivalenceClass (integerCongruence 5) 2 ∪ equivalenceClass (integerCongruence 5) 3 ∪
      equivalenceClass (integerCongruence 5) 4 = univ := by
  have hp := equivalenceClasses_partition (integerCongruence 5)
    (integerCongruence_equivalence 5 (by norm_num))
  constructor
  · simpa only [integerCongruence_five_classes] using hp
  · ext x
    simp only [mem_univ, iff_true]
    obtain ⟨A, hA, hx⟩ := hp.2.2.1 x
    rw [integerCongruence_five_classes] at hA
    simp only [mem_insert_iff, mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl <;> simp [hx]

/-- Hai màu trong ví dụ tích Descartes. -/
inductive Color where
  | red
  | green
  deriving DecidableEq

/-- Ví dụ tích (a): tích hai tập gồm sáu cặp. -/
theorem color_cartesian_enumeration :
    ({Color.red, Color.green} : Set Color) ×ˢ ({1, 2, 3} : Set ℕ) =
      {(Color.red, 1), (Color.red, 2), (Color.red, 3),
       (Color.green, 1), (Color.green, 2), (Color.green, 3)} := by
  ext ⟨c, n⟩
  cases c <;> simp

/-- Ví dụ tích (b): các cặp số nguyên trong mặt phẳng thực. -/
theorem integer_lattice_coordinates :
    range (fun p : ℤ × ℤ ↦ ((p.1 : ℝ), (p.2 : ℝ))) =
      {p : ℝ × ℝ | (∃ m : ℤ, p.1 = m) ∧ (∃ n : ℤ, p.2 = n)} := by
  ext p
  constructor
  · rintro ⟨⟨m, n⟩, rfl⟩; exact ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    exact ⟨(m, n), Prod.ext hm.symm hn.symm⟩

/-- Ví dụ quan hệ 1(a): đồ thị ba cặp nằm trong tích hai tập đã cho. -/
theorem finite_relation_subset_cartesian :
    ({(1, 3), (1, 5), (3, 3)} : Set (ℕ × ℕ)) ⊆
      ({1, 2, 3} : Set ℕ) ×ˢ ({3, 4, 5} : Set ℕ) := by
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> simp

/-- Ví dụ quan hệ 1(b): quan hệ lớn hơn trên toàn bộ các cặp số nguyên. -/
def integerGreaterRelation : Set (ℤ × ℤ) := {p | p.1 > p.2}

/-- Quan hệ phản xạ: mọi x liên hệ với chính nó. -/
theorem reflexive_criterion (R : X → X → Prop) : Std.Refl R ↔ ∀ x, R x x :=
  ⟨fun h ↦ h.refl, fun h ↦ ⟨h⟩⟩

/-- Quan hệ đối xứng: xRy kéo theo yRx. -/
theorem symmetric_criterion (R : X → X → Prop) :
    Std.Symm R ↔ ∀ x y, R x y → R y x :=
  ⟨fun h x y ↦ h.symm x y, fun h ↦ ⟨fun {_ _} ↦ h _ _⟩⟩

/-- Quan hệ bắc cầu: xRy và yRz kéo theo xRz. -/
theorem transitive_criterion (R : X → X → Prop) :
    IsTrans X R ↔ ∀ x y z, R x y → R y z → R x z :=
  ⟨fun h x y z ↦ h.trans x y z, fun h ↦ ⟨fun _ _ _ ↦ h _ _ _⟩⟩

/-- Quan hệ phản đối xứng: xRy và yRx kéo theo x=y. -/
def IsAntisymmetricRelation (R : X → X → Prop) : Prop := ∀ x y, R x y → R y x → x = y


theorem antisymmetricRelation_iff (R : X → X → Prop) :
    IsAntisymmetricRelation R ↔ Std.Antisymm R := by
  constructor
  · intro h; exact ⟨fun x y ↦ h x y⟩
  · intro h; exact fun x y ↦ h.antisymm x y

/-- Quan hệ thứ tự bộ phận: phản xạ, phản đối xứng và bắc cầu. -/
def IsPartialOrderRelation (R : X → X → Prop) : Prop :=
  (∀ x, R x x) ∧ IsAntisymmetricRelation R ∧ (∀ x y z, R x y → R y z → R x z)

/-- Quan hệ thứ tự bộ phận tương đương với `IsPartialOrder`. -/
theorem partialOrderRelation_iff (R : X → X → Prop) : IsPartialOrderRelation R ↔ IsPartialOrder X R := by
  constructor
  · rintro ⟨hr, ha, ht⟩
    exact { refl := hr, antisymm := fun x y ↦ ha x y, trans := ht }
  · intro h
    exact ⟨h.refl, fun x y ↦ h.antisymm x y, fun x y z ↦ h.trans x y z⟩

/-- Quan hệ tương đương: phản xạ, đối xứng và bắc cầu. -/
theorem equivalence_criterion (R : X → X → Prop) :
    Equivalence R ↔ (∀ x, R x x) ∧ (∀ x y, R x y → R y x) ∧
      (∀ x y z, R x y → R y z → R x z) := by
  constructor
  · intro h; exact ⟨h.refl, fun _ _ ↦ h.symm, fun _ _ _ ↦ h.trans⟩
  · rintro ⟨hr, hs, ht⟩; exact ⟨hr, fun h ↦ hs _ _ h, fun h₁ h₂ ↦ ht _ _ _ h₁ h₂⟩


theorem nonemptyPartition_criterion (C : Set (Set X)) :
    IsNonemptyPartition C ↔ Nonempty X ∧ (∀ A ∈ C, A ≠ ∅) ∧ (∀ x : X, ∃ A ∈ C, x ∈ A) ∧
      ∀ A ∈ C, ∀ B ∈ C, A = B ∨ A ∩ B = ∅ := by
  simp only [IsNonemptyPartition, Set.nonempty_iff_ne_empty]

/-- Bài tập số chính phương (b): phần dư theo môđun 3 là 0 hoặc 1. -/
theorem positive_square_mod_three (n : ℕ+) :
    (n : ℕ) ^ 2 % 3 = 0 ∨ (n : ℕ) ^ 2 % 3 = 1 := by
  have h : (n : ℕ) % 3 = 0 ∨ (n : ℕ) % 3 = 1 ∨ (n : ℕ) % 3 = 2 := by omega
  rcases h with h | h | h <;> norm_num [Nat.pow_mod, h]

/-- Bài tập số chính phương (c): phần dư theo môđun 4 là 0 hoặc 1. -/
theorem positive_square_mod_four (n : ℕ+) :
    (n : ℕ) ^ 2 % 4 = 0 ∨ (n : ℕ) ^ 2 % 4 = 1 := by
  have h : (n : ℕ) % 4 = 0 ∨ (n : ℕ) % 4 = 1 ∨ (n : ℕ) % 4 = 2 ∨ (n : ℕ) % 4 = 3 := by omega
  rcases h with h | h | h | h <;> norm_num [Nat.pow_mod, h]

/-- Bài tập số chính phương (d): phần dư theo môđun 5 là 0,1 hoặc 4. -/
theorem positive_square_mod_five (n : ℕ+) :
    (n : ℕ) ^ 2 % 5 = 0 ∨ (n : ℕ) ^ 2 % 5 = 1 ∨ (n : ℕ) ^ 2 % 5 = 4 := by
  have h : (n : ℕ) % 5 = 0 ∨ (n : ℕ) % 5 = 1 ∨ (n : ℕ) % 5 = 2 ∨
      (n : ℕ) % 5 = 3 ∨ (n : ℕ) % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;> norm_num [Nat.pow_mod, h]

/-- Bài tập số chính phương (e): phần dư theo môđun 8 là 0,1 hoặc 4. -/
theorem positive_square_mod_eight (n : ℕ+) :
    (n : ℕ) ^ 2 % 8 = 0 ∨ (n : ℕ) ^ 2 % 8 = 1 ∨ (n : ℕ) ^ 2 % 8 = 4 := by
  have h : (n : ℕ) % 8 = 0 ∨ (n : ℕ) % 8 = 1 ∨ (n : ℕ) % 8 = 2 ∨
      (n : ℕ) % 8 = 3 ∨ (n : ℕ) % 8 = 4 ∨ (n : ℕ) % 8 = 5 ∨
      (n : ℕ) % 8 = 6 ∨ (n : ℕ) % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> norm_num [Nat.pow_mod, h]

end calculus.Chapter01.Section04Exercises
