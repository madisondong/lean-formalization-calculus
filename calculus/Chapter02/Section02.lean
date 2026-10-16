import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 2.2. Định nghĩa dãy số

Nguồn: `source/Ch2_dayso.tex`, dòng 590–850.
-/

namespace calculus.Chapter02.Section02

/-- Định nghĩa 2.2.1: dãy số thực với chỉ số tự nhiên dương. -/
abbrev Sequence := ℕ+ → ℝ

/-- Ví dụ 2.2.2: dãy hằng, tất cả số hạng bằng c. -/
def constantSequence (c : ℝ) : Sequence := fun _ => c

/-- Ví dụ 2.2.2: các số hạng bất kỳ của dãy hằng đều bằng nhau. -/
theorem constant_sequence_terms (c : ℝ) (m n : ℕ+) :
    constantSequence c m = c ∧ constantSequence c n = c := ⟨rfl, rfl⟩

/-- Ví dụ 2.2.3: nghịch đảo các số tự nhiên dương; mẫu không bằng 0. -/
noncomputable def reciprocalSequence : Sequence := fun n => 1 / (n : Nat)

/-- Ví dụ 2.2.3: các giá trị tại chỉ số 1,2,3. -/
theorem reciprocal_sequence_first_terms :
    reciprocalSequence 1 = 1 ∧ reciprocalSequence 2 = 1 / 2 ∧
    reciprocalSequence 3 = 1 / 3 := by norm_num [reciprocalSequence]

/-- Ví dụ 2.2.3: mẫu của dãy nghịch đảo dương. -/
theorem reciprocal_sequence_denominator_pos (n : ℕ+) : (0 : ℝ) < (n : Nat) := by
  exact_mod_cast n.pos

/-- Ví dụ 2.2.4: dãy luân phiên −1 và 1. -/
noncomputable def alternatingSequence : Sequence := fun n => (-1 : ℝ) ^ (n : Nat)

/-- Ví dụ 2.2.4: bốn số hạng đầu và hai giá trị ±1 của dãy. -/
theorem alternating_sequence_properties :
    alternatingSequence 1 = -1 ∧ alternatingSequence 2 = 1 ∧
    alternatingSequence 3 = -1 ∧ alternatingSequence 4 = 1 ∧
    (∀ n : ℕ+, alternatingSequence n = 1 ∨ alternatingSequence n = -1) := by
  refine ⟨by norm_num [alternatingSequence], by norm_num [alternatingSequence],
    by norm_num [alternatingSequence], by norm_num [alternatingSequence], ?_⟩
  intro n
  exact neg_one_pow_eq_or ℝ (n : Nat)


theorem arithmetic_recurrence_solution (a : Nat → ℝ) (p d : ℝ)
    (hinit : a 1 = p) (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + d)
    (n : Nat) (hn : 1 ≤ n) : a n = p + ((n : ℝ) - 1) * d := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hinit
  | succ n hn ih =>
    rw [hrec n hn, ih]
    push_cast
    ring


theorem geometric_recurrence_solution (a : Nat → ℝ) (p q : ℝ)
    (hinit : a 1 = p) (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = q * a n)
    (n : Nat) (hn : 1 ≤ n) : a n = p * q ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hinit
  | succ n hn ih =>
    rw [hrec n hn, ih, Nat.add_sub_cancel]
    calc
      q * (p * q ^ (n - 1)) = p * (q ^ (n - 1) * q) := by ring
      _ = p * q ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]

/-- Ví dụ 2.2.5 và dòng 651: cấp số cộng 2,5,8,… -/
theorem arithmetic_example_formula (a : Nat → ℝ) (hinit : a 1 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + 3) (n : Nat) (hn : 1 ≤ n) :
    a n = 2 + 3 * ((n : ℝ) - 1) := by
  rw [arithmetic_recurrence_solution a 2 3 hinit hrec n hn]
  ring

/-- Ví dụ 2.2.5: các số hạng được liệt kê. -/
theorem arithmetic_example_first_terms (a : Nat → ℝ) (hinit : a 1 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + 3) :
    a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 8 ∧ a 4 = 11 ∧ a 5 = 14 ∧ a 6 = 17 := by
  have hf := arithmetic_example_formula a hinit hrec
  repeat' constructor
  all_goals rw [hf _ (by norm_num)]
  all_goals norm_num

/-- Ví dụ 2.2.6: công thức cấp số nhân 2,6,18,… -/
theorem geometric_example_formula (a : Nat → ℝ) (hinit : a 1 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n) (n : Nat) (hn : 1 ≤ n) :
    a n = 2 * 3 ^ (n - 1) := geometric_recurrence_solution a 2 3 hinit hrec n hn

/-- Ví dụ 2.2.6: năm số hạng đầu. -/
theorem geometric_example_first_terms (a : Nat → ℝ) (hinit : a 1 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n) :
    a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 18 ∧ a 4 = 54 ∧ a 5 = 162 := by
  have hf := geometric_example_formula a hinit hrec
  repeat' constructor
  all_goals rw [hf _ (by norm_num)]
  all_goals norm_num

/-- Ví dụ 2.2.7: bₙ=aₙ−4 là cấp số nhân. -/
theorem affine_example_geometric_bridge (a : Nat → ℝ) (hinit : a 1 = 6)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n - 8) :
    a 1 - 4 = 2 ∧ ∀ n : Nat, 1 ≤ n → a (n + 1) - 4 = 3 * (a n - 4) := by
  constructor
  · linarith
  · intro n hn
    rw [hrec n hn]
    ring

/-- Ví dụ 2.2.7: aₙ=2·3ⁿ⁻¹+4. -/
theorem affine_example_formula (a : Nat → ℝ) (hinit : a 1 = 6)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n - 8) (n : Nat) (hn : 1 ≤ n) :
    a n = 2 * 3 ^ (n - 1) + 4 := by
  have hb := affine_example_geometric_bridge a hinit hrec
  have hf := geometric_recurrence_solution (fun k => a k - 4) 2 3 hb.1 hb.2 n hn
  linarith

/-- Ví dụ 2.2.7: năm số hạng đầu. -/
theorem affine_example_first_terms (a : Nat → ℝ) (hinit : a 1 = 6)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n - 8) :
    a 1 = 6 ∧ a 2 = 10 ∧ a 3 = 22 ∧ a 4 = 58 ∧ a 5 = 166 := by
  have hf := affine_example_formula a hinit hrec
  repeat' constructor
  all_goals rw [hf _ (by norm_num)]
  all_goals norm_num

/-- Nhận xét 2.2.8: phép biến đổi afin của truy hồi. -/
theorem affine_change_iff (x y α β : ℝ) :
    y + α = β * (x + α) ↔ y = β * x + α * β - α := by
  constructor <;> intro h <;> nlinarith

/-- Nhận xét 2.2.8: hệ hệ số có nghiệm duy nhất. -/
theorem affine_example_coefficients (α β : ℝ) :
    (β = 3 ∧ α * β - α = -8) ↔ (β = 3 ∧ α = -4) := by
  constructor
  · rintro ⟨rfl, h⟩
    constructor
    · rfl
    · linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Ví dụ 2.2.9: phép đổi biến đưa truy hồi về cấp số nhân. -/
theorem exponential_example_geometric_bridge (a : Nat → ℝ) (hinit : a 1 = 22)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n + 5 * 4 ^ n) :
    a 1 - 5 * 4 ^ (1 : Nat) = 2 ∧
    ∀ n : Nat, 1 ≤ n → a (n + 1) - 5 * 4 ^ (n + 1) = 3 * (a n - 5 * 4 ^ n) := by
  constructor
  · norm_num [hinit]
  · intro n hn
    rw [hrec n hn, pow_succ]
    ring

/-- Ví dụ 2.2.9: aₙ=2·3^(n−1)+5·4ⁿ. -/
theorem exponential_example_formula (a : Nat → ℝ) (hinit : a 1 = 22)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n + 5 * 4 ^ n)
    (n : Nat) (hn : 1 ≤ n) : a n = 2 * 3 ^ (n - 1) + 5 * 4 ^ n := by
  have hb := exponential_example_geometric_bridge a hinit hrec
  have hf := geometric_recurrence_solution (fun k => a k - 5 * 4 ^ k) 2 3 hb.1 hb.2 n hn
  linarith

/-- Ví dụ 2.2.9: các số hạng đầu và giá trị a₂₀₂₄. -/
theorem exponential_example_terms_and_2024 (a : Nat → ℝ) (hinit : a 1 = 22)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = 3 * a n + 5 * 4 ^ n) :
    a 1 = 22 ∧ a 2 = 86 ∧ a 3 = 338 ∧ a 4 = 1334 ∧
    a 2024 = 2 * 3 ^ (2023 : Nat) + 5 * 4 ^ (2024 : Nat) := by
  have hf := exponential_example_formula a hinit hrec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf 1 (by norm_num)]; norm_num
  · rw [hf 2 (by norm_num)]; norm_num
  · rw [hf 3 (by norm_num)]; norm_num
  · rw [hf 4 (by norm_num)]; norm_num
  · exact hf 2024 (by norm_num)

/-- Ví dụ 2.2.10: hệ phương trình theo α,β còn có nghiệm (−4,3), ngoài (−3,4). -/
theorem second_order_coefficients_counterexample :
    (3 : ℝ) - (-4) = 7 ∧ (-4 : ℝ) * 3 = -12 ∧
    ¬ ((3 : ℝ) = 4 ∧ (-4 : ℝ) = -3) := by norm_num

/-- Ví dụ 2.2.10: hệ phương trình theo α,β có đúng hai nghiệm. -/
theorem second_order_coefficients_corrected (α β : ℝ) :
    (β - α = 7 ∧ α * β = -12) ↔
      (β = 4 ∧ α = -3) ∨ (β = 3 ∧ α = -4) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hα : α = β - 7 := by linarith
    rw [hα] at h2
    have hf : (β - 4) * (β - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hβ | hβ
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Ví dụ 2.2.10: bₙ=aₙ₊₁−3aₙ là cấp số nhân công bội 4. -/
theorem second_order_geometric_bridge (a : Nat → ℝ) (h1 : a 1 = 22) (h2 : a 2 = 86)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = 7 * a (n + 1) - 12 * a n) :
    a 2 - 3 * a 1 = 20 ∧
    ∀ n : Nat, 1 ≤ n → a (n + 2) - 3 * a (n + 1) = 4 * (a (n + 1) - 3 * a n) := by
  constructor
  · norm_num [h1, h2]
  · intro n hn
    rw [hrec n hn]
    ring

/-- Ví dụ 2.2.10: công thức bₙ=5·4ⁿ dẫn đến truy hồi cấp 1. -/
theorem second_order_first_order_bridge (a : Nat → ℝ) (h1 : a 1 = 22) (h2 : a 2 = 86)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = 7 * a (n + 1) - 12 * a n)
    (n : Nat) (hn : 1 ≤ n) : a (n + 1) = 3 * a n + 5 * 4 ^ n := by
  have hb := second_order_geometric_bridge a h1 h2 hrec
  have hr : ∀ k : Nat, 1 ≤ k →
      (a ((k + 1) + 1) - 3 * a (k + 1)) = 4 * (a (k + 1) - 3 * a k) := by
    simpa only [Nat.add_assoc] using hb.2
  have hi : a (1 + 1) - 3 * a 1 = 20 := hb.1
  have hf := geometric_recurrence_solution (fun k => a (k + 1) - 3 * a k) 20 4 hi hr n hn
  have hp : (20 : ℝ) * 4 ^ (n - 1) = 5 * 4 ^ n := by
    calc
      (20 : ℝ) * 4 ^ (n - 1) = 5 * (4 ^ (n - 1) * 4) := by ring
      _ = 5 * 4 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hp] at hf
  linarith

/-- Ví dụ 2.2.10: công thức tường minh của dãy truy hồi. -/
theorem second_order_example_formula (a : Nat → ℝ) (h1 : a 1 = 22) (h2 : a 2 = 86)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = 7 * a (n + 1) - 12 * a n)
    (n : Nat) (hn : 1 ≤ n) : a n = 2 * 3 ^ (n - 1) + 5 * 4 ^ n :=
  exponential_example_formula a h1 (second_order_first_order_bridge a h1 h2 hrec) n hn

/-- Ví dụ 2.2.11: truy hồi xác định dãy Fibonacci tại n≥1. -/
theorem fibonacci_recurrence_eq_natFib (F : Nat → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → F (n + 2) = F (n + 1) + F n)
    (n : Nat) (hn : 1 ≤ n) : F n = (Nat.fib n : ℝ) := by
  have hshift : ∀ k : Nat, F (k + 1) = (Nat.fib (k + 1) : ℝ) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [h1]
    | one => norm_num [h2]
    | more k ih0 ih1 =>
      have hr := hrec (k + 1) (by omega)
      have hb : Nat.fib ((k + 2) + 1) = Nat.fib (k + 1) + Nat.fib ((k + 1) + 1) := by
        simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := k + 1))
      rw [hb]
      push_cast
      rw [← ih0, ← ih1]
      have hi : (k + 2) + 1 = (k + 1) + 2 := by omega
      rw [hi, hr]
      ring
  simpa only [Nat.sub_add_cancel hn] using hshift (n - 1)

/-- Ví dụ 2.2.11: ba số hạng sau F₁,F₂ là 2,3,5. -/
theorem fibonacci_first_terms (F : Nat → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    F 3 = 2 ∧ F 4 = 3 ∧ F 5 = 5 := by
  have hf := fibonacci_recurrence_eq_natFib F h1 h2 hrec
  repeat' constructor
  all_goals rw [hf _ (by norm_num)]
  all_goals norm_num

/-- Ví dụ 2.2.11: công thức Binet của dãy Fibonacci. -/
theorem fibonacci_binet_formula (F : Nat → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → F (n + 2) = F (n + 1) + F n)
    (n : Nat) (hn : 1 ≤ n) :
    F n = 1 / Real.sqrt 5 *
      (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) := by
  rw [fibonacci_recurrence_eq_natFib F h1 h2 hrec n hn, Real.coe_fib_eq]
  simp only [Real.goldenRatio, Real.goldenConj]
  ring

/-- Ví dụ 2.2.11: mẫu √5 trong công thức Binet khác 0. -/
theorem fibonacci_binet_denominator_ne_zero : Real.sqrt 5 ≠ 0 := by
  positivity

/-- Nhận xét 2.2.12(ii): các cách đánh chỉ số 0,1,2 cho cùng dãy nghịch đảo tích. -/
theorem reciprocal_product_reindexing (n : Nat) :
    (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
      1 / (((n + 1 : Nat) : ℝ) * (((n + 1 : Nat) : ℝ) + 1)) ∧
    (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
      1 / ((((n + 2 : Nat) : ℝ) - 1) * ((n + 2 : Nat) : ℝ)) := by
  constructor <;> push_cast <;> ring

/-- Ví dụ 2.2.9: phép đổi aₙ+α 4ⁿ với các hệ số chưa chọn. -/
theorem exponential_change_iff (x y α β : ℝ) (n : Nat) :
    y + α * 4 ^ (n + 1) = β * (x + α * 4 ^ n) ↔
      y = β * x + (α * β - 4 * α) * 4 ^ n := by
  rw [pow_succ]
  constructor <;> intro h <;> nlinarith

/-- Ví dụ 2.2.9: hệ hệ số cho biến đổi không thuần nhất. -/
theorem exponential_example_coefficients (α β : ℝ) :
    (β = 3 ∧ α * β - 4 * α = 5) ↔ (β = 3 ∧ α = -5) := by
  constructor
  · rintro ⟨rfl, h⟩
    constructor
    · rfl
    · linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Ví dụ 2.2.10: đồng nhất thức biến đổi truy hồi cấp hai. -/
theorem second_order_change_iff (x y z α β : ℝ) :
    y + α * x = β * (x + α * z) ↔ y = (β - α) * x + α * β * z := by
  constructor <;> intro h <;> nlinarith

/-- Bài tập 2.2.1(b): dãy hữu tỉ có ba số hạng giống dãy đã cho. -/
noncomputable def rationalExerciseSequence : Sequence := fun n =>
  6 / ((((n : Nat) : ℝ) + 1) * (((n : Nat) : ℝ) ^ 2 - (n : Nat) + 6))

/-- Bài tập 2.2.1(b): năm số hạng đầu dưới dạng hữu tỉ. -/
theorem rational_exercise_first_five :
    rationalExerciseSequence 1 = 1 / 2 ∧ rationalExerciseSequence 2 = 1 / 4 ∧
    rationalExerciseSequence 3 = 1 / 8 ∧ rationalExerciseSequence 4 = 1 / 15 ∧
    rationalExerciseSequence 5 = 1 / 26 := by norm_num [rationalExerciseSequence]

/-- Bài tập 2.2.1(a): ba số hạng đầu không xác định toàn bộ dãy. -/
theorem three_terms_do_not_determine_sequence :
    ∃ a : Sequence, a 1 = 1 / 2 ∧ a 2 = 1 / 4 ∧ a 3 = 1 / 8 ∧ a 4 ≠ 1 / 2 ^ (4 : Nat) := by
  refine ⟨rationalExerciseSequence, rational_exercise_first_five.1,
    rational_exercise_first_five.2.1, rational_exercise_first_five.2.2.1, ?_⟩
  rw [rational_exercise_first_five.2.2.2.1]
  norm_num

/-- Bài tập 2.2.1(c): mẫu 9x²−25x+18 dương trên toàn ℝ, do biệt thức âm. -/
theorem rational_quadratic_denominator_pos (x : ℝ) : 0 < 9 * x ^ 2 - 25 * x + 18 := by
  nlinarith [sq_nonneg (18 * x - 25)]

/-- Bài tập 2.2.1(c): chọn A=9,B=−25,C=18 cho ba số hạng yêu cầu. -/
theorem rational_quadratic_coefficients_solution :
    ∃ A B C : ℝ,
      (∀ n : ℕ+, A * ((n : Nat) : ℝ) ^ 2 + B * (n : Nat) + C ≠ 0) ∧
      ((1 : ℝ) ^ 2 - 3 * 1 + 3) / (A * 1 ^ 2 + B * 1 + C) = 1 / 2 ∧
      ((2 : ℝ) ^ 2 - 3 * 2 + 3) / (A * 2 ^ 2 + B * 2 + C) = 1 / 4 ∧
      ((3 : ℝ) ^ 2 - 3 * 3 + 3) / (A * 3 ^ 2 + B * 3 + C) = 1 / 8 := by
  refine ⟨9, -25, 18, ?_, ?_⟩
  · intro n
    apply ne_of_gt
    have h := rational_quadratic_denominator_pos ((n : Nat) : ℝ)
    nlinarith
  · norm_num

/-- Bài tập 2.2.9: lạm phát 4,5% ứng với hệ số 209/200. -/
noncomputable def inflationPrice (n : Nat) : ℝ := 500000000 * (209 / 200 : ℝ) ^ n

/-- Bài tập 2.2.9: giá từng năm 1–5, tính bằng đồng. -/
theorem inflation_prices_five_years :
    inflationPrice 1 = 522500000 ∧ inflationPrice 2 = 546012500 ∧
    inflationPrice 3 = 1141166125 / 2 ∧ inflationPrice 4 = 9540148805 / 16 ∧
    inflationPrice 5 = 398778220049 / 640 := by norm_num [inflationPrice]

/-- Bài tập 2.2.3(a): công thức của dãy 1,0,1,0,… -/
theorem alternating_sum_recurrence_formula (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + (-1) ^ n)
    (n : Nat) (hn : 1 ≤ n) : a n = (1 - (-1) ^ n) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    rw [hrec n hn, ih, pow_succ]
    ring

/-- Bài tập 2.2.3(a): số hạng 2024 bằng 0. -/
theorem alternating_sum_term_2024 (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + (-1) ^ n) : a 2024 = 0 := by
  rw [alternating_sum_recurrence_formula a h1 hrec 2024 (by norm_num)]
  norm_num

/-- Bài tập 2.2.3(b): truy hồi nhân với n+1 xác định dãy giai thừa. -/
theorem factorial_recurrence_formula (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = ((n : ℝ) + 1) * a n)
    (n : Nat) (hn : 1 ≤ n) : a n = (Nat.factorial n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    rw [hrec n hn, ih, Nat.factorial_succ]
    push_cast
    rfl

/-- Bài tập 2.2.3(b): số hạng 2024 bằng 2024!. -/
theorem factorial_term_2024 (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = ((n : ℝ) + 1) * a n) :
    a 2024 = (Nat.factorial 2024 : ℝ) := factorial_recurrence_formula a h1 hrec 2024 (by norm_num)

/-- Bài tập 2.2.3(c): lấy căn liên tiếp cho aₙ=(1/2)^((1/2)^(n−1)). -/
theorem sqrt_recurrence_formula (a : Nat → ℝ) (h1 : a 1 = 1 / 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = Real.sqrt (a n))
    (n : Nat) (hn : 1 ≤ n) : a n = Real.rpow (1 / 2) ((1 / 2 : ℝ) ^ (n - 1)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    rw [hrec n hn, ih, Real.sqrt_eq_rpow]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Nat.add_sub_cancel]
    rw [← pow_succ, Nat.sub_add_cancel hn]

/-- Bài tập 2.2.3(c): số hạng 2024 dưới dạng lũy thừa thực chính xác. -/
theorem sqrt_term_2024 (a : Nat → ℝ) (h1 : a 1 = 1 / 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = Real.sqrt (a n)) :
    a 2024 = Real.rpow (1 / 2) ((1 / 2 : ℝ) ^ (2023 : Nat)) :=
  sqrt_recurrence_formula a h1 hrec 2024 (by norm_num)

/-- Bài tập 2.2.5: dãy mẫu có chu kì 5, với các giá trị 1,2,3,2,1. -/
def periodicFiveValue (n : Nat) : ℝ :=
  match n % 5 with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | _ => 1

/-- Bài tập 2.2.5: dãy chu kì 5 thỏa truy hồi. -/
theorem periodicFive_recurrence (n : Nat) :
    periodicFiveValue (n + 2) = (1 + periodicFiveValue (n + 1)) / periodicFiveValue n := by
  have hbound : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize hr : n % 5 = r at *
  interval_cases r <;> norm_num [periodicFiveValue, Nat.add_mod, hr]

/-- Bài tập 2.2.5: truy hồi và hai số hạng đầu xác định dãy chu kì 5. -/
theorem periodic_five_formula (a : Nat → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = (1 + a (n + 1)) / a n)
    (n : Nat) (hn : 1 ≤ n) : a n = periodicFiveValue n := by
  have hshift : ∀ k : Nat, a (k + 1) = periodicFiveValue (k + 1) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simpa [periodicFiveValue] using h1
    | one => simpa [periodicFiveValue] using h2
    | more k ih0 ih1 =>
      have hi : (k + 2) + 1 = (k + 1) + 2 := by omega
      rw [hi, hrec (k + 1) (by omega), ih0, ih1]
      exact (periodicFive_recurrence (k + 1)).symm
  simpa only [Nat.sub_add_cancel hn] using hshift (n - 1)

/-- Bài tập 2.2.5: số hạng 2023 bằng 3. -/
theorem periodic_five_term_2023 (a : Nat → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = (1 + a (n + 1)) / a n) : a 2023 = 3 := by
  rw [periodic_five_formula a h1 h2 hrec 2023 (by norm_num)]
  norm_num [periodicFiveValue]

/-- Bài tập 2.2.6: phương trình hàm dãy kéo theo công thức aₙ=n². -/
theorem quadratic_functional_sequence_formula (a : Nat → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hfun : ∀ m n : Nat, n ≤ m → a (m + n) + a (m - n) = (a (2 * m) + a (2 * n)) / 2)
    (n : Nat) : a n = (n : ℝ) ^ 2 := by
  have hd : ∀ m : Nat, a (2 * m) = 4 * a m := by
    intro m
    have h := hfun m 0 (Nat.zero_le m)
    simp only [Nat.add_zero, Nat.sub_zero, Nat.mul_zero, h0] at h
    linarith
  have h2 : a 2 = 4 := by simpa [h1] using hd 1
  have hr : ∀ k : Nat, a (k + 2) = 2 * a (k + 1) - a k + 2 := by
    intro k
    have h := hfun (k + 1) 1 (by omega)
    have hs : k + 1 - 1 = k := by omega
    have ht : (k + 1) + 1 = k + 2 := by omega
    rw [hs, ht, hd (k + 1), h2] at h
    linarith
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simpa using h1
  | more k ih0 ih1 =>
    rw [hr, ih0, ih1]
    push_cast
    ring

/-- Bài tập 2.2.6: số hạng 1000 bằng 1000000. -/
theorem quadratic_functional_term_1000 (a : Nat → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hfun : ∀ m n : Nat, n ≤ m → a (m + n) + a (m - n) = (a (2 * m) + a (2 * n)) / 2) :
    a 1000 = 1000000 := by
  rw [quadratic_functional_sequence_formula a h0 h1 hfun]
  norm_num

/-- Bài tập 2.2.4(c): công thức dãy có hiệu liên tiếp 2n−3. -/
theorem quadratic_difference_recurrence (a : Nat → ℝ) (h1 : a 1 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + 2 * (n : ℝ) - 3)
    (n : Nat) (hn : 1 ≤ n) : a n = (n : ℝ) ^ 2 - 4 * n + 5 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih => rw [hrec n hn, ih]; push_cast; ring

/-- Bài tập 2.2.4(d): truy hồi a/(1+a) cho nghịch đảo 1/n. -/
theorem reciprocal_recurrence (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n / (1 + a n))
    (n : Nat) (hn : 1 ≤ n) : a n = 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [hrec n hn, ih]
    push_cast
    field_simp

/-- Bài tập 2.2.4(e): công thức có phần đa thức và lũy thừa 5ⁿ. -/
theorem polynomial_exponential_recurrence (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + 3 * (n : ℝ) - 1 - 2 * 5 ^ n)
    (n : Nat) (hn : 1 ≤ n) :
    a n = (3 * (n : ℝ) ^ 2 - 5 * n + 9 - 5 ^ n) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih => rw [hrec n hn, ih, pow_succ]; push_cast; ring

/-- Bài tập 2.2.4(f): công thức tổng hiệu bậc 2 là đa thức bậc 3. -/
theorem cubic_difference_recurrence (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = a n + 2 * (n : ℝ) ^ 2 + 3 * n + 4)
    (n : Nat) (hn : 1 ≤ n) :
    a n = (4 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 + 17 * n - 18) / 6 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih => rw [hrec n hn, ih]; push_cast; ring

/-- Bài tập 2.2.4(g): sai phân cấp hai bằng 0, nghiệm aₙ=n. -/
theorem linear_second_order_recurrence (a : Nat → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 2)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = 2 * a (n + 1) - a n)
    (n : Nat) (hn : 1 ≤ n) : a n = (n : ℝ) := by
  have hshift : ∀ k : Nat, a (k + 1) = ((k + 1 : Nat) : ℝ) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [h1]
    | one => norm_num [h2]
    | more k ih0 ih1 =>
      have hi : (k + 2) + 1 = (k + 1) + 2 := by omega
      rw [hi, hrec (k + 1) (by omega), ih0, ih1]
      push_cast
      ring
  simpa only [Nat.sub_add_cancel hn] using hshift (n - 1)

/-- Bài tập 2.2.4(h): tổng hai cấp số nhân công bội 2 và 3. -/
theorem two_geometric_second_order_recurrence (a : Nat → ℝ) (h1 : a 1 = 2) (h2 : a 2 = 5)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 2) = 5 * a (n + 1) - 6 * a n)
    (n : Nat) (hn : 1 ≤ n) : a n = 2 ^ (n - 1) + 3 ^ (n - 1) := by
  have hshift : ∀ k : Nat, a (k + 1) = (2 : ℝ) ^ k + (3 : ℝ) ^ k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [h1]
    | one => norm_num [h2]
    | more k ih0 ih1 =>
      have hi : (k + 2) + 1 = (k + 1) + 2 := by omega
      rw [hi, hrec (k + 1) (by omega), ih0, ih1]
      simp only [pow_succ]
      ring
  simpa only [Nat.sub_add_cancel hn] using hshift (n - 1)

/-- Bài tập 2.2.4(a): tổng 1/(1·3)+…+1/((2n−1)(2n+1)) bằng n/(2n+1). -/
theorem odd_reciprocal_product_sum (n : Nat) :
    (∑ k ∈ Finset.range n, 1 / (((2 : ℝ) * k + 1) * (2 * k + 3))) =
      (n : ℝ) / (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- Bài tập 2.2.7: mọi số hạng của truy hồi aₙ₊₁=aₙ²+aₙ là dương. -/
theorem square_add_recurrence_positive (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = (a n) ^ 2 + a n)
    (n : Nat) (hn : 1 ≤ n) : 0 < a n := by
  induction n, hn using Nat.le_induction with
  | base => rw [h1]; norm_num
  | succ n hn ih => rw [hrec n hn]; nlinarith [sq_nonneg (a n)]

/-- Bài tập 2.2.7: một số hạng là hiệu nghịch đảo của hai số hạng liên tiếp. -/
theorem square_add_recurrence_reciprocal_difference (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = (a n) ^ 2 + a n)
    (n : Nat) (hn : 1 ≤ n) : 1 / (1 + a n) = 1 / a n - 1 / a (n + 1) := by
  have hp := square_add_recurrence_positive a h1 hrec n hn
  have ha : a n ≠ 0 := ne_of_gt hp
  have hsum : 1 + a n ≠ 0 := by linarith
  rw [hrec n hn, show (a n) ^ 2 + a n = a n * (1 + a n) by ring]
  field_simp
  ring

/-- Bài tập 2.2.7: tổng bằng 1−1/aₙ₊₁. -/
theorem square_add_recurrence_sum_formula (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = (a n) ^ 2 + a n) (n : Nat) :
    (∑ k ∈ Finset.range n, 1 / (1 + a (k + 1))) = 1 - 1 / a (n + 1) := by
  induction n with
  | zero => simp [h1]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      square_add_recurrence_reciprocal_difference a h1 hrec (n + 1) (by omega)]
    ring

/-- Bài tập 2.2.7: tổng n số hạng nhỏ hơn 1. -/
theorem square_add_recurrence_sum_lt_one (a : Nat → ℝ) (h1 : a 1 = 1)
    (hrec : ∀ n : Nat, 1 ≤ n → a (n + 1) = (a n) ^ 2 + a n)
    (n : Nat) (_hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, 1 / (1 + a (k + 1))) < 1 := by
  rw [square_add_recurrence_sum_formula a h1 hrec]
  have hp := square_add_recurrence_positive a h1 hrec (n + 1) (by omega)
  have hi := one_div_pos.mpr hp
  linarith

/-- Bài tập 2.2.4(b): số hạng chứa căn thu gọn thành hiệu 1/√x−1/√(x+1). -/
theorem reciprocal_sqrt_product_difference (x : ℝ) (hx : 0 < x) :
    1 / ((x + 1) * Real.sqrt x + x * Real.sqrt (x + 1)) =
      1 / Real.sqrt x - 1 / Real.sqrt (x + 1) := by
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hs1 : Real.sqrt (x + 1) ≠ 0 := by positivity
  have hd : (x + 1) * Real.sqrt x + x * Real.sqrt (x + 1) ≠ 0 := by positivity
  have hsq0 := Real.sq_sqrt (le_of_lt hx)
  have hsq1 := Real.sq_sqrt (by linarith : 0 ≤ x + 1)
  have hp0 : (x + 1) * Real.sqrt x ^ 2 = (x + 1) * x := by rw [hsq0]
  have hp1 : x * Real.sqrt (x + 1) ^ 2 = x * (x + 1) := by rw [hsq1]
  field_simp
  nlinarith [hp0, hp1]

/-- Bài tập 2.2.4(b): tổng n số hạng bằng 1−1/√(n+1). -/
theorem reciprocal_sqrt_product_sum (n : Nat) :
    (∑ k ∈ Finset.range n,
      1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1) +
        ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2))) =
      1 - 1 / Real.sqrt ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have ht : 1 / (((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1) +
        ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) =
        1 / Real.sqrt ((n : ℝ) + 1) - 1 / Real.sqrt ((n : ℝ) + 2) := by
      simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using
        reciprocal_sqrt_product_difference ((n : ℝ) + 1) (by positivity)
    rw [ht]
    have hs : ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 := by ring
    rw [hs]
    ring

/-- Bài tập 2.2.2(c): mười số hạng n mod 5 lấy n=2,…,11. -/
theorem residue_mod_five_first_ten :
    [2 % 5, 3 % 5, 4 % 5, 5 % 5, 6 % 5, 7 % 5, 8 % 5, 9 % 5, 10 % 5, 11 % 5] =
      ([2, 3, 4, 0, 1, 2, 3, 4, 0, 1] : List Nat) := by norm_num

/-- Bài tập 2.2.8(b): trung bình cộng và trung bình nhân nằm ngặt giữa hai số dương khác nhau. -/
theorem arithmetic_geometric_step_strict (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    (a + b) / 2 < a ∧ Real.sqrt (a * b) < (a + b) / 2 ∧ b < Real.sqrt (a * b) := by
  have ha : 0 < a := lt_trans hb hab
  have hm : 0 < (a + b) / 2 := by positivity
  have hprod : 0 ≤ a * b := by positivity
  have hsq : 0 < (a - b) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  refine ⟨by linarith, (Real.sqrt_lt hprod (le_of_lt hm)).mpr ?_,
    (Real.lt_sqrt (le_of_lt hb)).mpr ?_⟩
  · nlinarith
  · nlinarith

/-- Bài tập 2.2.8: 0<bₙ<aₙ tại mọi chỉ số. -/
theorem arithmetic_geometric_recurrence_invariant (a b : Nat → ℝ)
    (hb0 : 0 < b 0) (hab0 : b 0 < a 0)
    (ha : ∀ n : Nat, a (n + 1) = (a n + b n) / 2)
    (hb : ∀ n : Nat, b (n + 1) = Real.sqrt (a n * b n)) (n : Nat) :
    0 < b n ∧ b n < a n := by
  induction n with
  | zero => exact ⟨hb0, hab0⟩
  | succ n ih =>
    have hs := arithmetic_geometric_step_strict (a n) (b n) ih.1 ih.2
    rw [ha n, hb n]
    exact ⟨lt_trans ih.1 hs.2.2, hs.2.1⟩

/-- Bài tập 2.2.8(b): aₙ>aₙ₊₁>bₙ₊₁>bₙ. -/
theorem arithmetic_geometric_recurrence_strict_chain (a b : Nat → ℝ)
    (hb0 : 0 < b 0) (hab0 : b 0 < a 0)
    (ha : ∀ n : Nat, a (n + 1) = (a n + b n) / 2)
    (hb : ∀ n : Nat, b (n + 1) = Real.sqrt (a n * b n)) (n : Nat) :
    a (n + 1) < a n ∧ b (n + 1) < a (n + 1) ∧ b n < b (n + 1) := by
  have hi := arithmetic_geometric_recurrence_invariant a b hb0 hab0 ha hb n
  rw [ha n, hb n]
  exact arithmetic_geometric_step_strict (a n) (b n) hi.1 hi.2

/-- Bài tập 2.2.8(a): bảng căn thức tại các chỉ số 0,…,10. -/
theorem arithmetic_geometric_first_eleven_exact (a b : Nat → ℝ)
    (ha0 : a 0 = 10) (hb0 : b 0 = 3)
    (ha : ∀ n : Nat, a (n + 1) = (a n + b n) / 2)
    (hb : ∀ n : Nat, b (n + 1) = Real.sqrt (a n * b n)) :
    let p2 : ℝ × ℝ := ((13 / 2 + Real.sqrt 30) / 2, Real.sqrt (13 / 2 * Real.sqrt 30))
    let p3 : ℝ × ℝ := ((p2.1 + p2.2) / 2, Real.sqrt (p2.1 * p2.2))
    let p4 : ℝ × ℝ := ((p3.1 + p3.2) / 2, Real.sqrt (p3.1 * p3.2))
    let p5 : ℝ × ℝ := ((p4.1 + p4.2) / 2, Real.sqrt (p4.1 * p4.2))
    let p6 : ℝ × ℝ := ((p5.1 + p5.2) / 2, Real.sqrt (p5.1 * p5.2))
    let p7 : ℝ × ℝ := ((p6.1 + p6.2) / 2, Real.sqrt (p6.1 * p6.2))
    let p8 : ℝ × ℝ := ((p7.1 + p7.2) / 2, Real.sqrt (p7.1 * p7.2))
    let p9 : ℝ × ℝ := ((p8.1 + p8.2) / 2, Real.sqrt (p8.1 * p8.2))
    let p10 : ℝ × ℝ := ((p9.1 + p9.2) / 2, Real.sqrt (p9.1 * p9.2))
    (List.range 11).map (fun n => (a n, b n)) =
      [(10, 3), (13 / 2, Real.sqrt 30), p2, p3, p4, p5, p6, p7, p8, p9, p10] := by
  dsimp
  norm_num [List.range_succ, ha, hb, ha0, hb0]

/-- Bài tập 2.2.8(a): b tăng ngặt và bₙ<aₙ. -/
theorem arithmetic_geometric_example_comparisons (a b : Nat → ℝ)
    (ha0 : a 0 = 10) (hb0 : b 0 = 3)
    (ha : ∀ n : Nat, a (n + 1) = (a n + b n) / 2)
    (hb : ∀ n : Nat, b (n + 1) = Real.sqrt (a n * b n)) (n : Nat) :
    b n < b (n + 1) ∧ b n < a n := by
  have hp : 0 < b 0 := by norm_num [hb0]
  have hlt : b 0 < a 0 := by norm_num [ha0, hb0]
  exact ⟨(arithmetic_geometric_recurrence_strict_chain a b hp hlt ha hb n).2.2,
    (arithmetic_geometric_recurrence_invariant a b hp hlt ha hb n).2⟩

end calculus.Chapter02.Section02
