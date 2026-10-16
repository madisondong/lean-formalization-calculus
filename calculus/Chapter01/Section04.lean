import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.SymmDiff
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# 1.4. Tập hợp: định nghĩa, phép toán và họ tập

Nguồn: `source/Ch1_taphop.tex`, dòng 390–733.
Định lí 1.4.13 dùng giả thiết tập chỉ số khác rỗng ở dòng 677.
-/

namespace calculus.Chapter01.Section04

open Set
open scoped symmDiff

variable {α ι : Type*}

/-- Dòng 394: không thuộc chính là phủ định của thuộc. -/
theorem not_mem_iff (x : α) (A : Set α) : x ∉ A ↔ ¬ (x ∈ A) := Iff.rfl

/-- Ví dụ 1.4.1: phân biệt số với tập chứa số. -/
abbrev MixedElement := Nat ⊕ Set Nat

/-- Hai phần tử số 0 và 1 của ví dụ 1.4.1. -/
def mixedNumbers : Set MixedElement := {Sum.inl 0, Sum.inl 1}

/-- Tập ba phần tử trong ví dụ 1.4.1: 0, 1 và tập đơn {0}. -/
def mixedNumbersAndSingleton : Set MixedElement :=
  {Sum.inl 0, Sum.inl 1, Sum.inr ({0} : Set Nat)}

/-- Ví dụ 1.4.1: tập A có đúng hai phần tử. -/
theorem mixedNumbers_ncard : mixedNumbers.ncard = 2 := by
  apply Set.ncard_pair
  simp

/-- Ví dụ 1.4.1: tập B có đúng ba phần tử. -/
theorem mixedNumbersAndSingleton_ncard : mixedNumbersAndSingleton.ncard = 3 := by
  simp [mixedNumbersAndSingleton, Set.ncard_insert_of_notMem]

/-- Ví dụ 1.4.1: số 0, số 1 và tập đơn {0} là ba phần tử phân biệt. -/
theorem mixed_elements_distinct :
    (Sum.inl 0 : MixedElement) ≠ Sum.inl 1 ∧
    (Sum.inl 0 : MixedElement) ≠ Sum.inr ({0} : Set Nat) ∧
    (Sum.inl 1 : MixedElement) ≠ Sum.inr ({0} : Set Nat) := by simp

/-- Dòng 400: thứ tự liệt kê và phần tử lặp không làm thay đổi tập hợp. -/
theorem enumeration_order_and_repetition (a b : α) :
    ({a, b} : Set α) = {b, a} ∧ ({a, b, a} : Set α) = {a, b} := by
  constructor <;> ext x <;> simp [or_comm]

/-- Dòng 400–401: tập đơn {0} làm tập B khác tập chỉ chứa hai số. -/
theorem mixedNumbersAndSingleton_ne_mixedNumbers :
    mixedNumbersAndSingleton ≠ mixedNumbers := by
  intro h
  have hm : Sum.inr ({0} : Set Nat) ∈ mixedNumbersAndSingleton := by
    simp [mixedNumbersAndSingleton]
  rw [h] at hm
  simp [mixedNumbers] at hm

/-- Dòng 403–406: các số tự nhiên dương không vượt quá 1000 tạo thành đoạn 1,…,1000. -/
theorem positive_naturals_upto_thousand :
    {n : Nat | 0 < n ∧ n ≤ 1000} = Icc 1 1000 := by
  ext n
  simp only [mem_ofPred_eq, mem_Icc]
  omega

/-- Dòng 405: tập số tự nhiên dương không vượt quá 1000 có đúng 1000 phần tử. -/
theorem positive_naturals_upto_thousand_ncard :
    ({n : Nat | 0 < n ∧ n ≤ 1000} : Set Nat).ncard = 1000 := by
  rw [positive_naturals_upto_thousand, ncard_Icc_nat]

/-- Dòng 412–416: định nghĩa tập con, cho phép hai tập bằng nhau. -/
theorem subset_iff (A B : Set α) : A ⊆ B ↔ ∀ x : α, x ∈ A → x ∈ B := Iff.rfl

/-- Dòng 418: nghiệm nguyên của x²−x=0 là chính xác 0 và 1. -/
theorem integer_quadratic_roots : {x : ℤ | x ^ 2 - x = 0} = {0, 1} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    have hf : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> norm_num

/-- Dòng 420–423: hai tập bằng nhau khi và chỉ khi bao hàm nhau. -/
theorem eq_iff_subsets (A B : Set α) : A = B ↔ A ⊆ B ∧ B ⊆ A :=
  Set.Subset.antisymm_iff

/-- Dòng 424: tập con thực sự gồm bao hàm và không bằng nhau. -/
theorem proper_subset_iff (A B : Set α) : A ⊂ B ↔ A ⊆ B ∧ A ≠ B :=
  Set.ssubset_iff_subset_ne

/-- Dòng 429: phương trình thực x²+1=0 vô nghiệm. -/
theorem real_square_add_one_roots_empty : {x : ℝ | x ^ 2 + 1 = 0} = ∅ := by
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  nlinarith [sq_nonneg x]

/-- Dòng 431: tập không có phần tử là duy nhất, bằng tập rỗng. -/
theorem empty_set_unique (A : Set α) (h : ∀ x : α, x ∉ A) : A = ∅ := by
  ext x
  simp [h x]

/-- Dòng 431: phương trình nguyên x²−2=0 không có nghiệm. -/
theorem integer_square_sub_two_roots_empty : {x : ℤ | x ^ 2 - 2 = 0} = ∅ := by
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro h
  have hb : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
  rcases hb with ⟨hl, hu⟩
  interval_cases x <;> norm_num at h

/-- Dòng 441–442: tập lũy thừa gồm chính các tập con. -/
theorem powerset_membership (A S : Set α) : S ∈ 𝒫 A ↔ S ⊆ A := Iff.rfl

/-- Ví dụ 1.4.2: toàn bộ tám tập con của {0,1,2}. -/
theorem three_element_powerset :
    𝒫 ({0, 1, 2} : Set Nat) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
  simp only [Set.powerset_insert, Set.powerset_singleton, Set.image_insert_eq,
    Set.image_singleton, Set.image_union, insert_empty_eq]
  ext S
  simp only [mem_union, mem_insert_iff, mem_singleton_iff]
  simp only [or_left_comm, or_assoc]


/-- Ví dụ 1.4.2: tập S có ba phần tử và tập lũy thừa có tám phần tử. -/
theorem three_element_powerset_ncard :
    ({0, 1, 2} : Set Nat).ncard = 3 ∧ (𝒫 ({0, 1, 2} : Set Nat)).ncard = 8 := by
  have hs : ({0, 1, 2} : Set Nat).ncard = 3 := by
    simp [Set.ncard_insert_of_notMem]
  constructor
  · exact hs
  · rw [Set.ncard_powerset ({0, 1, 2} : Set Nat) (by simp), hs]
    norm_num

/-- Dòng 443: tập hữu hạn A có n phần tử thì tập lũy thừa có 2ⁿ phần tử. -/
theorem finite_powerset_cardinality (A : Set α) (hA : A.Finite) (n : Nat)
    (hcard : A.ncard = n) : (𝒫 A).ncard = 2 ^ n := by
  rw [Set.ncard_powerset A hA, hcard]

/-- Định nghĩa 1.4.3 và dòng 471: thuộc hợp tương đương phép tuyển. -/
theorem union_membership (A B : Set α) (x : α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

/-- Định nghĩa 1.4.4 và dòng 493: thuộc giao tương đương phép hội. -/
theorem inter_membership (A B : Set α) (x : α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

/-- Dòng 496: hai tập rời nhau khi và chỉ khi giao rỗng. -/
theorem disjoint_iff_inter_empty (A B : Set α) : Disjoint A B ↔ A ∩ B = ∅ :=
  Set.disjoint_iff_inter_eq_empty

/-- Định nghĩa 1.4.5 và dòng 516: x∈A\B khi và chỉ khi x∈A và x∉B. -/
theorem diff_membership (A B : Set α) (x : α) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := Iff.rfl

/-- Dòng 521: luật De Morgan áp dụng cho hiệu tập hợp. -/
theorem not_diff_membership_demorgan (A B : Set α) (x : α) :
    ¬ (x ∈ A \ B) ↔ ¬ (x ∈ A) ∨ ¬ (x ∉ B) := by
  classical
  simp only [mem_sdiff, not_and_or]

/-- Dòng 525: x∉A\B khi và chỉ khi x∉A hoặc x∈B. -/
theorem not_diff_membership (A B : Set α) (x : α) : x ∉ A \ B ↔ x ∉ A ∨ x ∈ B := by
  classical
  simp only [mem_sdiff, not_and_or, not_not]

/-- Dòng 528: phản ví dụ cho tính giao hoán của hiệu. -/
theorem diff_not_commutative :
    ∃ A B : Set Nat, A \ B ≠ B \ A := by
  refine ⟨{0}, ∅, ?_⟩
  simp

/-- Định nghĩa 1.4.6: hiệu đối xứng là hợp của hai hiệu. -/
theorem symmDiff_eq_diffs (A B : Set α) : A ∆ B = (A \ B) ∪ (B \ A) := rfl

/-- Ví dụ 1.4.7: cả năm phép toán với hai tập số cụ thể. -/
theorem finite_set_operations :
    let A : Set Nat := {0, 1, 2, 3, 4, 5}
    let B : Set Nat := {1, 3, 5, 7, 9}
    A ∪ B = {0, 1, 2, 3, 4, 5, 7, 9} ∧
    A ∩ B = {1, 3, 5} ∧
    A \ B = {0, 2, 4} ∧
    B \ A = {7, 9} ∧
    A ∆ B = {0, 2, 4, 7, 9} := by
  dsimp
  repeat' constructor
  all_goals ext x
  all_goals simp only [Set.symmDiff_def, mem_union, mem_inter_iff, mem_sdiff,
    mem_insert_iff, mem_singleton_iff]
  all_goals omega

/-- Mệnh đề 1.4.8(i): hợp, giao và hiệu đối xứng đều giao hoán. -/
theorem set_operations_commutative (A B : Set α) :
    A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A ∧ A ∆ B = B ∆ A :=
  ⟨Set.union_comm A B, Set.inter_comm A B, symmDiff_comm A B⟩

/-- Mệnh đề 1.4.8(ii): hợp và giao có tính kết hợp. -/
theorem set_operations_associative (A B C : Set α) :
    A ∪ (B ∪ C) = (A ∪ B) ∪ C ∧ A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
  ⟨(Set.union_assoc A B C).symm, (Set.inter_assoc A B C).symm⟩

/-- Mệnh đề 1.4.8(iii): hai luật phân phối của hợp và giao. -/
theorem set_operations_distributive (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∧
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  constructor
  · ext x
    exact and_or_left
  · ext x
    exact or_and_left

/-- Mệnh đề 1.4.8(iv): hợp và giao lũy đẳng. -/
theorem set_operations_idempotent (A : Set α) : A ∪ A = A ∧ A ∩ A = A :=
  ⟨Set.union_self A, Set.inter_self A⟩

/-- Mệnh đề 1.4.8(v): hai luật De Morgan tương đối. -/
theorem diff_union_inter (A B C : Set α) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) ∧
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  classical
  constructor <;> ext x
  all_goals by_cases ha : x ∈ A
  all_goals by_cases hb : x ∈ B
  all_goals by_cases hc : x ∈ C
  all_goals simp [ha, hb, hc]


/-- Mệnh đề 1.4.8(vi)(a): hợp của A và B\A bằng A∪B. -/
theorem union_diff_eq_union (A B : Set α) : A ∪ (B \ A) = A ∪ B := by
  classical
  ext x
  by_cases hx : x ∈ A <;> simp [hx]

/-- Mệnh đề 1.4.8(vi)(b): A\B=A\(A∩B). -/
theorem diff_inter_eq_diff (A B : Set α) : A \ B = A \ (A ∩ B) := by
  ext x
  simp only [mem_sdiff, mem_inter_iff]
  exact and_congr_right fun hx => by simp [hx]

/-- Mệnh đề 1.4.8(vi)(c): hợp chia thành phần giao và hiệu đối xứng. -/
theorem union_eq_inter_union_symmDiff (A B : Set α) : A ∪ B = (A ∩ B) ∪ (A ∆ B) := by
  classical
  ext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [Set.symmDiff_def, ha, hb]

/-- Định nghĩa 1.4.9: phần bù được lấy trong tập nền X. -/
def relativeComplement (X A : Set α) : Set α := X \ A

/-- Định nghĩa 1.4.9: phần bù trong X bằng hiệu X\A. -/
theorem relativeComplement_eq_diff (X A : Set α) : relativeComplement X A = X \ A := rfl

/-- Mệnh đề 1.4.10: sáu luật phần bù trong tập nền X. -/
theorem relative_complement_laws (X A B : Set α) (hA : A ⊆ X) (hB : B ⊆ X) :
    A ∪ relativeComplement X A = X ∧
    A ∩ relativeComplement X A = ∅ ∧
    relativeComplement X (A ∩ B) = relativeComplement X A ∪ relativeComplement X B ∧
    relativeComplement X (A ∪ B) = relativeComplement X A ∩ relativeComplement X B ∧
    relativeComplement X (relativeComplement X A) = A ∧
    A \ B = A ∩ relativeComplement X B := by
  classical
  dsimp [relativeComplement]
  repeat' constructor
  all_goals ext x
  all_goals by_cases ha : x ∈ A
  all_goals by_cases hb : x ∈ B
  all_goals by_cases hx : x ∈ X
  all_goals simp_all [subset_def]


/-- Định nghĩa 1.4.11: thuộc hợp của họ là tồn tại một chỉ số. -/
theorem indexed_union_membership (A : ι → Set α) (x : α) :
    x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := Set.mem_iUnion

/-- Định nghĩa 1.4.11: thuộc giao của họ là thuộc mọi tập trong họ. -/
theorem indexed_inter_membership (A : ι → Set α) (x : α) :
    x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i := Set.mem_iInter

/-- Ví dụ 1.4.12(a): các đuôi số tự nhiên dương hợp thành A₁ và có giao rỗng. -/
theorem positive_tail_union_inter :
    (⋃ n : ℕ+, {k : ℕ+ | n ≤ k}) = {k : ℕ+ | 1 ≤ k} ∧
    (⋂ n : ℕ+, {k : ℕ+ | n ≤ k}) = ∅ := by
  constructor
  · ext k
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact le_trans (by exact_mod_cast n.pos) hn
    · intro hk
      exact ⟨1, hk⟩
  · ext k
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    have hb := h ⟨(k : Nat) + 1, by omega⟩
    have hn : (k : Nat) + 1 ≤ k := hb
    omega

/-- Ví dụ 1.4.12(b): các tập {0,n}, n≥1, có hợp là tập số tự nhiên và giao là {0}. -/
theorem zero_positive_pairs_union_inter :
    (⋃ n : ℕ+, ({0, (n : Nat)} : Set Nat)) =
      ({k : Nat | 0 < k} ∪ {0}) ∧
    (⋂ n : ℕ+, ({0, (n : Nat)} : Set Nat)) = {0} := by
  constructor
  · ext k
    simp only [mem_iUnion, mem_union, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl | hn⟩
      · exact Or.inr rfl
      · exact Or.inl (by rw [hn]; exact n.pos)
    · rintro (hk | rfl)
      · exact ⟨⟨k, hk⟩, Or.inr rfl⟩
      · exact ⟨1, Or.inl rfl⟩
  · ext k
    simp only [mem_iInter, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hk
      have h1 := hk 1
      have h2 := hk 2
      norm_num at h1 h2
      omega
    · intro hk n
      exact Or.inl hk

/-- Ví dụ 1.4.12(c): các đoạn [−n,n], n≥1, có hợp ℝ và giao [−1,1]. -/
theorem expanding_closed_intervals_union_inter :
    (⋃ n : ℕ+, Icc (-(n : Nat) : ℝ) (n : Nat)) = univ ∧
    (⋂ n : ℕ+, Icc (-(n : Nat) : ℝ) (n : Nat)) = Icc (-1) 1 := by
  constructor
  · apply eq_univ_of_forall
    intro x
    obtain ⟨m, hm⟩ := exists_nat_gt |x|
    let n : ℕ+ := ⟨m + 1, by omega⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hn : |x| ≤ ((n : Nat) : ℝ) := by
      dsimp [n]
      push_cast
      linarith
    exact abs_le.mp hn
  · ext x
    simp only [mem_iInter, mem_Icc]
    constructor
    · intro h
      simpa using h 1
    · intro hx n
      have hn : (1 : ℝ) ≤ (n : Nat) := by exact_mod_cast n.pos
      constructor <;> linarith [hx.1, hx.2]

/-- Ví dụ 1.4.12(d): khoảng mở (−1/n,1/n) có hợp (−1,1) và giao {0}. -/
theorem shrinking_open_intervals_union_inter :
    (⋃ n : ℕ+, Ioo (-(1 / (n : Nat)) : ℝ) (1 / (n : Nat))) = Ioo (-1) 1 ∧
    (⋂ n : ℕ+, Ioo (-(1 / (n : Nat)) : ℝ) (1 / (n : Nat))) = {0} := by
  constructor
  · ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨n, hx⟩
      have hn : (1 : ℝ) ≤ (n : Nat) := by exact_mod_cast n.pos
      have hi : 1 / ((n : Nat) : ℝ) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
      constructor <;> linarith [hx.1, hx.2]
    · intro hx
      exact ⟨1, by simpa using hx⟩
  · ext x
    simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
      let n : ℕ+ := ⟨m + 1, by omega⟩
      have hn := abs_lt.mpr (hx n)
      have hb : 1 / ((n : Nat) : ℝ) < |x| := by simpa [n] using hm
      linarith
    · rintro rfl n
      have hn : (0 : ℝ) < (n : Nat) := by exact_mod_cast n.pos
      have hi : (0 : ℝ) < 1 / (n : Nat) := one_div_pos.mpr hn
      constructor <;> linarith

/-- Định lí 1.4.13(i): hợp phân phối qua giao của một họ. -/
theorem union_indexed_inter (B : Set α) (A : ι → Set α) :
    B ∪ (⋂ i, A i) = ⋂ i, B ∪ A i := Set.union_iInter B A

/-- Định lí 1.4.13(ii): giao phân phối qua hợp của một họ. -/
theorem inter_indexed_union (B : Set α) (A : ι → Set α) :
    B ∩ (⋃ i, A i) = ⋃ i, B ∩ A i := Set.inter_iUnion B A

/-- Định lí 1.4.13(iii): hiệu của giao biến thành hợp của các hiệu. -/
theorem diff_indexed_inter (B : Set α) (A : ι → Set α) :
    B \ (⋂ i, A i) = ⋃ i, B \ A i := Set.sdiff_iInter B A

/-- Định lí 1.4.13(iv): hiệu của hợp biến thành giao của các hiệu, I khác rỗng. -/
theorem diff_indexed_union [Nonempty ι] (B : Set α) (A : ι → Set α) :
    B \ (⋃ i, A i) = ⋂ i, B \ A i := Set.sdiff_iUnion B A

/-- Định lí 1.4.13(v): De Morgan cho phần bù tương đối của giao họ tập. -/
theorem relative_complement_indexed_inter (X : Set α) (A : ι → Set α) :
    relativeComplement X (⋂ i, A i) = ⋃ i, relativeComplement X (A i) :=
  Set.sdiff_iInter X A

/-- Định lí 1.4.13(vi): De Morgan cho phần bù tương đối của hợp họ tập, I khác rỗng. -/
theorem relative_complement_indexed_union [Nonempty ι] (X : Set α) (A : ι → Set α) :
    relativeComplement X (⋃ i, A i) = ⋂ i, relativeComplement X (A i) :=
  Set.sdiff_iUnion X A

/-- Định lí 1.4.13: các đồng nhất thức cho họ tập con của X có tập chỉ số khác rỗng. -/
theorem indexed_family_laws [Nonempty ι] (X B : Set α) (A : ι → Set α)
    (_hB : B ⊆ X) (_hA : ∀ i, A i ⊆ X) :
    B ∪ (⋂ i, A i) = ⋂ i, B ∪ A i ∧
    B ∩ (⋃ i, A i) = ⋃ i, B ∩ A i ∧
    B \ (⋂ i, A i) = ⋃ i, B \ A i ∧
    B \ (⋃ i, A i) = ⋂ i, B \ A i ∧
    relativeComplement X (⋂ i, A i) = ⋃ i, relativeComplement X (A i) ∧
    relativeComplement X (⋃ i, A i) = ⋂ i, relativeComplement X (A i) :=
  ⟨union_indexed_inter B A, inter_indexed_union B A, diff_indexed_inter B A,
    diff_indexed_union B A, relative_complement_indexed_inter X A,
    relative_complement_indexed_union X A⟩

end calculus.Chapter01.Section04
