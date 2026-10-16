import calculus.Chapter01.Section01

/-!
# 1.2. Luật logic

Nguồn: `source/Ch1_taphop.tex`, dòng 143–287; sách in trang 5–8.
-/

namespace calculus.Chapter01.Section02

/-- Định nghĩa 1.2.1: một mẫu công thức đúng với mọi phép gán các biến mệnh đề. -/
def Tautology {n : Nat} (formula : (Fin n → Prop) → Prop) : Prop :=
  ∀ valuation : Fin n → Prop, formula valuation

/-- Nhận xét 1.2.2: mẫu công thức sai với mọi phép gán. -/
def Contradiction {n : Nat} (formula : (Fin n → Prop) → Prop) : Prop :=
  ∀ valuation : Fin n → Prop, ¬ formula valuation

/-- Nhận xét 1.2.2: phủ định của hằng đúng là hằng sai. -/
theorem contradiction_not_of_tautology {n : Nat} (formula : (Fin n → Prop) → Prop)
    (h : Tautology formula) : Contradiction (fun valuation ↦ ¬ formula valuation) := by
  intro valuation hnot
  exact hnot (h valuation)

/-- Định nghĩa 1.2.4: hai mẫu có cùng chân trị với mọi phép gán. -/
def LogicallyEquivalent {n : Nat} (left right : (Fin n → Prop) → Prop) : Prop :=
  ∀ valuation : Fin n → Prop, left valuation ↔ right valuation

/-- Định nghĩa 1.2.4: hai mẫu tương đương khi và chỉ khi phép tương đương giữa chúng là hằng đúng. -/
theorem logicallyEquivalent_iff_tautology {n : Nat}
    (left right : (Fin n → Prop) → Prop) :
    LogicallyEquivalent left right ↔ Tautology (fun valuation ↦ left valuation ↔ right valuation) :=
  Iff.rfl

/-- Ví dụ 1.2.3: từ hội suy ra tuyển. -/
theorem disjunction_of_conjunction (A B : Prop) : A ∧ B → A ∨ B := by
  intro h
  exact Or.inl h.1

/-- Định lí 1.2.5(i), luật giao hoán của tuyển. -/
theorem disjunction_comm (A B : Prop) : A ∨ B ↔ B ∨ A := or_comm

/-- Định lí 1.2.5(i), luật giao hoán của hội. -/
theorem conjunction_comm (A B : Prop) : A ∧ B ↔ B ∧ A := and_comm

/-- Định lí 1.2.5(ii), luật kết hợp của tuyển. -/
theorem disjunction_assoc (A B C : Prop) : (A ∨ B) ∨ C ↔ A ∨ (B ∨ C) := or_assoc

/-- Định lí 1.2.5(ii), luật kết hợp của hội. -/
theorem conjunction_assoc (A B C : Prop) : (A ∧ B) ∧ C ↔ A ∧ (B ∧ C) := and_assoc

/-- Định lí 1.2.5(iii), hội phân phối qua tuyển. -/
theorem conjunction_distributes (A B C : Prop) :
    A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := and_or_left

/-- Định lí 1.2.5(iii), tuyển phân phối qua hội. -/
theorem disjunction_distributes (A B C : Prop) :
    A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) := or_and_left

/-- Định lí 1.2.5(iv), luật lũy đẳng của hội. -/
theorem conjunction_idempotent (A : Prop) : A ∧ A ↔ A := by simp

/-- Định lí 1.2.5(iv), luật lũy đẳng của tuyển. -/
theorem disjunction_idempotent (A : Prop) : A ∨ A ↔ A := by simp

/-- Định lí 1.2.5(v): hội với hằng đúng. -/
theorem conjunction_true (A : Prop) : A ∧ True ↔ A := by simp

/-- Định lí 1.2.5(v): hội với hằng sai. -/
theorem conjunction_false (A : Prop) : A ∧ False ↔ False := by simp

/-- Định lí 1.2.5(v): tuyển với hằng đúng. -/
theorem disjunction_true (A : Prop) : A ∨ True ↔ True := by simp

/-- Định lí 1.2.5(v): tuyển với hằng sai. -/
theorem disjunction_false (A : Prop) : A ∨ False ↔ A := by simp

/-- Định lí 1.2.5(vi): không thể đồng thời có A và phủ định của A. -/
theorem conjunction_negation (A : Prop) : A ∧ ¬ A ↔ False := by simp

/-- Định lí 1.2.5(vi): luật bài trung. -/
theorem disjunction_negation (A : Prop) : A ∨ ¬ A ↔ True := by
  exact ⟨fun _ ↦ True.intro, fun _ ↦ Classical.em A⟩

/-- Định lí 1.2.5(vii): luật phủ định kép. -/
theorem double_negation (A : Prop) : ¬ ¬ A ↔ A :=
  calculus.Chapter01.Section01.double_negation A

/-- Định lí 1.2.5(viii), luật De Morgan thứ nhất. -/
theorem negation_disjunction (A B : Prop) : ¬ (A ∨ B) ↔ ¬ A ∧ ¬ B := not_or

/-- Định lí 1.2.5(viii), luật De Morgan thứ hai. -/
theorem negation_conjunction (A B : Prop) : ¬ (A ∧ B) ↔ ¬ A ∨ ¬ B := not_and_or

/-- Định lí 1.2.5(ix): luật phản đảo. -/
theorem implication_contrapositive (A B : Prop) : (A → B) ↔ (¬ B → ¬ A) :=
  not_imp_not.symm

/-- Định lí 1.2.5(ix), biểu diễn kéo theo bằng tuyển. -/
theorem implication_iff_disjunction (A B : Prop) : (A → B) ↔ ¬ A ∨ B := imp_iff_not_or

/-- Ví dụ không đánh số, dòng 255–283: chuyển một nhánh tuyển sang giả thiết. -/
theorem implication_disjunction_iff (A B C : Prop) :
    (A → B ∨ C) ↔ (A ∧ ¬ B → C) := by
  classical
  constructor
  · intro h hAB
    rcases h hAB.1 with hB | hC
    · exact False.elim (hAB.2 hB)
    · exact hC
  · intro h hA
    by_cases hB : B
    · exact Or.inl hB
    · exact Or.inr (h ⟨hA, hB⟩)

end calculus.Chapter01.Section02
