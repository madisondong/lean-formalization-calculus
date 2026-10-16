import calculus.Chapter01.Section02

/-!
# 1.3. Quy tắc suy luận và bài tập

Nguồn: `source/Ch1_taphop.tex`, dòng 288–389; sách in trang 8–10.
-/

namespace calculus.Chapter01.Section03

/-- Định nghĩa 1.3.1: với mọi phép gán, các giả thiết cùng đúng thì kết luận đúng. -/
def LogicalConsequence {n : Nat} (premises : List ((Fin n → Prop) → Prop))
    (conclusion : (Fin n → Prop) → Prop) : Prop :=
  ∀ valuation : Fin n → Prop,
    (∀ premise ∈ premises, premise valuation) → conclusion valuation

/-- Một giả thiết: hệ quả logic tương đương với kéo theo là hằng đúng. -/
theorem logicalConsequence_singleton_iff {n : Nat}
    (premise conclusion : (Fin n → Prop) → Prop) :
    LogicalConsequence [premise] conclusion ↔
      calculus.Chapter01.Section02.Tautology (fun valuation ↦ premise valuation → conclusion valuation) := by
  simp [LogicalConsequence, calculus.Chapter01.Section02.Tautology]

/-- Định lí 1.3.2(i), quy tắc kết luận (modus ponens). -/
theorem modus_ponens (A B : Prop) (hAB : A → B) (hA : A) : B := hAB hA

/-- Định lí 1.3.2(ii), quy tắc phủ định (modus tollens). -/
theorem modus_tollens (A B : Prop) (hAB : A → B) (hnotB : ¬ B) : ¬ A := by
  intro hA
  exact hnotB (hAB hA)

/-- Định lí 1.3.2(iii), quy tắc tam đoạn luận. -/
theorem hypothetical_syllogism (A B C : Prop) (hAB : A → B) (hBC : B → C) : A → C := by
  intro hA
  exact hBC (hAB hA)

/-- Định lí 1.3.2(iv): quy tắc phản đảo. -/
theorem converse_contrapositive (A B : Prop) (h : ¬ B → ¬ A) : A → B := by
  intro hA
  apply Classical.byContradiction
  intro hnotB
  exact h hnotB hA

/-- Định lí 1.3.2(v): quy tắc phản chứng. -/
theorem proof_by_contradiction (A B : Prop) (h : A ∧ ¬ B → ¬ A) : A → B := by
  intro hA
  apply Classical.byContradiction
  intro hnotB
  exact h ⟨hA, hnotB⟩ hA

/-- Bài tập 1.3.1(a): kéo theo từ tuyển tương đương hội của hai kéo theo. -/
theorem exercise_or_imp (P Q R : Prop) :
    ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  classical
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- Bài tập 1.3.1(b): kéo theo từ hội tương đương tuyển của hai kéo theo. -/
theorem exercise_and_imp (P Q R : Prop) :
    ((P ∧ Q) → R) ↔ (P → R) ∨ (Q → R) := by
  classical
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- Bài tập 1.3.1(c): kéo theo phân phối qua hội ở kết luận. -/
theorem exercise_imp_and (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  classical
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- Bài tập 1.3.2(a): phủ định tương đương khi hai vế có chân trị khác nhau. -/
theorem exercise_not_iff (P Q : Prop) :
    ¬ (P ↔ Q) ↔ (P ∧ ¬ Q) ∨ (Q ∧ ¬ P) := by
  simp only [iff_def, not_and_or, Classical.not_imp]

/-- Bài tập 1.3.2(b): kéo theo được nhóm thành ((P → Q) → R). -/
theorem exercise_implication_implication (P Q R : Prop) :
    ((P → Q) → R) ↔ (P ∧ ¬ Q) ∨ R := by
  simp only [imp_iff_not_or, not_or, not_not]

/-- Bài tập 1.3.2(c): tách giả thiết P → Q thành hai nhánh ¬P và Q. -/
theorem exercise_implication_implication_split (P Q R : Prop) :
    ((P → Q) → R) ↔ (¬ P → R) ∧ (Q → R) := by
  calc
    ((P → Q) → R) ↔ ((¬ P ∨ Q) → R) :=
      ⟨fun h hOr ↦ h ((calculus.Chapter01.Section02.implication_iff_disjunction P Q).mpr hOr),
        fun h hImp ↦ h ((calculus.Chapter01.Section02.implication_iff_disjunction P Q).mp hImp)⟩
    _ ↔ (¬ P → R) ∧ (Q → R) := or_imp

/-- Bài tập 1.3.2(d): phản đảo của kéo theo từ hội đến tuyển. -/
theorem exercise_contrapositive (P Q R S : Prop) :
    ((P ∧ Q) → R ∨ S) ↔ ((¬ R ∧ ¬ S) → ¬ P ∨ ¬ Q) := by
  simpa only [not_or, not_and_or] using
    calculus.Chapter01.Section02.implication_contrapositive (P ∧ Q) (R ∨ S)

/-- Bài tập 1.3.2(e): chuyển nhánh R sang giả thiết phủ định R. -/
theorem exercise_disjunction_transfer (P Q R S : Prop) :
    ((P ∧ Q) → R ∨ S) ↔ ((P ∧ Q ∧ ¬ R) → S) := by
  simpa only [and_assoc] using
    calculus.Chapter01.Section02.implication_disjunction_iff (P ∧ Q) R S

/-- Bài tập 1.3.2(f): dạng tuyển của kéo theo từ P∧Q đến R∨S. -/
theorem exercise_implication_normal_form (P Q R S : Prop) :
    ((P ∧ Q) → R ∨ S) ↔ (¬ P ∨ ¬ Q ∨ R ∨ S) := by
  simp only [imp_iff_not_or, not_and_or, or_assoc]

/-- Bài tập 1.3.2(g): phủ định của kéo theo và của tuyển. -/
theorem exercise_negated_implication (P Q R S : Prop) :
    ¬ ((P ∧ Q) → R ∨ S) ↔ (P ∧ Q ∧ ¬ R ∧ ¬ S) := by
  simp only [Classical.not_imp, not_or, and_assoc]

/-- Bài tập 1.3.3: năm quy tắc suy luận dưới dạng hằng đúng. -/
theorem exercise_inference_rules (A B C : Prop) :
    (((A → B) ∧ A) → B) ∧
    (((A → B) ∧ ¬ B) → ¬ A) ∧
    (((A → B) ∧ (B → C)) → (A → C)) ∧
    ((¬ B → ¬ A) → (A → B)) ∧
    ((A ∧ ¬ B → ¬ A) → (A → B)) := by
  exact ⟨fun h ↦ modus_ponens A B h.1 h.2,
    fun h ↦ modus_tollens A B h.1 h.2,
    fun h ↦ hypothetical_syllogism A B C h.1 h.2,
    converse_contrapositive A B, proof_by_contradiction A B⟩

/-- Bài tập 1.3.4: ba kéo theo tạo chu trình thì A, B, C đôi một tương đương. -/
theorem exercise_cyclic_equivalence (A B C : Prop)
    (hAB : A → B) (hBC : B → C) (hCA : C → A) :
    (A ↔ B) ∧ (B ↔ C) ∧ (C ↔ A) := by
  exact ⟨⟨hAB, fun hB ↦ hCA (hBC hB)⟩,
    ⟨hBC, fun hC ↦ hAB (hCA hC)⟩,
    ⟨hCA, fun hA ↦ hBC (hAB hA)⟩⟩

end calculus.Chapter01.Section03
