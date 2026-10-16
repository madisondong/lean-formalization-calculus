import Mathlib.Logic.Basic

/-!
# 1.1. Các phép toán trên mệnh đề

Nguồn: `source/Ch1_taphop.tex`, dòng 42–142; sách in trang 2–5 (PDF trang 12–15).
-/

namespace calculus.Chapter01.Section01

/-- Bảng chân trị của phép phủ định. -/
theorem negation_truth_table : (¬ True ↔ False) ∧ (¬ False ↔ True) := by
  simp

/-- Bảng chân trị phép hội. -/
theorem conjunction_truth_table :
    (True ∧ True ↔ True) ∧ (True ∧ False ↔ False) ∧
    (False ∧ True ↔ False) ∧ (False ∧ False ↔ False) := by
  simp

/-- Bảng chân trị của phép tuyển bao hàm. -/
theorem disjunction_truth_table :
    (True ∨ True ↔ True) ∧ (True ∨ False ↔ True) ∧
    (False ∨ True ↔ True) ∧ (False ∨ False ↔ False) := by
  simp

/-- Bảng chân trị kéo theo, kể cả khi tiền đề sai. -/
theorem implication_truth_table :
    ((True → True) ↔ True) ∧ ((True → False) ↔ False) ∧
    ((False → True) ↔ True) ∧ ((False → False) ↔ True) := by
  simp

/-- Bảng chân trị tương đương: hai vế có cùng chân trị. -/
theorem equivalence_truth_table :
    ((True ↔ True) ↔ True) ∧ ((True ↔ False) ↔ False) ∧
    ((False ↔ True) ↔ False) ∧ ((False ↔ False) ↔ True) := by
  simp

/-- Luật phủ định của phủ định, dòng 136–139, sách in trang 5. -/
theorem double_negation (A : Prop) : ¬ ¬ A ↔ A :=
  not_not

end calculus.Chapter01.Section01
