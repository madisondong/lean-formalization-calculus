import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Dẫn nhập Chương 1: mệnh đề và chân trị

Nguồn: `source/Ch1_taphop.tex`, dòng 15–39.
-/
namespace calculus.Chapter01.Section00

/-- Logic cổ điển: mỗi mệnh đề đúng hoặc sai, không đồng thời cả hai. -/
theorem proposition_bivalence (P : Prop) : (P ∨ ¬ P) ∧ ¬ (P ∧ ¬ P) := by
  exact ⟨Classical.em P, fun h ↦ h.2 h.1⟩

/-- Ví dụ C: 3>5 là sai. -/
theorem three_not_gt_five : ¬ (3 : ℕ) > 5 := by norm_num

/-- Ví dụ D: 3<5 là đúng. -/
theorem three_lt_five : (3 : ℕ) < 5 := by norm_num

/-- Hợp số: tích của hai số tự nhiên đều lớn hơn 1. -/
def Composite (n : ℕ) : Prop := ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n

/-- Mỗi số tự nhiên n>1 là nguyên tố hoặc hợp số. -/
theorem prime_or_composite (n : ℕ) (hn : 1 < n) : Nat.Prime n ∨ Composite n := by
  classical
  by_cases hp : Nat.Prime n
  · exact Or.inl hp
  · right
    have hex : ∃ a b : ℕ, a < n ∧ b < n ∧ a * b = n := by
      by_contra h
      exact hp (Nat.prime_iff_not_exists_mul_eq.mpr ⟨by omega, h⟩)
    rcases hex with ⟨a, b, ha, hb, he⟩
    refine ⟨a, b, ?_, ?_, he⟩
    · by_contra h
      have hz : a = 0 ∨ a = 1 := by omega
      rcases hz with hz | hz <;> subst a <;> simp_all
    · by_contra h
      have hz : b = 0 ∨ b = 1 := by omega
      rcases hz with hz | hz <;> subst b <;> simp_all

/-- Mệnh đề E: 126^3728 + 15^15876 + 8 là số nguyên tố. -/
def PrimalityStatementE : Prop := Nat.Prime ((126 ^ 3728 + 15 ^ 15876) + 8)

end calculus.Chapter01.Section00
