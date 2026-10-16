import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# 2.10. Giới hạn trên, giới hạn dưới: định nghĩa và thứ tự

Nguồn: `source/Ch2_dayso.tex`, dòng 2930–2999 và 3102–3113; mã C02-S11.
-/

namespace calculus.Chapter02.Section10

open Set

/-- Thứ tự mở rộng ở dòng 2932–2933. -/
theorem extended_real_order_bounds (x : EReal) : ⊥ ≤ x ∧ x ≤ ⊤ :=
  ⟨bot_le, le_top⟩

/-- Mọi số thực hữu hạn nằm ngặt giữa hai vô cùng. -/
theorem real_strict_extended_bounds (x : ℝ) :
    (⊥ : EReal) < x ∧ (x : EReal) < ⊤ := ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩

/-- Định nghĩa 2.10.1(a), kể cả tập rỗng. -/
theorem extended_sup_eq_bot_iff (A : Set EReal) : sSup A = ⊥ ↔ A ⊆ {⊥} := by
  simp only [sSup_eq_bot, subset_def, mem_singleton_iff]

/-- Định nghĩa 2.10.1(d), kể cả tập rỗng. -/
theorem extended_inf_eq_top_iff (A : Set EReal) : sInf A = ⊤ ↔ A ⊆ {⊤} := by
  simp only [sInf_eq_top, subset_def, mem_singleton_iff]

/-- Định nghĩa 2.10.1(b): không có cận trên hữu hạn tương đương cận trên bé nhất=+∞. -/
theorem extended_sup_eq_top_iff (A : Set EReal) :
    sSup A = ⊤ ↔ ¬ ∃ r : ℝ, ∀ x ∈ A, x ≤ (r : EReal) := by
  constructor
  · rintro h ⟨r, hr⟩
    have htop : (⊤ : EReal) ≤ r := h ▸ sSup_le hr
    exact (not_le_of_gt (EReal.coe_lt_top r)) htop
  · intro h
    by_contra hne
    obtain ⟨r, hr, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hne)
    exact h ⟨r, fun x hx ↦ (le_sSup hx).trans hr.le⟩

/-- Định nghĩa 2.10.1(c): không có cận dưới hữu hạn tương đương cận dưới lớn nhất=−∞. -/
theorem extended_inf_eq_bot_iff (A : Set EReal) :
    sInf A = ⊥ ↔ ¬ ∃ r : ℝ, ∀ x ∈ A, (r : EReal) ≤ x := by
  constructor
  · rintro h ⟨r, hr⟩
    have hbot : (r : EReal) ≤ ⊥ := h ▸ le_sInf hr
    exact (not_le_of_gt (EReal.bot_lt_coe r)) hbot
  · intro h
    by_contra hne
    obtain ⟨r, _, hr⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hne)
    exact h ⟨r, fun x hx ↦ hr.le.trans (sInf_le hx)⟩

/-- Nhận xét 2.10.2(i): chính xác hai tập có cận trên bé nhất=−∞. -/
theorem extended_sup_eq_bot_iff_empty_or_singleton_bot (A : Set EReal) :
    sSup A = ⊥ ↔ A = ∅ ∨ A = {⊥} := sSup_eq_bot'

/-- Nhận xét 2.10.2(i): chính xác hai tập có cận dưới lớn nhất=+∞. -/
theorem extended_inf_eq_top_iff_empty_or_singleton_top (A : Set EReal) :
    sInf A = ⊤ ↔ A = ∅ ∨ A = {⊤} := sInf_eq_top'

/-- Nếu tập chứa +∞ thì cận trên bé nhất bằng +∞. -/
theorem extended_sup_of_top_mem {A : Set EReal} (h : ⊤ ∈ A) : sSup A = ⊤ :=
  top_unique (le_sSup h)

/-- Nếu tập chứa −∞ thì cận dưới lớn nhất bằng −∞. -/
theorem extended_inf_of_bot_mem {A : Set EReal} (h : ⊥ ∈ A) : sInf A = ⊥ :=
  bot_unique (sInf_le h)

/-- Nhận xét 2.10.2(ii): cận trên bé nhất và cận dưới lớn nhất có chiều đơn điệu đối nhau theo bao hàm. -/
theorem extended_bounds_mono {A B : Set EReal} (h : A ⊆ B) :
    sSup A ≤ sSup B ∧ sInf B ≤ sInf A := ⟨sSup_le_sSup h, sInf_le_sInf h⟩

/-- Nhận xét 2.10.2(iii): mỗi cận dưới không vượt cận dưới lớn nhất. -/
theorem extended_lower_bound_le_inf {A : Set EReal} {m : EReal}
    (h : ∀ x ∈ A, m ≤ x) : m ≤ sInf A := le_sInf h

/-- Nhận xét 2.10.2(iii): mỗi cận trên không nhỏ hơn cận trên bé nhất. -/
theorem extended_sup_le_upper_bound {A : Set EReal} {m : EReal}
    (h : ∀ x ∈ A, x ≤ m) : sSup A ≤ m := sSup_le h

/-- Nhận xét 2.10.2(iv) đúng cả khi một trong hai tập rỗng. -/
theorem extended_sup_le_inf {A B : Set EReal}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) : sSup A ≤ sInf B :=
  sSup_le (fun a ha ↦ le_sInf (h a ha))

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- Phần hữu hạn của một tập số thực mở rộng. -/
def finitePart (A : Set EReal) : Set ℝ := {x | (x : EReal) ∈ A}

/-- C02-S11-prose-L2937 và definition-001.p05: cận trên bé nhất của phần hữu hạn
không rỗng bằng cận trên bé nhất trong `EReal` khi tập bị chặn trên bởi một số thực. -/
theorem finite_part_supremum (A : Set EReal) (r : ℝ)
    (hupper : ∀ x ∈ A, x ≤ (r : EReal))
    (hne : (finitePart A).Nonempty) :
    ∃ s : ℝ, IsLUB (finitePart A) s ∧ sSup A = (s : EReal) := by
  have hb : BddAbove (finitePart A) :=
    ⟨r, fun x hx ↦ EReal.coe_le_coe_iff.mp (hupper x hx)⟩
  obtain ⟨s, hs⟩ := calculus.Chapter02.Section01.real_completeness hne hb
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · apply sSup_le
    intro x hx
    cases x using EReal.rec with
    | bot => exact bot_le
    | coe x => exact EReal.coe_le_coe_iff.mpr (hs.1 hx)
    | top => exact False.elim ((not_le_of_gt (EReal.coe_lt_top r)) (hupper ⊤ hx))
  · generalize he : sSup A = e
    cases e using EReal.rec with
    | bot =>
      obtain ⟨x, hx⟩ := hne
      have h := le_sSup (show (x : EReal) ∈ A from hx)
      rw [he] at h
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe x)) h)
    | coe t =>
      apply EReal.coe_le_coe_iff.mpr
      apply hs.2
      intro x hx
      have h := le_sSup (show (x : EReal) ∈ A from hx)
      rw [he] at h
      exact EReal.coe_le_coe_iff.mp h
    | top => exact le_top

/-- Cận dưới lớn nhất của phần hữu hạn không rỗng bằng cận dưới lớn nhất trong `EReal`
khi tập bị chặn dưới bởi một số thực. -/
theorem finite_part_infimum (A : Set EReal) (r : ℝ)
    (hlower : ∀ x ∈ A, (r : EReal) ≤ x)
    (hne : (finitePart A).Nonempty) :
    ∃ s : ℝ, IsGLB (finitePart A) s ∧ sInf A = (s : EReal) := by
  have hb : BddBelow (finitePart A) :=
    ⟨r, fun x hx ↦ EReal.coe_le_coe_iff.mp (hlower x hx)⟩
  obtain ⟨s, hs⟩ := calculus.Chapter02.Section01.exists_greatestLowerBound hne hb
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · generalize he : sInf A = e
    cases e using EReal.rec with
    | bot => exact bot_le
    | coe t =>
      apply EReal.coe_le_coe_iff.mpr
      apply hs.2
      intro x hx
      have h := sInf_le (show (x : EReal) ∈ A from hx)
      rw [he] at h
      exact EReal.coe_le_coe_iff.mp h
    | top =>
      obtain ⟨x, hx⟩ := hne
      have h := sInf_le (show (x : EReal) ∈ A from hx)
      rw [he] at h
      exact False.elim ((not_le_of_gt (EReal.coe_lt_top x)) h)
  · apply le_sInf
    intro x hx
    cases x using EReal.rec with
    | bot => exact False.elim ((not_le_of_gt (EReal.bot_lt_coe r)) (hlower ⊥ hx))
    | coe x => exact EReal.coe_le_coe_iff.mpr (hs.1 hx)
    | top => exact le_top

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S11-prose-L2937, dòng 2937: khẳng định gốc về cận thực của phần hữu hạn. -/
theorem source_finite_part_extrema_exist (A : Set EReal) (hA : A.Nonempty) :
    ((∃ r : ℝ, ∀ x ∈ A, x ≤ (r : EReal)) →
      ⊤ ∉ A ∧ BddAbove ({x : ℝ | (x : EReal) ∈ A}) ∧
        ∃ s : ℝ, IsLUB ({x : ℝ | (x : EReal) ∈ A}) s) ∧
    ((∃ r : ℝ, ∀ x ∈ A, (r : EReal) ≤ x) →
      ⊥ ∉ A ∧ BddBelow ({x : ℝ | (x : EReal) ∈ A}) ∧
        ∃ s : ℝ, IsGLB ({x : ℝ | (x : EReal) ∈ A}) s) := by
  sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S11-definition-001.p05, dòng 2947: định nghĩa gốc của sup, inf qua phần hữu hạn. -/
theorem source_finite_part_sup_inf_definition (A : Set EReal) :
    ((∃ r : ℝ, ∀ x ∈ A, x ≤ (r : EReal)) →
      ∃ s : ℝ, IsLUB ({x : ℝ | (x : EReal) ∈ A}) s ∧ sSup A = (s : EReal)) ∧
    ((∃ r : ℝ, ∀ x ∈ A, (r : EReal) ≤ x) →
      ∃ s : ℝ, IsGLB ({x : ℝ | (x : EReal) ∈ A}) s ∧ sInf A = (s : EReal)) := by
  sorry

/-- Tập rỗng không có cận trên bé nhất theo nghĩa `IsLUB` trong ℝ. -/
theorem empty_real_set_has_no_lub (a : ℝ) : ¬ IsLUB (∅ : Set ℝ) a := by
  intro h
  have hle : a ≤ a - 1 := h.2 (by simp : a - 1 ∈ upperBounds (∅ : Set ℝ))
  linarith

/-- Bỏ −∞ khỏi tập chỉ chứa −∞ để lại phần hữu hạn rỗng dù có cận trên 0. -/
theorem bottom_only_finite_part_empty :
    (fun x : ℝ ↦ (x : EReal)) ⁻¹' (({⊥} : Set EReal) \ {⊥}) = ∅ := by simp

/-- Bỏ +∞ khỏi tập chỉ chứa +∞ cũng để lại phần hữu hạn rỗng. -/
theorem top_only_finite_part_empty :
    (fun x : ℝ ↦ (x : EReal)) ⁻¹' (({⊤} : Set EReal) \ {⊤}) = ∅ := by simp

/-- Tập số hạng của đuôi k≥n trong số thực mở rộng. -/
def tailRange (u : ℕ → ℝ) (n : ℕ) : Set EReal :=
  {x | ∃ k : ℕ, n ≤ k ∧ x = (u k : EReal)}

/-- sₙ là cận trên bé nhất của đuôi trong số thực mở rộng. -/
noncomputable def tailSup (u : ℕ → ℝ) (n : ℕ) : EReal := sSup (tailRange u n)

/-- tₙ= cận dưới lớn nhất mở rộng của đuôi. -/
noncomputable def tailInf (u : ℕ → ℝ) (n : ℕ) : EReal := sInf (tailRange u n)

/-- Định nghĩa 2.10.3(a): cận dưới lớn nhất của s₁,s₂,…. -/
noncomputable def sequenceLimsup (u : ℕ → ℝ) : EReal := ⨅ n : ℕ, tailSup u (n + 1)

/-- Định nghĩa 2.10.3(b): cận trên bé nhất của t₁,t₂,…. -/
noncomputable def sequenceLiminf (u : ℕ → ℝ) : EReal := ⨆ n : ℕ, tailInf u (n + 1)

/-- Mỗi đuôi khác rỗng vì chứa số hạng đầu. -/
theorem tailRange_nonempty (u : ℕ → ℝ) (n : ℕ) : (tailRange u n).Nonempty :=
  ⟨u n, n, le_rfl, rfl⟩


theorem tailRange_subset {u : ℕ → ℝ} {n m : ℕ} (h : n ≤ m) :
    tailRange u m ⊆ tailRange u n := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, h.trans hk, rfl⟩


theorem tail_bounds_term (u : ℕ → ℝ) (n : ℕ) :
    tailInf u n ≤ (u n : EReal) ∧ (u n : EReal) ≤ tailSup u n :=
  ⟨sInf_le ⟨n, le_rfl, rfl⟩, le_sSup ⟨n, le_rfl, rfl⟩⟩

/-- sₙ giảm và tₙ tăng theo thứ tự không ngặt. -/
theorem tail_bounds_mono {u : ℕ → ℝ} {n m : ℕ} (h : n ≤ m) :
    tailSup u m ≤ tailSup u n ∧ tailInf u n ≤ tailInf u m :=
  extended_bounds_mono (tailRange_subset h)


theorem tail_inf_le_tail_sup (u : ℕ → ℝ) (m n : ℕ) : tailInf u m ≤ tailSup u n := by
  exact (sInf_le (show (u (max m n) : EReal) ∈ tailRange u m from
    ⟨max m n, le_max_left _ _, rfl⟩)).trans
    (le_sSup (show (u (max m n) : EReal) ∈ tailRange u n from
      ⟨max m n, le_max_right _ _, rfl⟩))

/-- Nhận xét 2.10.9(ii): luôn liminf≤limsup trong số thực mở rộng. -/
theorem sequenceLiminf_le_sequenceLimsup (u : ℕ → ℝ) : sequenceLiminf u ≤ sequenceLimsup u :=
  iSup_le (fun m ↦ le_iInf (fun n ↦ tail_inf_le_tail_sup u (m + 1) (n + 1)))

/-- Nhận xét 2.10.9(i): chuỗi cận từ đuôi toàn bộ đến số hạng thứ n. -/
theorem full_tail_bounds (u : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    tailInf u 1 ≤ tailInf u n ∧ tailInf u n ≤ (u n : EReal) ∧
      (u n : EReal) ≤ tailSup u n ∧ tailSup u n ≤ tailSup u 1 :=
  ⟨(tail_bounds_mono hn).2, (tail_bounds_term u n).1,
    (tail_bounds_term u n).2, (tail_bounds_mono hn).1⟩

end calculus.Chapter02.Section10
