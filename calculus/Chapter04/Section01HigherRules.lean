import calculus.Chapter04.Section01Higher
import calculus.Chapter04.Section01OscillatingExercises
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Abel

/-!
# 4.1.20(iii,iv): Leibniz và khả vi cấp cao của thương

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 362–363. Hàm chỉ cần khả vi `n` lần; tổng Leibniz chạy từ 0 đến `n`, và công thức thương yêu cầu mẫu khác 0 trên miền.
-/
namespace calculus.Chapter04.Section01HigherRules
open Set calculus.Chapter04.Section01Higher


theorem differentiableToOrderOn_succ (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) :
    DifferentiableToOrderOn (n + 1) f I ↔
      DifferentiableOn ℝ f I ∧ DifferentiableToOrderOn n (derivWithin f I) I := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [iteratedDerivWithin_zero] using h 0 (Nat.zero_lt_succ n)
    · intro k hk
      simpa only [← iteratedDerivWithin_succ'] using h (k + 1) (Nat.succ_lt_succ hk)
  · rintro ⟨hf, hd⟩ k hk
    cases k with
    | zero => simpa only [iteratedDerivWithin_zero] using hf
    | succ k => simpa only [iteratedDerivWithin_succ'] using hd k (Nat.lt_of_succ_lt_succ hk)


theorem differentiableToOrderOn_congr (n : ℕ) {f g : ℝ → ℝ} {I : Set ℝ}
    (hfg : EqOn f g I) (hf : DifferentiableToOrderOn n f I) : DifferentiableToOrderOn n g I := by
  intro k hk
  exact (hf k hk).congr (iteratedDerivWithin_congr hfg.symm)


theorem source_mul_higher (n : ℕ) {f g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hf : DifferentiableToOrderOn n f I) (hg : DifferentiableToOrderOn n g I) :
    DifferentiableToOrderOn n (fun x ↦ f x * g x) I ∧
      EqOn (iteratedDerivWithin n (fun x ↦ f x * g x) I)
        (fun x ↦ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * iteratedDerivWithin i f I x * iteratedDerivWithin (n - i) g I x) I := by
  induction n generalizing f g with
  | zero =>
    exact ⟨fun k hk ↦ (Nat.not_lt_zero k hk).elim, by simp [EqOn]⟩
  | succ n ih =>
    have hf' := (differentiableToOrderOn_succ n f I).mp hf
    have hg' := (differentiableToOrderOn_succ n g I).mp hg
    have hf0 : DifferentiableToOrderOn n f I := fun k hk ↦ hf k (hk.trans_le n.le_succ)
    have hg0 : DifferentiableToOrderOn n g I := fun k hk ↦ hg k (hk.trans_le n.le_succ)
    have hleft := ih hf0 hg'.2
    have hright := ih hf'.2 hg0
    have hsum := source_add_higher n hI hleft.1 hright.1
    have hder : EqOn (derivWithin (fun x ↦ f x * g x) I)
        (fun x ↦ f x * derivWithin g I x + derivWithin f I x * g x) I := by
      intro x hx
      rw [derivWithin_fun_mul (hf'.1 x hx) (hg'.1 x hx), add_comm]
    refine ⟨(differentiableToOrderOn_succ n _ I).mpr ⟨hf'.1.mul hg'.1,
      differentiableToOrderOn_congr n hder.symm hsum.1⟩, ?_⟩
    intro x hx
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr hder hx, hsum.2 n le_rfl hx]
    dsimp only
    rw [hleft.2 hx, hright.2 hx]
    rw [Finset.sum_range_succ' (fun i ↦ ((n + 1).choose i : ℝ) *
      iteratedDerivWithin i f I x * iteratedDerivWithin (n + 1 - i) g I x) (n + 1)]
    simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i ↦ (n.choose i : ℝ) *
      iteratedDerivWithin i f I x * iteratedDerivWithin (n - i) (derivWithin g I) I x) n]
    rw [Finset.sum_range_succ (fun i ↦ (n.choose (i + 1) : ℝ) *
      iteratedDerivWithin (i + 1) f I x * iteratedDerivWithin (n + 1 - (i + 1)) g I x) n]
    have hn : ∀ i ∈ Finset.range n, 1 ≤ n - i := by
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub,
      Nat.sub_add_cancel, hn]
    abel


theorem source_inv_higher (n : ℕ) {g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hg : DifferentiableToOrderOn n g I) (hzero : ∀ x ∈ I, g x ≠ 0) :
    DifferentiableToOrderOn n (fun x ↦ (g x)⁻¹) I := by
  induction n with
  | zero => exact fun k hk ↦ (Nat.not_lt_zero k hk).elim
  | succ n ih =>
    have hg' := (differentiableToOrderOn_succ n g I).mp hg
    have hg0 : DifferentiableToOrderOn n g I := fun k hk ↦ hg k (hk.trans_le n.le_succ)
    have hi := ih hg0
    have hsquare := (source_mul_higher n hI hi hi).1
    have hprod := (source_mul_higher n hI hg'.2 hsquare).1
    have hneg := (source_const_mul_higher n hprod (-1)).1
    have hder : EqOn (derivWithin (fun x ↦ (g x)⁻¹) I)
        (fun x ↦ (-1 : ℝ) * (derivWithin g I x * ((g x)⁻¹ * (g x)⁻¹))) I := by
      intro x hx
      rw [derivWithin_fun_inv' (hg'.1 x hx) (hzero x hx)]
      simp only [div_eq_mul_inv, pow_two]
      ring
    apply (differentiableToOrderOn_succ n _ I).mpr
    exact ⟨hg'.1.inv hzero, differentiableToOrderOn_congr n hder.symm hneg⟩

/-- Định lí 4.1.20(iv): thương của hai hàm khả vi `n` lần cũng khả vi `n` lần khi mẫu khác 0 trên miền. -/
theorem source_div_higher (n : ℕ) {f g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hf : DifferentiableToOrderOn n f I) (hg : DifferentiableToOrderOn n g I)
    (hzero : ∀ x ∈ I, g x ≠ 0) : DifferentiableToOrderOn n (fun x ↦ f x / g x) I := by
  simpa only [div_eq_mul_inv] using
    (source_mul_higher n hI hf (source_inv_higher n hI hg hzero)).1


theorem source_mul_positive_order (n : ℕ) (_hn : 1 ≤ n) {f g : ℝ → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hf : DifferentiableToOrderOn n f I)
    (hg : DifferentiableToOrderOn n g I) :
    DifferentiableToOrderOn n (fun x ↦ f x * g x) I ∧
      EqOn (iteratedDerivWithin n (fun x ↦ f x * g x) I)
        (fun x ↦ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * iteratedDerivWithin i f I x * iteratedDerivWithin (n - i) g I x) I :=
  source_mul_higher n hI hf hg

theorem source_div_positive_order (n : ℕ) (_hn : 1 ≤ n) {f g : ℝ → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hf : DifferentiableToOrderOn n f I)
    (hg : DifferentiableToOrderOn n g I) (hzero : ∀ x ∈ I, g x ≠ 0) :
    DifferentiableToOrderOn n (fun x ↦ f x / g x) I := source_div_higher n hI hf hg hzero

/-- Nhận xét 4.1.23(i): trường hợp `n = 1` cho hàm khả vi nhưng không thuộc C¹. -/
theorem differentiable_not_domainC_one :
    ∃ f : ℝ → ℝ, DifferentiableToOrderOn 1 f univ ∧ ¬DomainC 1 f univ := by
  let f := Section01OscillatingExercises.quadraticSineReciprocal
  refine ⟨f, (differentiableToOrderOn_one f univ).mpr
    Section01OscillatingExercises.quadratic_differentiable.differentiableOn, ?_⟩
  intro hc
  have hcont : ContDiff ℝ 1 f := contDiffOn_univ.mp ((domainC_iff_contDiffOn 1 f isOpen_univ).mp hc)
  exact Section01OscillatingExercises.quadratic_derivative_not_continuousAt_zero
    hcont.continuous_deriv_one.continuousAt

end calculus.Chapter04.Section01HigherRules
