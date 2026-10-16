import calculus.Chapter04.Section03Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bài 24: các đạo hàm triệt tiêu ở hai đầu mút

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1195–1196. Xét `a < b`; đạo hàm tại đầu mút là đạo hàm một bên, không cần Cⁿ⁺¹.
-/
namespace calculus.Chapter04.Section03EndpointFlatExercise
open Set Finset calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section01HigherClosed calculus.Chapter04.Section03Taylor
open scoped BigOperators


theorem sum_successors_sub_sum (v : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range N, v (k + 1)) - (∑ k ∈ range N, v k) = v N - v 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    calc
      ((∑ k ∈ range N, v (k + 1)) + v (N + 1)) -
          ((∑ k ∈ range N, v k) + v N) =
        ((∑ k ∈ range N, v (k + 1)) - (∑ k ∈ range N, v k)) + v (N + 1) - v N := by ring
      _ = v (N + 1) - v 0 := by rw [ih]; ring

/-- Bài 24 trên đoạn không suy biến, với các đạo hàm hữu hạn một bên tại đầu mút. -/
theorem source_endpoint_flat_equation_non_degenerate (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval (n + 1) f a b)
    (hz : ∀ k ≤ n, iteratedDerivWithin k f (Icc a b) a = 0 ∧
      iteratedDerivWithin k f (Icc a b) b = 0) :
    ∃ c ∈ Ioo a b, iteratedDerivWithin (n + 1) f (Icc a b) c = f c := by
  have hd := source_closed_to_within hf
  let G : ℝ → ℝ := fun x ↦ ∑ k ∈ range (n + 1), iteratedDerivWithin k f (Icc a b) x
  have hG : ContinuousOn G (Icc a b) :=
    continuousOn_finsetSum (range (n + 1)) fun k hk ↦ (hd k (mem_range.mp hk)).continuousOn
  have hGa : G a = 0 := by
    apply sum_eq_zero
    intro k hk
    exact (hz k (Nat.le_of_lt_succ (mem_range.mp hk))).1
  have hGb : G b = 0 := by
    apply sum_eq_zero
    intro k hk
    exact (hz k (Nat.le_of_lt_succ (mem_range.mp hk))).2
  have hGd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt G (∑ k ∈ range (n + 1), iteratedDerivWithin (k + 1) f (Icc a b) x) x := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hwithin := (hd k (mem_range.mp hk) x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
    simpa only [iteratedDerivWithin_succ] using
      hwithin.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hH (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y : ℝ ↦ Real.exp (-y) * G y)
        (Real.exp (-x) * (iteratedDerivWithin (n + 1) f (Icc a b) x - f x)) x := by
    have hExp : HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (Real.exp (-x) * (-1)) x := by
      simpa only [Pi.neg_apply, id_eq] using ((hasDerivAt_id x).neg.exp)
    have h := hExp.fun_mul (hGd x hx)
    apply h.congr_deriv
    have hs := sum_successors_sub_sum (fun k ↦ iteratedDerivWithin k f (Icc a b) x) (n + 1)
    simp only [iteratedDerivWithin_zero] at hs
    change Real.exp (-x) * (-1) * G x + Real.exp (-x) *
      (∑ k ∈ range (n + 1), iteratedDerivWithin (k + 1) f (Icc a b) x) = _
    calc
      _ = Real.exp (-x) * ((∑ k ∈ range (n + 1),
          iteratedDerivWithin (k + 1) f (Icc a b) x) - G x) := by ring
      _ = _ := by rw [show G x = ∑ k ∈ range (n + 1),
        iteratedDerivWithin k f (Icc a b) x from rfl, hs]
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_zero hf.1
    ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hG)
    (by
      change Real.exp (-a) * G a = Real.exp (-b) * G b
      simp only [hGa, hGb, mul_zero]) hH
  refine ⟨c, hc, ?_⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (Real.exp_pos _).ne')

/-- Bài 24 theo Định nghĩa 2.1.6, với khả vi cấp cao trên đoạn và giá trị đạo hàm tại hai đầu mút. -/
theorem source_endpoint_flat_equation (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval (n + 1) f a b)
    (hz : ∀ k ≤ n, iteratedDerivWithin k f (Icc a b) a = 0 ∧
      iteratedDerivWithin k f (Icc a b) b = 0) :
    ∃ c ∈ Ioo a b, iteratedDerivWithin (n + 1) f (Icc a b) c = f c :=
  source_endpoint_flat_equation_non_degenerate n hf hz

end calculus.Chapter04.Section03EndpointFlatExercise
