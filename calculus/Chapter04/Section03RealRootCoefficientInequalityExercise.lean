import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# §4.3, Bài 15: hệ số đầu của đa thức có n nghiệm thực phân biệt

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1158–1160. Các hệ số đầu tương ứng với các bậc `n, n−1, n−2`, với `n ≥ 2`.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03RealRootCoefficientInequalityExercise
open Polynomial


theorem quadratic_coefficient_gap {p : ℝ[X]} (hp : p.natDegree = 2)
    (hr : p.roots.toFinset.card = 2) :
    4 * p.coeff 2 * p.coeff 0 < (p.coeff 1) ^ 2 := by
  classical
  have hp0 : p ≠ 0 := by intro h; simp only [h, natDegree_zero] at hp; omega
  have ha : p.coeff 2 ≠ 0 := by
    rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp0
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < p.roots.toFinset.card)
  have hx0 : p.eval x = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hx)
  have hy0 : p.eval y = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hy)
  have heval (z : ℝ) : p.eval z = p.coeff 0 + p.coeff 1 * z + p.coeff 2 * z ^ 2 := by
    rw [Polynomial.eval_eq_sum_range, hp]
    norm_num [Finset.sum_range_succ]
  rw [heval] at hx0 hy0
  have hfactor : (x - y) * (p.coeff 2 * (x + y) + p.coeff 1) = 0 := by
    nlinarith [hx0, hy0]
  have hb : p.coeff 1 = -(p.coeff 2 * (x + y)) := by
    have hh := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hxy)
    linarith
  have hc : p.coeff 0 = p.coeff 2 * x * y := by
    rw [hb] at hx0
    nlinarith [hx0]
  have hs : 0 < (p.coeff 2 * (x - y)) ^ 2 := sq_pos_of_ne_zero
    (mul_ne_zero ha (sub_ne_zero.mpr hxy))
  rw [hb, hc]
  nlinarith [hs]


theorem derivative_distinct_root_count {p : ℝ[X]} {n : ℕ} (hn : 0 < n)
    (hp : p.natDegree = n) (hr : p.roots.toFinset.card = n) :
    p.derivative.roots.toFinset.card = n - 1 := by
  have hlow := p.card_roots_toFinset_le_derivative
  have hup : p.derivative.roots.toFinset.card ≤ n - 1 := by
    calc
      _ ≤ p.derivative.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.derivative.natDegree := p.derivative.card_roots'
      _ = n - 1 := by rw [natDegree_derivative, hp]
  omega

/-- Bài 15: bất đẳng thức ngặt giữa ba hệ số đầu khi có `n ≥ 2` nghiệm thực phân biệt. -/
theorem source_real_root_coefficient_inequality (k : ℕ) {p : ℝ[X]}
    (hp : p.natDegree = k + 2) (hr : p.roots.toFinset.card = k + 2) :
    2 * ((k + 2 : ℕ) : ℝ) * p.coeff (k + 2) * p.coeff k <
      ((k + 1 : ℕ) : ℝ) * (p.coeff (k + 1)) ^ 2 := by
  induction k generalizing p with
  | zero =>
      have he := quadratic_coefficient_gap hp hr
      norm_num at he ⊢
      exact he
  | succ k ih =>
      have hp' : p.derivative.natDegree = k + 2 := by
        rw [natDegree_derivative, hp]
        omega
      have hr' : p.derivative.roots.toFinset.card = k + 2 := by
        have hh := derivative_distinct_root_count (by omega : 0 < k + 1 + 2) hp hr
        have hsub : k + 1 + 2 - 1 = k + 2 := by omega
        rw [hsub] at hh
        exact hh
      have hi := ih hp' hr'
      simp only [coeff_derivative] at hi
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hi ⊢
      have hF : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
      have hscaled :
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
              (2 * ((k : ℝ) + 1 + 2) * p.coeff (k + 1 + 2) * p.coeff (k + 1)) <
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
              (((k : ℝ) + 1 + 1) * (p.coeff (k + 1 + 1)) ^ 2) := by
        have hindex : k + 1 + 1 = k + 2 := by omega
        have hindex' : k + 2 + 1 = k + 1 + 2 := by omega
        rw [hindex, hindex'] at hi
        rw [hindex]
        nlinarith [hi]
      exact (mul_lt_mul_iff_of_pos_left hF).mp hscaled

end calculus.Chapter04.Section03RealRootCoefficientInequalityExercise
