import calculus.Chapter04.Section03ExercisesBasic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Bài tập 4.3.39: tổng các hệ số Taylor bậc chẵn của đa thức

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1404–1406. Tổng hữu hạn dừng ở bậc của đa thức.
-/
namespace calculus.Chapter04.Section03PolynomialEvenExercise
open Set Polynomial
open scoped BigOperators


theorem iteratedDeriv_polynomial_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ p.eval x) =
      fun x ↦ ((Polynomial.derivative^[n]) p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simpa only [Function.iterate_succ_apply'] using
      (((Polynomial.derivative^[n]) p).deriv (x := x))


theorem polynomial_taylor_coeff (p : ℝ[X]) (x : ℝ) (n : ℕ) :
    (p.taylor x).coeff n = iteratedDeriv n (fun y : ℝ ↦ p.eval y) x /
      (n.factorial : ℝ) := by
  have h := congrArg (fun q : ℝ[X] ↦ q.eval x)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := n)) p)
  change (n.factorial • Polynomial.hasseDeriv n p).eval x =
    ((Polynomial.derivative^[n]) p).eval x at h
  simp only [nsmul_eq_mul, Polynomial.eval_natCast_mul] at h
  rw [iteratedDeriv_polynomial_eval]
  change (p.taylor x).coeff n = ((Polynomial.derivative^[n]) p).eval x /
    (n.factorial : ℝ)
  rw [Polynomial.taylor_coeff]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using h


theorem iteratedDeriv_polynomial_eval_eq_zero {p : ℝ[X]} {n : ℕ}
    (hn : p.natDegree < n) (x : ℝ) : iteratedDeriv n (fun y : ℝ ↦ p.eval y) x = 0 := by
  have hc : (p.taylor x).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa only [Polynomial.natDegree_taylor] using hn)
  have hz : iteratedDeriv n (fun y : ℝ ↦ p.eval y) x / (n.factorial : ℝ) = 0 := by
    rw [← polynomial_taylor_coeff, hc]
  exact (div_eq_zero_iff.mp hz).resolve_right (by positivity : (n.factorial : ℝ) ≠ 0)


noncomputable def evenTaylorCoefficientSum (p : ℝ[X]) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    if Even k then iteratedDeriv k (fun y : ℝ ↦ p.eval y) x / (k.factorial : ℝ) else 0


theorem evenTaylorCoefficientSum_eq_average (p : ℝ[X]) (x : ℝ) :
    evenTaylorCoefficientSum p x = (p.eval (x + 1) + p.eval (x - 1)) / 2 := by
  have hp (u : ℝ) : p.eval (x + u) =
      ∑ k ∈ Finset.range (p.natDegree + 1), (p.taylor x).coeff k * u ^ k := by
    calc
      _ = (p.taylor x).eval u := by rw [Polynomial.taylor_eval, add_comm]
      _ = _ := by rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_taylor]
  rw [show x - 1 = x + (-1) by ring, hp 1, hp (-1),
    ← Finset.sum_add_distrib, Finset.sum_div]
  unfold evenTaylorCoefficientSum
  apply Finset.sum_congr rfl
  intro k _
  rw [polynomial_taylor_coeff]
  by_cases hk : Even k
  · simp [hk, hk.neg_one_pow]
  · have ho : Odd k := Nat.not_even_iff_odd.mp hk
    simp [hk, ho.neg_one_pow]

/-- Bài 39: nếu đa thức `P` không có nghiệm thực thì tổng các hệ số Taylor bậc chẵn của `P` cũng không có nghiệm thực. -/
theorem evenTaylorCoefficientSum_ne_zero (p : ℝ[X])
    (hne : ∀ x : ℝ, p.eval x ≠ 0) (x : ℝ) : evenTaylorCoefficientSum p x ≠ 0 := by
  have hratio : 0 < p.eval (x + 1) / p.eval (x - 1) :=
    Section03ExercisesBasic.endpoint_ratio_positive (by linarith)
      p.differentiable.continuous.continuousOn (fun y _ ↦ hne y)
  rw [evenTaylorCoefficientSum_eq_average]
  intro hz
  have hs : p.eval (x + 1) + p.eval (x - 1) = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (by norm_num : (2 : ℝ) ≠ 0)
  have he : p.eval (x + 1) / p.eval (x - 1) = -1 := by
    apply (div_eq_iff (hne (x - 1))).mpr
    linarith
  rw [he] at hratio
  norm_num at hratio

end calculus.Chapter04.Section03PolynomialEvenExercise
