import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bài 24(h): xⁿ⁻¹ exp(1/x)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 673.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherExponentialExercise
open Filter Set
open scoped ContDiff Topology


theorem linear_factor_iteratedDeriv (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ} (x : ℝ)
    (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun y : ℝ ↦ y * f y) x =
      x * iteratedDeriv n f x + (n : ℝ) * iteratedDeriv (n - 1) f x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change iteratedDeriv (m + 1) (fun y : ℝ ↦ id y * f y) x =
    x * iteratedDeriv (m + 1) f x + ((m + 1 : ℕ) : ℝ) * iteratedDeriv m f x
  rw [iteratedDeriv_fun_mul (f := id) contDiff_id.contDiffAt hf]
  let t := fun i : ℕ ↦ ((m + 1).choose i : ℝ) * iteratedDeriv i id x *
    iteratedDeriv (m + 1 - i) f x
  change ∑ i ∈ Finset.range (m + 2), t i = _
  rw [Finset.sum_range_succ' t (m + 1), Finset.sum_range_succ' (fun i ↦ t (i + 1)) m]
  have hz : ∑ i ∈ Finset.range m, t (i + 1 + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [t, iteratedDeriv_id]
  rw [hz]
  simp [t, iteratedDeriv_id, Nat.choose_one_right]
  ring


def powerMulExpReciprocal (m : ℕ) (x : ℝ) : ℝ := x ^ m * Real.exp (1 / x)


theorem exponential_reciprocal_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (1 / y)) (-Real.exp (1 / x) / x ^ 2) x := by
  have h := (Real.hasDerivAt_exp x⁻¹).comp x
    ((hasDerivAt_id x).inv hx)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by simp [one_div])).congr_deriv
  simp only [id_eq, one_div]
  ring


theorem powerMulExpReciprocal_iteratedDeriv (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iteratedDeriv (m + 1) (powerMulExpReciprocal m) x =
      (-1 : ℝ) ^ (m + 1) * Real.exp (1 / x) / x ^ (m + 2) := by
  induction m generalizing x with
  | zero =>
    have hfun : powerMulExpReciprocal 0 = fun y : ℝ ↦ Real.exp (1 / y) := by
      funext y
      simp [powerMulExpReciprocal]
    rw [iteratedDeriv_one, hfun, (exponential_reciprocal_hasDerivAt x hx).deriv]
    ring
  | succ m ih =>
    have hf : ContDiffAt ℝ (m + 2) (powerMulExpReciprocal m) x := by
      exact (contDiffAt_id.pow m).mul ((contDiffAt_id.inv hx).exp.congr_of_eventuallyEq
        (Eventually.of_forall fun y ↦ by simp [one_div]))
    have heq : powerMulExpReciprocal (m + 1) = fun y : ℝ ↦ y * powerMulExpReciprocal m y := by
      funext y
      simp only [powerMulExpReciprocal, pow_succ]
      ring
    have hnear : iteratedDeriv (m + 1) (powerMulExpReciprocal m) =ᶠ[𝓝 x]
        fun y : ℝ ↦ (-1 : ℝ) ^ (m + 1) * Real.exp (1 / y) / y ^ (m + 2) := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
      exact ih y hy
    have hder := ((exponential_reciprocal_hasDerivAt x hx).const_mul ((-1 : ℝ) ^ (m + 1))).fun_div
      (hasDerivAt_pow (m + 2) x) (pow_ne_zero _ hx)
    rw [heq, linear_factor_iteratedDeriv (m + 2) (by omega) x hf,
      show m + 2 - 1 = m + 1 by omega, ih x hx]
    have hd : iteratedDeriv (m + 2) (powerMulExpReciprocal m) x =
        (((-1 : ℝ) ^ (m + 1) * (-Real.exp (1 / x) / x ^ 2)) * x ^ (m + 2) -
          ((-1 : ℝ) ^ (m + 1) * Real.exp (1 / x)) *
            (((m + 2 : ℕ) : ℝ) * x ^ (m + 1))) / (x ^ (m + 2)) ^ 2 := by
      rw [show m + 2 = (m + 1) + 1 by omega, iteratedDeriv_succ,
        hnear.deriv_eq, hder.deriv]
      simp only [show m + 2 - 1 = m + 1 by omega]
    rw [hd]
    simp only [Nat.cast_add]
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    rw [pow_succ]
    field_simp [hx]
    ring

/-- Bài 24(h): công thức đạo hàm cấp `n` của `xⁿ⁻¹ exp(1/x)` trên `x ≠ 0`. -/
theorem power_exponential_reciprocal_iteratedDeriv (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ y ^ (n - 1) * Real.exp (1 / y)) x =
      (-1 : ℝ) ^ n * Real.exp (1 / x) / x ^ (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change iteratedDeriv (m + 1) (powerMulExpReciprocal m) x =
    (-1 : ℝ) ^ (m + 1) * Real.exp (1 / x) / x ^ (m + 2)
  exact powerMulExpReciprocal_iteratedDeriv m x hx

end calculus.Chapter04.Section01HigherExponentialExercise
