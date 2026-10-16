import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Bài 24(d,e,f): công thức đạo hàm cấp n

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 669–671. Bài 24(f) yêu cầu `a, b ≠ 0`.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherCalculations
open calculus.Chapter04.Section01Higher
open scoped ContDiff


theorem affine_sine_hasDerivAt (a c x : ℝ) :
    HasDerivAt (fun y ↦ Real.sin (a * y + c)) (a * Real.cos (a * x + c)) x := by
  have h := (Real.hasDerivAt_sin (a * x + c)).comp x ((hasDerivAt_id x).const_mul a |>.add_const c)
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  ring


theorem affine_cosine_hasDerivAt (a c x : ℝ) :
    HasDerivAt (fun y ↦ Real.cos (a * y + c)) (-a * Real.sin (a * x + c)) x := by
  have h := (Real.hasDerivAt_cos (a * x + c)).comp x ((hasDerivAt_id x).const_mul a |>.add_const c)
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  ring


theorem affine_sine_iteratedDeriv (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun x ↦ Real.sin (a * x)) =
      fun x ↦ a ^ n * Real.sin (a * x + (n : ℝ) * Real.pi / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field']
    funext x
    rw [(affine_sine_hasDerivAt a ((n : ℝ) * Real.pi / 2) x).deriv,
      ← Real.sin_add_pi_div_two, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : a * x + ((n : ℝ) + 1) * Real.pi / 2 =
        (a * x + (n : ℝ) * Real.pi / 2) + Real.pi / 2 := by ring
    rw [hp]
    ring


theorem affine_cosine_iteratedDeriv (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun x ↦ Real.cos (a * x)) =
      fun x ↦ a ^ n * Real.cos (a * x + (n : ℝ) * Real.pi / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field']
    funext x
    rw [(affine_cosine_hasDerivAt a ((n : ℝ) * Real.pi / 2) x).deriv, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : a * x + ((n : ℝ) + 1) * Real.pi / 2 =
        (a * x + (n : ℝ) * Real.pi / 2) + Real.pi / 2 := by ring
    rw [hp, Real.cos_add_pi_div_two]
    ring


theorem affine_exponential_iteratedDeriv (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun x : ℝ ↦ Real.exp (a * x)) = fun x ↦ a ^ n * Real.exp (a * x) := by
  funext x
  exact congrFun (iteratedDeriv_exp_const_mul n a) x

/-- Bài 24(f): đạo hàm cấp `n` của `exp(ax) sin(bx)`. -/
theorem exponential_sine_iteratedDeriv (n : ℕ) (_hn : 1 ≤ n) (a b x : ℝ)
    (_ha : a ≠ 0) (_hb : b ≠ 0) :
    iteratedDeriv n (fun y ↦ Real.exp (a * y) * Real.sin (b * y)) x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (a ^ i * Real.exp (a * x)) *
        (b ^ (n - i) * Real.sin (b * x + ((n - i : ℕ) : ℝ) * Real.pi / 2)) := by
  have he : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (a * y)) :=
    (contDiff_const.mul contDiff_id).exp
  have hs : ContDiff ℝ n (fun y : ℝ ↦ Real.sin (b * y)) :=
    (contDiff_const.mul contDiff_id).sin
  rw [iteratedDeriv_fun_mul he.contDiffAt hs.contDiffAt]
  simp only [affine_exponential_iteratedDeriv, affine_sine_iteratedDeriv]



theorem phase_succ (n : ℕ) (x : ℝ) :
    x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2 =
      (x + (n : ℝ) * Real.pi / 2) + Real.pi / 2 := by
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Bài 24(d): công thức đạo hàm cấp `n+1` của `x sin x`. -/
theorem identity_mul_sine_iteratedDeriv_succ (n : ℕ) :
    iteratedDeriv (n + 1) (fun x : ℝ ↦ x * Real.sin x) =
      fun x ↦ x * Real.sin (x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2) +
        ((n + 1 : ℕ) : ℝ) * Real.sin (x + (n : ℝ) * Real.pi / 2) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext x
    have h := (hasDerivAt_id x).mul (Real.hasDerivAt_sin x)
    have hd : HasDerivAt (fun y : ℝ ↦ y * Real.sin y)
        (1 * Real.sin x + x * Real.cos x) x :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
    rw [hd.deriv]
    simp only [Nat.cast_zero, Nat.cast_one, one_mul, zero_mul,
      zero_div, zero_add, add_zero]
    rw [Real.sin_add_pi_div_two]
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 := (hasDerivAt_id x).mul
      (affine_sine_hasDerivAt 1 (((n + 1 : ℕ) : ℝ) * Real.pi / 2) x)
    have h2 := (affine_sine_hasDerivAt 1 ((n : ℝ) * Real.pi / 2) x).const_mul
      ((n + 1 : ℕ) : ℝ)
    have h := h1.add h2
    have hd : HasDerivAt
        (fun y : ℝ ↦ y * Real.sin (y + ((n + 1 : ℕ) : ℝ) * Real.pi / 2) +
          ((n + 1 : ℕ) : ℝ) * Real.sin (y + (n : ℝ) * Real.pi / 2))
        (Real.sin (x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2) +
          x * Real.cos (x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2) +
          ((n + 1 : ℕ) : ℝ) * Real.cos (x + (n : ℝ) * Real.pi / 2)) x := by
      apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
        simp only [Pi.add_apply, Pi.mul_apply, id_eq, one_mul])).congr_deriv
      simp only [one_mul, id_eq]
    rw [hd.deriv]
    simp only [phase_succ, Real.sin_add_pi_div_two]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Bài 24(d): công thức đạo hàm cấp `n` của `x sin x`. -/
theorem identity_mul_sine_iteratedDeriv (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ y * Real.sin y) x =
      x * Real.sin (x + (n : ℝ) * Real.pi / 2) +
        (n : ℝ) * Real.sin (x + ((n - 1 : ℕ) : ℝ) * Real.pi / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    congrFun (identity_mul_sine_iteratedDeriv_succ m) x



theorem sine_cosine_fourth_eq (x : ℝ) :
    Real.sin x ^ 4 + Real.cos x ^ 4 = 3 / 4 + (1 / 4 : ℝ) * Real.cos (4 * x) := by
  have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq x]
  have hc : Real.cos (4 * x) = 2 * (2 * Real.cos x ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul, Real.cos_two_mul]
  rw [hc, show Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 by ring, hs]
  ring

/-- Bài 24(e): đạo hàm cấp `n` của `sin⁴x + cos⁴x`. -/
theorem sine_cosine_fourth_iteratedDeriv (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ Real.sin y ^ 4 + Real.cos y ^ 4) x =
      (1 / 4 : ℝ) * 4 ^ n * Real.cos (4 * x + (n : ℝ) * Real.pi / 2) := by
  have heq : (fun y : ℝ ↦ Real.sin y ^ 4 + Real.cos y ^ 4) =
      (fun y : ℝ ↦ 3 / 4 + (1 / 4 : ℝ) * Real.cos (4 * y)) := funext sine_cosine_fourth_eq
  rw [heq, iteratedDeriv_const_add (by omega : 0 < n), iteratedDeriv_const_mul_field,
    affine_cosine_iteratedDeriv]
  ring

end calculus.Chapter04.Section01HigherCalculations
