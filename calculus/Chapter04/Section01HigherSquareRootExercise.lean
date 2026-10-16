import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Bài 20: dấu các đạo hàm của √(x²−1) trên x>1

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 644–646.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherSquareRootExercise
open Filter Set Polynomial
open scoped Topology ContDiff


def quadraticSquareRoot (x : ℝ) : ℝ := Real.sqrt (x ^ 2 - 1)


theorem descending_negative_pochhammer (q : ℝ) (n : ℕ) :
    (descPochhammer ℝ n).eval (-q) = (-1 : ℝ) ^ n * (ascPochhammer ℝ n).eval q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ascPochhammer_succ_eval, ih, pow_succ]
    ring


theorem shifted_negative_power_iteratedDeriv (n : ℕ) (q c x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ (y - c) ^ (-q)) x =
      (-1 : ℝ) ^ n * (ascPochhammer ℝ n).eval q * (x - c) ^ (-q - n) := by
  have hs := congrFun (iteratedDeriv_comp_sub_const n (fun y : ℝ ↦ y ^ (-q)) c) x
  calc
    _ = iteratedDeriv n (fun y : ℝ ↦ y ^ (-q)) (x - c) := hs
    _ = _ := by
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
        descending_negative_pochhammer]


theorem shifted_negative_power_contDiffAt (n : ℕ) (q c x : ℝ) (hx : c < x) :
    ContDiffAt ℝ n (fun y : ℝ ↦ (y - c) ^ (-q)) x := by
  have hs : ContDiffAt ℝ n (fun y : ℝ ↦ y - c) x :=
    contDiffAt_id.sub contDiffAt_const
  exact hs.rpow_const_of_ne (sub_ne_zero.mpr hx.ne')


def derivativeMagnitude (n : ℕ) (q x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    ((ascPochhammer ℝ i).eval q * (x - 1) ^ (-q - i)) *
    ((ascPochhammer ℝ (n - i)).eval q * (x + 1) ^ (-q - (n - i)))


theorem derivativeMagnitude_pos (n : ℕ) (q x : ℝ) (hq : 0 < q) (hx : 1 < x) :
    0 < derivativeMagnitude n q x := by
  have hleft : 0 < x - 1 := sub_pos.mpr hx
  have hright : 0 < x + 1 := by linarith
  apply Finset.sum_pos'
  · intro i hi
    have hp := ascPochhammer_pos i q hq
    have hq' := ascPochhammer_pos (n - i) q hq
    have hpl := Real.rpow_pos_of_pos hleft (-q - i)
    have hpr := Real.rpow_pos_of_pos hright (-q - (n - i))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_pos hp hpl).le)
      (mul_pos hq' hpr).le
  · refine ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), ?_⟩
    have hp := ascPochhammer_pos n q hq
    have hpl := Real.rpow_pos_of_pos hleft (-q)
    have hpr := Real.rpow_pos_of_pos hright (-q - n)
    simpa using mul_pos hpl (mul_pos hp hpr)


theorem negative_power_product_iteratedDeriv (n : ℕ) (q x : ℝ) (hx : 1 < x) :
    iteratedDeriv n (fun y : ℝ ↦ (y - 1) ^ (-q) * (y + 1) ^ (-q)) x =
      (-1 : ℝ) ^ n * derivativeMagnitude n q x := by
  have hl := shifted_negative_power_contDiffAt n q 1 x hx
  have hr := shifted_negative_power_contDiffAt n q (-1) x (by linarith)
  have hr' : ContDiffAt ℝ n (fun y : ℝ ↦ (y + 1) ^ (-q)) x := by
    simpa only [sub_neg_eq_add] using hr
  rw [iteratedDeriv_fun_mul hl hr', derivativeMagnitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hineq : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [shifted_negative_power_iteratedDeriv]
  have heq := shifted_negative_power_iteratedDeriv (n - i) q (-1) x
  simp only [sub_neg_eq_add] at heq
  rw [heq, Nat.cast_sub hineq]
  have hsign : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - i) = (-1 : ℝ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hineq]
  calc
    _ = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - i)) *
        ((n.choose i : ℝ) * ((ascPochhammer ℝ i).eval q * (x - 1) ^ (-q - i)) *
          ((ascPochhammer ℝ (n - i)).eval q * (x + 1) ^ (-q - (n - i)))) := by ring
    _ = _ := by rw [hsign]


theorem quadraticSquareRoot_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt quadraticSquareRoot (x * (x ^ 2 - 1) ^ (-(1 / 2 : ℝ))) x := by
  have hD : 0 < x ^ 2 - 1 := by nlinarith
  have hd := ((hasDerivAt_pow 2 x).sub_const 1).rpow_const
    (p := (1 / 2 : ℝ)) (Or.inl hD.ne')
  apply (hd.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
    rw [quadraticSquareRoot, Real.sqrt_eq_rpow])).congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  ring


theorem quadraticSquareRoot_deriv (x : ℝ) (hx : 1 < x) :
    deriv quadraticSquareRoot x = x * (x ^ 2 - 1) ^ (-(1 / 2 : ℝ)) :=
  (quadraticSquareRoot_hasDerivAt x hx).deriv


theorem first_coefficient_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun y : ℝ ↦ y * (y ^ 2 - 1) ^ (-(1 / 2 : ℝ)))
      (-(x ^ 2 - 1) ^ (-(3 / 2 : ℝ))) x := by
  have hD : 0 < x ^ 2 - 1 := by nlinarith
  have hp := ((hasDerivAt_pow 2 x).sub_const 1).rpow_const
    (p := (-(1 / 2 : ℝ))) (Or.inl hD.ne')
  apply ((hasDerivAt_id x).mul hp).congr_deriv
  have he : -(1 / 2 : ℝ) = -(3 / 2 : ℝ) + 1 := by norm_num
  rw [he, Real.rpow_add hD, Real.rpow_one]
  have he' : -(3 / 2 : ℝ) + 1 - 1 = -(3 / 2 : ℝ) := by ring
  rw [he']
  norm_num
  ring


theorem quadraticSquareRoot_second_deriv (x : ℝ) (hx : 1 < x) :
    deriv (deriv quadraticSquareRoot) x =
      -((x - 1) ^ (-(3 / 2 : ℝ)) * (x + 1) ^ (-(3 / 2 : ℝ))) := by
  have heq : deriv quadraticSquareRoot =ᶠ[𝓝 x]
      (fun y : ℝ ↦ y * (y ^ 2 - 1) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact quadraticSquareRoot_deriv y hy
  rw [heq.deriv_eq, (first_coefficient_hasDerivAt x hx).deriv]
  have hf : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hf, Real.mul_rpow (by linarith : 0 ≤ x - 1) (by linarith : 0 ≤ x + 1)]


theorem quadraticSquareRoot_iteratedDeriv_add_two (m : ℕ) (x : ℝ) (hx : 1 < x) :
    iteratedDeriv (m + 2) quadraticSquareRoot x =
      -((-1 : ℝ) ^ m * derivativeMagnitude m (3 / 2) x) := by
  have heq : deriv (deriv quadraticSquareRoot) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ -((y - 1) ^ (-(3 / 2 : ℝ)) * (y + 1) ^ (-(3 / 2 : ℝ)))) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact quadraticSquareRoot_second_deriv y hy
  rw [show m + 2 = (m + 1) + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
  rw [Filter.EventuallyEq.iteratedDeriv_eq m heq, iteratedDeriv_fun_neg,
    negative_power_product_iteratedDeriv m (3 / 2) x hx]

/-- Bài 20: trên `x > 1`, đạo hàm cấp lẻ dương, cấp chẵn âm. -/
theorem quadraticSquareRoot_derivative_sign (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 < x) :
    (Odd n → 0 < iteratedDeriv n quadraticSquareRoot x) ∧
      (Even n → iteratedDeriv n quadraticSquareRoot x < 0) := by
  by_cases h1 : n = 1
  · subst n
    rw [iteratedDeriv_one, quadraticSquareRoot_deriv x hx]
    constructor
    · intro _
      exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by nlinarith) _)
    · intro he
      norm_num at he
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
    rw [quadraticSquareRoot_iteratedDeriv_add_two m x hx]
    have hm := derivativeMagnitude_pos m (3 / 2 : ℝ) x (by norm_num) hx
    constructor
    · intro ho
      have hom : Odd m := by
        rcases ho with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      rw [hom.neg_one_pow]
      simpa using hm
    · intro he
      have hem : Even m := by
        rcases he with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      rw [hem.neg_one_pow]
      simpa using neg_neg_of_pos hm

end calculus.Chapter04.Section01HigherSquareRootExercise
