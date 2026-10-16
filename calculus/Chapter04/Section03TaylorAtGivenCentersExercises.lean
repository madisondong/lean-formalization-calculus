import calculus.Chapter04.Section03TaylorElementary
import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# §4.3 — Bài tập 26: Taylor tại ba tâm đã cho

Nguồn: `source/Ch4_hamsokhavi.tex` dòng 1332–1340, các phần (a), (b), (c). Tổng chạy từ 0 đến `n`; chọn `θ ∈ (0, 1)` sau `n` và `x`.
-/
set_option autoImplicit false
open Set Finset
open scoped BigOperators

namespace calculus.Chapter04.Section03TaylorAtGivenCentersExercises
open calculus.Chapter04.Section03TaylorElementary


theorem between_eq_affine_fraction {a x c : ℝ} (hx : x ≠ a)
    (hc : c ∈ uIoo a x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, c = a + θ * (x - a) := by
  have hca : c - a ∈ uIoo 0 (x - a) := by
    rcases lt_or_gt_of_ne hx with h | h
    · have hc' : c ∈ Ioo x a := by simpa only [uIoo_of_ge h.le] using hc
      rw [uIoo_of_ge (by linarith : x - a ≤ 0)]
      exact ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
    · have hc' : c ∈ Ioo a x := by simpa only [uIoo_of_le h.le] using hc
      rw [uIoo_of_le (by linarith : 0 ≤ x - a)]
      exact ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
  obtain ⟨θ, hθ, he⟩ := between_zero_eq_fraction (sub_ne_zero.mpr hx) hca
  exact ⟨θ, hθ, by linarith⟩


theorem global_taylor_affine_fraction {f : ℝ → ℝ} (n : ℕ) (a x : ℝ)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      f x = (∑ k ∈ range (n + 1), iteratedDeriv k f a / (k.factorial : ℝ) *
        (x - a) ^ k) +
        iteratedDeriv (n + 1) f (a + θ * (x - a)) * (x - a) ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by
  by_cases hx : x = a
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [sum_range_succ']
    simp
  · obtain ⟨c, hc, he⟩ := global_taylor_lagrange n hf (Ne.symm hx)
    obtain ⟨θ, hθ, hcθ⟩ := between_eq_affine_fraction hx hc
    exact ⟨θ, hθ, by simpa only [hcθ] using he⟩


theorem iteratedDeriv_exponential_three (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ Real.exp (3 * y - 1)) x =
      (3 : ℝ) ^ k * Real.exp (3 * x - 1) := by
  simpa only [sub_eq_add_neg] using
    calculus.Chapter04.Section01Higher.exponential_affine_iteratedDeriv k 3 (-1) x
      (by norm_num)


theorem iteratedDeriv_sine_phase (k : ℕ) (x : ℝ) :
    iteratedDeriv k Real.sin x = Real.sin (x + (k : ℝ) * Real.pi / 2) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by omega]
    have hp : x + ((2 * j : ℕ) : ℝ) * Real.pi / 2 = x + (j : ℝ) * Real.pi := by
      push_cast
      ring
    rw [hp, Real.sin_add_nat_mul_pi]
    simp
  · have hp : x + ((2 * j + 1 : ℕ) : ℝ) * Real.pi / 2 =
        (x + Real.pi / 2) + (j : ℝ) * Real.pi := by
      push_cast
      ring
    rw [hp, Real.sin_add_nat_mul_pi, Real.sin_add_pi_div_two]
    simp


theorem iteratedDeriv_sine_two (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ Real.sin (2 * y)) x =
      (2 : ℝ) ^ k * Real.sin (2 * x + (k : ℝ) * Real.pi / 2) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin 2]
  exact congrArg ((2 : ℝ) ^ k * ·) (iteratedDeriv_sine_phase k (2 * x))


theorem iteratedDeriv_shifted_cosh (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ Real.cosh (y - 5)) x =
      (1 / 2 : ℝ) * (Real.exp (x - 5) + (-1 : ℝ) ^ k * Real.exp (5 - x)) := by
  rw [iteratedDeriv_comp_sub_const]
  have he := calculus.Chapter04.Section01Higher.hyperbolic_cosine_iteratedDeriv k (x - 5)
  simpa only [neg_sub] using he

/-- Bài 4.3.26(a): khai triển Taylor của `exp(3x−1)` tại 2. -/
theorem exponential_taylor_at_two (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.exp (3 * x - 1) =
        (∑ k ∈ range (n + 1), (3 : ℝ) ^ k * Real.exp 5 /
          (k.factorial : ℝ) * (x - 2) ^ k) +
        (3 : ℝ) ^ (n + 1) * Real.exp (5 + 3 * θ * (x - 2)) *
          (x - 2) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hf : ContDiff ℝ (n + 1) (fun y : ℝ ↦ Real.exp (3 * y - 1)) :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).exp
  obtain ⟨θ, hθ, he⟩ := global_taylor_affine_fraction n 2 x hf
  refine ⟨θ, hθ, ?_⟩
  have hp : 3 * (2 + θ * (x - 2)) - 1 = 5 + 3 * θ * (x - 2) := by ring
  simpa only [iteratedDeriv_exponential_three, hp,
    show (3 : ℝ) * 2 - 1 = 5 by norm_num] using he

/-- Bài 4.3.26(b): khai triển Taylor của `sin(2x)` tại `π/2`. -/
theorem sine_taylor_at_pi_div_two (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.sin (2 * x) =
        (∑ k ∈ range (n + 1), (2 : ℝ) ^ k *
          Real.sin (Real.pi + (k : ℝ) * Real.pi / 2) / (k.factorial : ℝ) *
          (x - Real.pi / 2) ^ k) +
        (2 : ℝ) ^ (n + 1) * Real.sin (Real.pi + 2 * θ * (x - Real.pi / 2) +
          ((n + 1 : ℕ) : ℝ) * Real.pi / 2) * (x - Real.pi / 2) ^ (n + 1) /
            ((n + 1).factorial : ℝ) := by
  have hf : ContDiff ℝ (n + 1) (fun y : ℝ ↦ Real.sin (2 * y)) :=
    (contDiff_const.mul contDiff_id).sin
  obtain ⟨θ, hθ, he⟩ := global_taylor_affine_fraction n (Real.pi / 2) x hf
  refine ⟨θ, hθ, ?_⟩
  have hp : 2 * (Real.pi / 2 + θ * (x - Real.pi / 2)) =
      Real.pi + 2 * θ * (x - Real.pi / 2) := by ring
  simpa only [iteratedDeriv_sine_two, hp,
    show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] using he

/-- Bài 4.3.26(c): khai triển Taylor của `cosh(x−5)` tại 1. -/
theorem shifted_cosh_taylor_at_one (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.cosh (x - 5) =
        (∑ k ∈ range (n + 1), ((1 / 2 : ℝ) *
          (Real.exp (-4) + (-1 : ℝ) ^ k * Real.exp 4)) /
            (k.factorial : ℝ) * (x - 1) ^ k) +
        ((1 / 2 : ℝ) * (Real.exp (-4 + θ * (x - 1)) +
          (-1 : ℝ) ^ (n + 1) * Real.exp (4 - θ * (x - 1)))) *
            (x - 1) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hf : ContDiff ℝ (n + 1) (fun y : ℝ ↦ Real.cosh (y - 5)) :=
    (contDiff_id.sub contDiff_const).cosh
  obtain ⟨θ, hθ, he⟩ := global_taylor_affine_fraction n 1 x hf
  refine ⟨θ, hθ, ?_⟩
  have hp : 1 + θ * (x - 1) - 5 = -4 + θ * (x - 1) := by ring
  have hq : 5 - (1 + θ * (x - 1)) = 4 - θ * (x - 1) := by ring
  simpa only [iteratedDeriv_shifted_cosh, hp, hq,
    show (1 : ℝ) - 5 = -4 by norm_num, show (5 : ℝ) - 1 = 4 by norm_num] using he

end calculus.Chapter04.Section03TaylorAtGivenCentersExercises
