import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bài 24(a,b): phân tích phân thức và đạo hàm cấp n

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 665–666.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherPartialFractions
open Filter Set calculus.Chapter04.Section01Higher
open scoped ContDiff Topology


theorem shifted_reciprocal_iteratedDeriv (n : ℕ) (c x : ℝ) (hx : x ≠ c) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (y - c)) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x - c) ^ (n + 1) := by
  simpa only [one_mul, one_pow, sub_eq_add_neg] using
    reciprocal_affine_iteratedDeriv n 1 (-c) x (by norm_num) (by simpa using hx)


theorem shifted_reciprocal_contDiffAt (n : ℕ) (c x : ℝ) (hx : x ≠ c) :
    ContDiffAt ℝ n (fun y : ℝ ↦ 1 / (y - c)) x := by
  apply ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hx)).congr_of_eventuallyEq
  exact Eventually.of_forall fun y ↦ by simp [one_div]


theorem reciprocal_square_iteratedDeriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / y ^ 2) x =
      (-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) / x ^ (n + 2) := by
  have hnear : (fun y : ℝ ↦ 1 / y ^ 2) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ -deriv (fun z : ℝ ↦ 1 / z) y) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    have h := reciprocal_iteratedDeriv 1 y hy
    rw [iteratedDeriv_one] at h
    rw [h]
    norm_num
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hnear, iteratedDeriv_fun_neg,
    ← iteratedDeriv_succ', reciprocal_iteratedDeriv (n + 1) x hx]
  rw [pow_succ]
  simp only [Nat.add_assoc]
  ring


theorem quadratic_reciprocal_nonzero_parameter (n : ℕ) (a x : ℝ) (ha : a ≠ 0)
    (hxa : x ≠ a) (hxna : x ≠ -a) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (y ^ 2 - a ^ 2)) x =
      (1 / (2 * a)) *
        ((-1 : ℝ) ^ n * (n.factorial : ℝ) / (x - a) ^ (n + 1) -
          (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + a) ^ (n + 1)) := by
  have hnear : (fun y : ℝ ↦ 1 / (y ^ 2 - a ^ 2)) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ (1 / (2 * a)) * (1 / (y - a) - 1 / (y + a))) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hxa,
      isClosed_singleton.isOpen_compl.mem_nhds hxna] with y hy hyn
    have hy1 : y - a ≠ 0 := sub_ne_zero.mpr hy
    have hyn_ne : y ≠ -a := by simpa using hyn
    have hy2 : y + a ≠ 0 := by intro h; apply hyn_ne; linarith
    rw [show y ^ 2 - a ^ 2 = (y - a) * (y + a) by ring]
    field_simp [ha, hy1, hy2]
    ring
  have hA := shifted_reciprocal_contDiffAt n a x hxa
  have hB : ContDiffAt ℝ n (fun y : ℝ ↦ 1 / (y + a)) x := by
    simpa only [sub_neg_eq_add] using shifted_reciprocal_contDiffAt n (-a) x hxna
  have hdB : iteratedDeriv n (fun y : ℝ ↦ 1 / (y + a)) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + a) ^ (n + 1) := by
    simpa only [sub_neg_eq_add] using shifted_reciprocal_iteratedDeriv n (-a) x hxna
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hnear, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub hA hB, shifted_reciprocal_iteratedDeriv n a x hxa, hdB]

/-- Bài 24(a): công thức đạo hàm trên miền `x² ≠ a²`, với mọi `a`. -/
theorem quadratic_reciprocal_iteratedDeriv (n : ℕ) (_hn : 1 ≤ n) (a x : ℝ)
    (hx : x ^ 2 - a ^ 2 ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (y ^ 2 - a ^ 2)) x =
      if a = 0 then (-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) / x ^ (n + 2)
      else (1 / (2 * a)) *
        ((-1 : ℝ) ^ n * (n.factorial : ℝ) / (x - a) ^ (n + 1) -
          (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + a) ^ (n + 1)) := by
  by_cases ha : a = 0
  · subst a
    have hx0 : x ≠ 0 := by intro he; subst x; simp at hx
    simpa using reciprocal_square_iteratedDeriv n x hx0
  · rw [if_neg ha]
    have hxa : x ≠ a := by intro he; subst x; simp at hx
    have hxna : x ≠ -a := by intro he; subst x; simp at hx
    exact quadratic_reciprocal_nonzero_parameter n a x ha hxa hxna

/-- Bài 24(b): đạo hàm trên miền đã loại các cực 1, 2, 3. -/
theorem cubic_reciprocal_iteratedDeriv (n : ℕ) (_hn : 1 ≤ n) (x : ℝ)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / ((y - 1) * (y - 2) * (y - 3))) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (1 / (2 * (x - 1) ^ (n + 1)) - 1 / (x - 2) ^ (n + 1) +
          1 / (2 * (x - 3) ^ (n + 1))) := by
  have hnear : (fun y : ℝ ↦ 1 / ((y - 1) * (y - 2) * (y - 3))) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ (1 / 2 : ℝ) * (1 / (y - 1)) - 1 / (y - 2) +
        (1 / 2 : ℝ) * (1 / (y - 3))) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx1,
      isClosed_singleton.isOpen_compl.mem_nhds hx2,
      isClosed_singleton.isOpen_compl.mem_nhds hx3] with y hy1 hy2 hy3
    field_simp [sub_ne_zero.mpr hy1, sub_ne_zero.mpr hy2, sub_ne_zero.mpr hy3]
    ring
  have h1 := shifted_reciprocal_contDiffAt n 1 x hx1
  have h2 := shifted_reciprocal_contDiffAt n 2 x hx2
  have h3 := shifted_reciprocal_contDiffAt n 3 x hx3
  have hs1 : ContDiffAt ℝ n (fun y : ℝ ↦ (1 / 2 : ℝ) * (1 / (y - 1))) x :=
    contDiffAt_const.mul h1
  have hs3 : ContDiffAt ℝ n (fun y : ℝ ↦ (1 / 2 : ℝ) * (1 / (y - 3))) x :=
    contDiffAt_const.mul h3
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hnear,
    iteratedDeriv_fun_add (hs1.sub h2) hs3,
    iteratedDeriv_fun_sub hs1 h2,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    shifted_reciprocal_iteratedDeriv n 1 x hx1,
    shifted_reciprocal_iteratedDeriv n 2 x hx2,
    shifted_reciprocal_iteratedDeriv n 3 x hx3]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end calculus.Chapter04.Section01HigherPartialFractions
