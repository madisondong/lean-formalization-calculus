import calculus.Chapter04.Section03TaylorElementary
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Các công thức Maclaurin của nghịch đảo và logarit

Nguồn: `C04-S03-display-L1287`, `source/Ch4_hamsokhavi.tex`, dòng 1290–1292; điều kiện θ tại dòng 1294. Xét `x > −1` cho `1/(1+x)` và `ln(1+x)`, `x < 1` cho `1/(1−x)`; toàn đoạn Taylor phải tránh cực.
-/
namespace calculus.Chapter04.Section03ReciprocalLogMaclaurin
open Set Finset
open scoped BigOperators


noncomputable def plusReciprocal (x : ℝ) : ℝ := 1 / (1 + x)


noncomputable def minusReciprocal (x : ℝ) : ℝ := 1 / (1 - x)


noncomputable def logOneAdd (x : ℝ) : ℝ := Real.log (1 + x)


theorem iteratedDeriv_one_div (n : ℕ) (y : ℝ) (_hy : y ≠ 0) :
    iteratedDeriv n (fun t : ℝ ↦ 1 / t) y =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / y ^ (n + 1) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ (mem_univ y)
  rw [iteratedDerivWithin_univ] at h
  have he : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  dsimp only at h
  rw [he, zpow_neg, zpow_natCast] at h
  simpa only [div_eq_mul_inv] using h


theorem iteratedDeriv_plusReciprocal (n : ℕ) (x : ℝ) (hx : 1 + x ≠ 0) :
    iteratedDeriv n plusReciprocal x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / (1 + x) ^ (n + 1) := by
  change iteratedDeriv n (fun y : ℝ ↦ (fun t : ℝ ↦ 1 / t) (1 + y)) x = _
  rw [iteratedDeriv_comp_const_add]
  exact iteratedDeriv_one_div n (1 + x) hx


theorem iteratedDeriv_minusReciprocal (n : ℕ) (x : ℝ) (hx : 1 - x ≠ 0) :
    iteratedDeriv n minusReciprocal x = (n.factorial : ℝ) / (1 - x) ^ (n + 1) := by
  change iteratedDeriv n (fun y : ℝ ↦ (fun t : ℝ ↦ 1 / t) (1 - y)) x = _
  rw [iteratedDeriv_comp_const_sub]
  change (-1 : ℝ) ^ n * iteratedDeriv n (fun t : ℝ ↦ 1 / t) (1 - x) = _
  rw [iteratedDeriv_one_div n (1 - x) hx]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (n.factorial : ℝ) / (1 - x) ^ (n + 1)) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * (n.factorial : ℝ) / (1 - x) ^ (n + 1) := by ring
    _ = _ := by rw [hs, one_mul]


theorem iteratedDeriv_logOneAdd_succ (n : ℕ) (x : ℝ) (hx : 0 < 1 + x) :
    iteratedDeriv (n + 1) logOneAdd x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / (1 + x) ^ (n + 1) := by
  change iteratedDeriv (n + 1) (fun y : ℝ ↦ Real.log (1 + y)) x = _
  rw [iteratedDeriv_comp_const_add, iteratedDeriv_succ', Real.deriv_log']
  simpa only [one_div] using iteratedDeriv_one_div n (1 + x) hx.ne'


theorem plusReciprocal_contDiffAt (m : ℕ) (y : ℝ) (hy : 1 + y ≠ 0) :
    ContDiffAt ℝ m plusReciprocal y := by
  have h : ContDiffAt ℝ m (fun z : ℝ ↦ 1 + z) y := contDiffAt_const.add contDiffAt_id
  change ContDiffAt ℝ m (fun z : ℝ ↦ 1 / (1 + z)) y
  simpa only [one_div, Pi.inv_def] using h.inv hy


theorem minusReciprocal_contDiffAt (m : ℕ) (y : ℝ) (hy : 1 - y ≠ 0) :
    ContDiffAt ℝ m minusReciprocal y := by
  have h : ContDiffAt ℝ m (fun z : ℝ ↦ 1 - z) y := contDiffAt_const.sub contDiffAt_id
  change ContDiffAt ℝ m (fun z : ℝ ↦ 1 / (1 - z)) y
  simpa only [one_div, Pi.inv_def] using h.inv hy


theorem logOneAdd_contDiffAt (m : ℕ) (y : ℝ) (hy : 0 < 1 + y) :
    ContDiffAt ℝ m logOneAdd y := by
  have h : ContDiffAt ℝ m (fun z : ℝ ↦ 1 + z) y := contDiffAt_const.add contDiffAt_id
  exact h.log hy.ne'


theorem one_add_pos_on_segment {x : ℝ} (hx : -1 < x) {y : ℝ} (hy : y ∈ uIcc 0 x) :
    0 < 1 + y := by
  rcases le_total (0 : ℝ) x with hx0 | hx0
  · rw [uIcc_of_le hx0] at hy
    linarith [hy.1]
  · rw [uIcc_of_ge hx0] at hy
    linarith [hy.1]


theorem one_sub_pos_on_segment {x : ℝ} (hx : x < 1) {y : ℝ} (hy : y ∈ uIcc 0 x) :
    0 < 1 - y := by
  rcases le_total (0 : ℝ) x with hx0 | hx0
  · rw [uIcc_of_le hx0] at hy
    linarith [hy.2]
  · rw [uIcc_of_ge hx0] at hy
    linarith [hy.2]


theorem segment_taylor_lagrange {f : ℝ → ℝ} (n : ℕ) {x₀ x : ℝ}
    (hne : x₀ ≠ x) (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x))
    (hcenter : ContDiffAt ℝ (n + 1) f x₀) :
    ∃ c ∈ uIoo x₀ x,
      f x = (∑ k ∈ range (n + 1), iteratedDeriv k f x₀ / (k.factorial : ℝ) *
        (x - x₀) ^ k) +
          iteratedDeriv (n + 1) f c * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf
  have hp : taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∑ k ∈ range (n + 1), iteratedDeriv k f x₀ / (k.factorial : ℝ) * (x - x₀) ^ k := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n + 1 := (Nat.le_of_lt_succ (mem_range.mp hk)).trans n.le_succ
    have hd : ContDiffAt ℝ k f x₀ := hcenter.of_le (by exact_mod_cast hkn)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) hd left_mem_uIcc]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hp] at he
  exact ⟨c, hc, by linarith⟩


theorem plusReciprocal_derivative_coefficient (k : ℕ) :
    iteratedDeriv k plusReciprocal 0 / (k.factorial : ℝ) = (-1 : ℝ) ^ k := by
  rw [iteratedDeriv_plusReciprocal k 0 (by norm_num)]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [add_zero, one_pow, div_one]
  field_simp [hk]


theorem minusReciprocal_derivative_coefficient (k : ℕ) :
    iteratedDeriv k minusReciprocal 0 / (k.factorial : ℝ) = 1 := by
  rw [iteratedDeriv_minusReciprocal k 0 (by norm_num)]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [sub_zero, one_pow, div_one]
  exact div_self hk


theorem logOneAdd_derivative_coefficient (k : ℕ) :
    iteratedDeriv (k + 1) logOneAdd 0 / ((k + 1).factorial : ℝ) =
      (-1 : ℝ) ^ k / (k + 1 : ℕ) := by
  rw [iteratedDeriv_logOneAdd_succ k 0 (by norm_num), Nat.factorial_succ]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  simp only [add_zero, one_pow, div_one, Nat.cast_mul]
  field_simp [hk, hk1]

/-- Công thức dòng 1290: khai triển của `1/(1+x)` với `x > −1`. -/
theorem plusReciprocal_maclaurin_on_source_component (n : ℕ) (_hn : 1 ≤ n)
    (x : ℝ) (hx : -1 < x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      1 / (1 + x) = (∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * x ^ k) +
        (-1 : ℝ) ^ (n + 1) * (1 / (1 + θ * x) ^ (n + 2)) * x ^ (n + 1) := by
  by_cases hx0 : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [sum_range_succ']
    simp
  · have hf : ContDiffOn ℝ (n + 1) plusReciprocal (uIcc 0 x) := fun y hy ↦
      (plusReciprocal_contDiffAt (n + 1) y (one_add_pos_on_segment hx hy).ne').contDiffWithinAt
    obtain ⟨c, hc, he⟩ := segment_taylor_lagrange (x₀ := 0) (x := x) n (Ne.symm hx0) hf
      (plusReciprocal_contDiffAt (n + 1) 0 (by norm_num))
    obtain ⟨θ, hθ, hcθ⟩ := Section03TaylorElementary.between_zero_eq_fraction hx0 hc
    have hcpos : 0 < 1 + c := one_add_pos_on_segment hx (Ioo_subset_Icc_self hc)
    rw [iteratedDeriv_plusReciprocal (n + 1) c hcpos.ne'] at he
    simp_rw [plusReciprocal_derivative_coefficient] at he
    have hfac : ((n + 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
    have hden : 1 + θ * x ≠ 0 := by rw [← hcθ]; exact hcpos.ne'
    simp only [plusReciprocal, sub_zero, hcθ] at he
    have hr :
        ((-1 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ) /
          (1 + θ * x) ^ (n + 2)) * x ^ (n + 1) / ((n + 1).factorial : ℝ) =
        (-1 : ℝ) ^ (n + 1) * (1 / (1 + θ * x) ^ (n + 2)) * x ^ (n + 1) := by
      field_simp [hfac, hden]
    rw [hr] at he
    exact ⟨θ, hθ, he⟩

/-- Công thức dòng 1291, với `x < 1` để đoạn Taylor tránh cực. -/
theorem minusReciprocal_maclaurin_on_source_component (n : ℕ) (_hn : 1 ≤ n)
    (x : ℝ) (hx : x < 1) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      1 / (1 - x) = (∑ k ∈ range (n + 1), x ^ k) +
        (1 / (1 - θ * x) ^ (n + 2)) * x ^ (n + 1) := by
  by_cases hx0 : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [sum_range_succ']
    simp
  · have hf : ContDiffOn ℝ (n + 1) minusReciprocal (uIcc 0 x) := fun y hy ↦
      (minusReciprocal_contDiffAt (n + 1) y (one_sub_pos_on_segment hx hy).ne').contDiffWithinAt
    obtain ⟨c, hc, he⟩ := segment_taylor_lagrange (x₀ := 0) (x := x) n (Ne.symm hx0) hf
      (minusReciprocal_contDiffAt (n + 1) 0 (by norm_num))
    obtain ⟨θ, hθ, hcθ⟩ := Section03TaylorElementary.between_zero_eq_fraction hx0 hc
    have hcpos : 0 < 1 - c := one_sub_pos_on_segment hx (Ioo_subset_Icc_self hc)
    rw [iteratedDeriv_minusReciprocal (n + 1) c hcpos.ne'] at he
    simp_rw [minusReciprocal_derivative_coefficient, one_mul] at he
    have hfac : ((n + 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
    have hden : 1 - θ * x ≠ 0 := by rw [← hcθ]; exact hcpos.ne'
    simp only [minusReciprocal, sub_zero, hcθ] at he
    have hr :
        (((n + 1).factorial : ℝ) / (1 - θ * x) ^ (n + 2)) *
          x ^ (n + 1) / ((n + 1).factorial : ℝ) =
        (1 / (1 - θ * x) ^ (n + 2)) * x ^ (n + 1) := by
      field_simp [hfac, hden]
    rw [hr] at he
    exact ⟨θ, hθ, he⟩

/-- Công thức dòng 1292: tổng chứa các lũy thừa từ 1 đến `n`. -/
theorem logOneAdd_maclaurin_on_source_domain (n : ℕ) (_hn : 1 ≤ n)
    (x : ℝ) (hx : -1 < x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.log (1 + x) = (∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1 : ℕ)) +
        (-1 : ℝ) ^ n * x ^ (n + 1) / ((1 + θ * x) ^ (n + 1) * (n + 1 : ℕ)) := by
  by_cases hx0 : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp
  · have hf : ContDiffOn ℝ (n + 1) logOneAdd (uIcc 0 x) := fun y hy ↦
      (logOneAdd_contDiffAt (n + 1) y (one_add_pos_on_segment hx hy)).contDiffWithinAt
    obtain ⟨c, hc, he⟩ := segment_taylor_lagrange (x₀ := 0) (x := x) n (Ne.symm hx0) hf
      (logOneAdd_contDiffAt (n + 1) 0 (by norm_num))
    obtain ⟨θ, hθ, hcθ⟩ := Section03TaylorElementary.between_zero_eq_fraction hx0 hc
    have hcpos : 0 < 1 + c := one_add_pos_on_segment hx (Ioo_subset_Icc_self hc)
    rw [iteratedDeriv_logOneAdd_succ n c hcpos] at he
    rw [sum_range_succ'] at he
    simp_rw [logOneAdd_derivative_coefficient] at he
    simp only [iteratedDeriv_zero, logOneAdd, add_zero, Real.log_one, zero_div,
      zero_mul, sub_zero, hcθ, Nat.factorial_succ, Nat.cast_mul] at he
    have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hden : 1 + θ * x ≠ 0 := by rw [← hcθ]; exact hcpos.ne'
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hp : (∑ k ∈ range n, ((-1 : ℝ) ^ k / (k + 1 : ℕ)) * x ^ (k + 1)) =
        ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1 : ℕ) := by
      apply sum_congr rfl
      intro k _
      ring
    have hr : (((-1 : ℝ) ^ n * (n.factorial : ℝ) / (1 + θ * x) ^ (n + 1)) *
        x ^ (n + 1)) / (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ)) =
        (-1 : ℝ) ^ n * x ^ (n + 1) /
          ((1 + θ * x) ^ (n + 1) * (n + 1 : ℕ)) := by
      field_simp [hfac, hden, hn1]
    rw [hp, hr] at he
    exact ⟨θ, hθ, he⟩


theorem crossing_pole_first_degree_counterexample :
    ¬∃ θ ∈ Ioo (0 : ℝ) 1, (-1 : ℝ) = 3 + 4 / (1 - 2 * θ) ^ 3 := by
  rintro ⟨θ, hθ, he⟩
  let d : ℝ := 1 - 2 * θ
  change (-1 : ℝ) = 3 + 4 / d ^ 3 at he
  have hd : -1 < d := by dsimp [d]; linarith [hθ.2]
  by_cases hd0 : d = 0
  · rw [hd0] at he
    norm_num at he
  · have hq : 0 < d ^ 2 - d + 1 := by nlinarith [sq_nonneg (d - 1 / 2)]
    have hp : 0 < (d + 1) * (d ^ 2 - d + 1) := mul_pos (by linarith) hq
    have hquot : 4 / d ^ 3 = -4 := by linarith
    have hmul := (div_eq_iff (pow_ne_zero 3 hd0)).mp hquot
    nlinarith

end calculus.Chapter04.Section03ReciprocalLogMaclaurin
