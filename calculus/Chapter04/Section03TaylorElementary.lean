import calculus.Chapter02.Section06Euler
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Ví dụ Taylor sơ cấp trong §4.3

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1269–1322.
-/
namespace calculus.Chapter04.Section03TaylorElementary
open Set Finset
open scoped BigOperators


theorem global_taylor_lagrange {f : ℝ → ℝ} (n : ℕ) {x₀ x : ℝ}
    (hf : ContDiff ℝ (n + 1) f) (hne : x₀ ≠ x) :
    ∃ c ∈ uIoo x₀ x,
      f x = (∑ k ∈ range (n + 1), iteratedDeriv k f x₀ / (k.factorial : ℝ) *
        (x - x₀) ^ k) +
          iteratedDeriv (n + 1) f c * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf.contDiffOn
  have hp : taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∑ k ∈ range (n + 1), iteratedDeriv k f x₀ / (k.factorial : ℝ) * (x - x₀) ^ k := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n + 1 := (Nat.le_of_lt_succ (mem_range.mp hk)).trans n.le_succ
    have hd : ContDiffAt ℝ k f x₀ := hf.contDiffAt.of_le (by exact_mod_cast hkn)
    have hval : iteratedDerivWithin k f (uIcc x₀ x) x₀ = iteratedDeriv k f x₀ := by
      unfold iteratedDerivWithin iteratedDeriv
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_uIcc hne) hd left_mem_uIcc]
    rw [hval]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hp] at he
  exact ⟨c, hc, by linarith⟩


theorem between_zero_eq_fraction {x c : ℝ} (hx : x ≠ 0) (hc : c ∈ uIoo 0 x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, c = θ * x := by
  refine ⟨c / x, ?_, by field_simp [hx]⟩
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hc' : c ∈ Ioo x 0 := by simpa only [uIoo_of_ge hx.le] using hc
    exact ⟨div_pos_of_neg_of_neg hc'.2 hx,
      (div_lt_iff_of_neg hx).mpr (by simpa only [one_mul] using hc'.1)⟩
  · have hc' : c ∈ Ioo 0 x := by simpa only [uIoo_of_le hx.le] using hc
    exact ⟨div_pos hc'.1 hx, (div_lt_one hx).mpr hc'.2⟩


theorem iteratedDeriv_exponential (n : ℕ) (x : ℝ) : iteratedDeriv n Real.exp x = Real.exp x := by
  simpa only [one_mul, one_pow] using congrFun (iteratedDeriv_exp_const_mul n 1) x

/-- Ví dụ 4.3.14: khai triển Maclaurin của exp; chọn `θ` sau `n` và `x`. -/
theorem exponential_maclaurin (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.exp x = (∑ k ∈ range (n + 1), x ^ k / (k.factorial : ℝ)) +
        Real.exp (θ * x) * x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hx : x = 0
  · subst x
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [sum_range_succ']
    simp
  · obtain ⟨c, hc, he⟩ := global_taylor_lagrange n
      (Real.contDiff_exp : ContDiff ℝ (n + 1) Real.exp) (Ne.symm hx)
    obtain ⟨θ, hθ, hcθ⟩ := between_zero_eq_fraction hx hc
    refine ⟨θ, hθ, ?_⟩
    simpa only [iteratedDeriv_exponential, Real.exp_zero, zero_mul, sub_zero,
      one_div_mul_eq_div, hcθ] using he


theorem exponential_partial_sum_eight :
    (∑ k ∈ range 9, 1 / (k.factorial : ℝ)) = (109601 / 40320 : ℝ) := by
  norm_num [sum_range_succ, Nat.factorial]

/-- Ví dụ 4.3.16: đa thức Maclaurin bậc 8 tại 1 xấp xỉ e với sai số nhỏ hơn `10⁻⁵`. -/
theorem exponential_one_approximation :
    |Real.exp 1 - 109601 / 40320| < (1 / 100000 : ℝ) := by
  obtain ⟨θ, hθ, he⟩ := exponential_maclaurin 8 (by decide) 1
  simp only [Nat.reduceAdd, one_pow, mul_one, exponential_partial_sum_eight] at he
  have hp : 0 < Real.exp θ := Real.exp_pos θ
  have hlt : Real.exp θ < 3 := (Real.exp_strictMono hθ.2).trans Real.exp_one_lt_three
  have hr : Real.exp 1 - 109601 / 40320 = Real.exp θ / (Nat.factorial 9 : ℝ) := by
    linarith [he]
  rw [hr, abs_of_pos (div_pos hp (by positivity))]
  norm_num [Nat.factorial] at ⊢
  nlinarith


theorem exponential_one_printed_decimal :
    |Real.exp 1 - (271828 / 100000 : ℝ)| < (1 / 100000 : ℝ) := by
  apply abs_lt.mpr
  constructor <;> linarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9]

/-- Ví dụ 4.3.18: e là số vô tỉ. -/
theorem exponential_one_irrational : Irrational (Real.exp 1) :=
  calculus.Chapter02.Section06Euler.irrational_exp_one

/-- Ví dụ 4.3.19: `cos x ≥ 1 − x²/2` trên ℝ. -/
theorem cosine_lower_bound (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

/-- Ví dụ 4.3.20: `exp π > π^e`, với lũy thừa thực có cơ số π dương. -/
theorem exponential_pi_gt_pi_power_e :
    Real.pi ^ (Real.exp 1) < (Real.exp 1) ^ Real.pi := by
  have hepos := Real.exp_pos 1
  have hpie : Real.exp 1 < Real.pi := Real.exp_one_lt_three.trans Real.pi_gt_three
  have hgap : 0 < Real.pi / Real.exp 1 - 1 := by
    exact sub_pos.mpr ((one_lt_div hepos).mpr hpie)
  have hquot : Real.pi / Real.exp 1 < Real.exp (Real.pi / Real.exp 1 - 1) := by
    simpa only [sub_add_cancel] using Real.add_one_lt_exp hgap.ne'
  have hlog := Real.log_lt_log (div_pos Real.pi_pos hepos) hquot
  rw [Real.log_div Real.pi_pos.ne' hepos.ne', Real.log_exp, Real.log_exp] at hlog
  have hmul := mul_lt_mul_of_pos_right hlog hepos
  have htarget : Real.log Real.pi * Real.exp 1 < Real.pi := by
    field_simp [hepos.ne'] at hmul
    nlinarith
  rw [Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos hepos, Real.log_exp, one_mul]
  exact Real.exp_strictMono htarget


theorem sine_taylor_polynomial_three (x : ℝ) :
    (∑ k ∈ range 4, iteratedDeriv k Real.sin 0 / (k.factorial : ℝ) * x ^ k) =
      x - x ^ 3 / 6 := by
  have h2 : iteratedDeriv 2 Real.sin = -Real.sin := by
    simpa using Real.iteratedDeriv_even_sin 1
  have h3 : iteratedDeriv 3 Real.sin = -Real.cos := by
    simp
  norm_num [sum_range_succ, h2, h3, iteratedDeriv_zero, iteratedDeriv_one,
    Real.deriv_sin, Pi.neg_apply, Real.sin_zero, Real.cos_zero, Nat.factorial]
  ring

/-- Ví dụ 4.3.17: cận sai số của đa thức Maclaurin bậc ba của sin. -/
theorem sine_taylor_error_three (x : ℝ) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 / 24 := by
  by_cases hx : x = 0
  · subst x; norm_num
  · obtain ⟨c, _, he⟩ := global_taylor_lagrange 3
      (Real.contDiff_sin : ContDiff ℝ 4 Real.sin) (Ne.symm hx)
    have h4 : iteratedDeriv 4 Real.sin = Real.sin := by
      simpa using Real.iteratedDeriv_even_sin 2
    simp only [Nat.reduceAdd, sub_zero, h4] at he
    rw [sine_taylor_polynomial_three] at he
    have he' : Real.sin x - (x - x ^ 3 / 6) = Real.sin c * x ^ 4 / 24 := by
      norm_num [Nat.factorial] at he
      linarith
    rw [he', abs_div, abs_mul, abs_pow]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    have hm : |Real.sin c| * |x| ^ 4 ≤ |x| ^ 4 := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one c) (pow_nonneg (abs_nonneg x) 4))
    exact div_le_div_of_nonneg_right hm (by norm_num)


theorem sine_taylor_error_three_on_interval {x : ℝ} (hx : x ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ (Real.pi / 2) ^ 4 / 24 ∧
      (Real.pi / 2) ^ 4 / 24 ≤ (25367 / 100000 : ℝ) := by
  have hax : |x| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  constructor
  · exact (sine_taylor_error_three x).trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg x) hax 4) (by norm_num))
  · have hpi : Real.pi / 2 ≤ (3141593 / 1000000 : ℝ) / 2 := by
      linarith [Real.pi_lt_d6]
    have hp := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi / 2) hpi 4)
      (by norm_num : (0 : ℝ) ≤ 24)
    exact hp.trans (by norm_num)

/-- Bài 31: đa thức Maclaurin bậc năm của cos có hệ số bậc năm bằng 0. -/
theorem cosine_taylor_polynomial_five (x : ℝ) :
    (∑ k ∈ range 6, iteratedDeriv k Real.cos 0 / (k.factorial : ℝ) * x ^ k) =
      1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h2 : iteratedDeriv 2 Real.cos = -Real.cos := by
    simp
  have h3 : iteratedDeriv 3 Real.cos = Real.sin := by
    simpa using Real.iteratedDeriv_odd_cos 1
  have h4 : iteratedDeriv 4 Real.cos = Real.cos := by
    simp
  have h5 : iteratedDeriv 5 Real.cos = -Real.sin := by
    funext y
    change iteratedDeriv 5 Real.cos y = -Real.sin y
    have h := congrFun (Real.iteratedDeriv_odd_cos 2) y
    change iteratedDeriv 5 Real.cos y = (-1 : ℝ) ^ 3 * Real.sin y at h
    norm_num only [neg_one_mul] at h
    exact h
  norm_num [sum_range_succ, h2, h3, h4, h5, iteratedDeriv_zero, iteratedDeriv_one,
    Real.deriv_cos, Pi.neg_apply, Real.sin_zero, Real.cos_zero, Nat.factorial]
  ring

/-- Bài 31: cận sai số của đa thức Maclaurin bậc năm của cos trên đoạn đã cho. -/
theorem cosine_taylor_error_five_on_interval {x : ℝ}
    (hx : x ∈ Icc (-Real.pi / 2) (Real.pi / 2)) :
    |(1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x| ≤ (Real.pi / 2) ^ 6 / 720 := by
  by_cases hz : x = 0
  · subst x
    norm_num
    positivity
  · obtain ⟨c, _, he⟩ := global_taylor_lagrange 5
      (Real.contDiff_cos : ContDiff ℝ 6 Real.cos) (Ne.symm hz)
    have h6 : iteratedDeriv 6 Real.cos = -Real.cos := by
      simp
    simp only [Nat.reduceAdd, sub_zero, h6, Pi.neg_apply] at he
    rw [cosine_taylor_polynomial_five] at he
    have he' : (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x = Real.cos c * x ^ 6 / 720 := by
      norm_num [Nat.factorial] at he
      linarith
    rw [he', abs_div, abs_mul, abs_pow]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 720)]
    have hax : |x| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hm : |Real.cos c| * |x| ^ 6 ≤ |x| ^ 6 := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one c) (pow_nonneg (abs_nonneg x) 6))
    exact div_le_div_of_nonneg_right
      (hm.trans (pow_le_pow_left₀ (abs_nonneg x) hax 6)) (by norm_num)

end calculus.Chapter04.Section03TaylorElementary
