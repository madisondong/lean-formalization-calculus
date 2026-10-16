import calculus.Chapter04.Section03
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Bài tập 4.3.1–6

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1093–1119. Bài 4–6 dùng quy ước đoạn không suy biến `a < b` của Định nghĩa 2.1.6, Chương 2, dòng 119–133.
-/
namespace calculus.Chapter04.Section03ExercisesBasic
open Set Filter calculus.Chapter04.Section03
open scoped Topology


theorem derivatives_eq_at_contact {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : f x = g x) (hle : ∀ y, f y ≤ g y) : deriv f x = deriv g x := by
  have hm : IsLocalMax (fun y ↦ f y - g y) x := by
    apply Filter.Eventually.of_forall
    intro y
    simp only [he, sub_self]
    exact sub_nonpos.mpr (hle y)
  have hz := hm.hasDerivAt_eq_zero (hf.hasDerivAt.fun_sub hg.hasDerivAt)
  exact sub_eq_zero.mp hz

/-- Bài 2(a): cận trên `√(1+x) ≤ 1+x/2` khi `x > 0`. -/
theorem sqrt_one_add_le {x : ℝ} (hx : 0 < x) : Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hd (u : ℝ) (hu : u ∈ Ioo 0 x) :
      HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 + t)) (1 / (2 * Real.sqrt (1 + u))) u := by
    simpa only [zero_add, mul_one, id_eq, Function.comp_def] using
      (Real.hasDerivAt_sqrt (by linarith [hu.1] : (1 + u : ℝ) ≠ 0)).comp u
        ((hasDerivAt_const u (1 : ℝ)).fun_add (hasDerivAt_id u))
  obtain ⟨c, hcm, he⟩ := lagrange_increment (f := fun t : ℝ ↦ Real.sqrt (1 + t)) hx
    ((continuous_const.add continuous_id).sqrt.continuousOn)
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt)
  rw [(hd c hcm).deriv, add_zero, Real.sqrt_one] at he
  have hs : 1 ≤ Real.sqrt (1 + c) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + c by linarith [hcm.1])
  have hden : 0 < 2 * Real.sqrt (1 + c) := by linarith
  have hle : 1 / (2 * Real.sqrt (1 + c)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have := mul_le_mul_of_nonneg_right hle hx.le
  simp only [sub_zero] at he
  linarith

/-- Bài 2(b): `exp x > 1+x` khi `x > 0`. -/
theorem exponential_gt_one_add {x : ℝ} (hx : 0 < x) : 1 + x < Real.exp x := by
  obtain ⟨c, hcm, he⟩ := lagrange_increment hx
    Real.continuous_exp.continuousOn Real.differentiable_exp.differentiableOn
  rw [Real.deriv_exp, Real.exp_zero, sub_zero] at he
  have hc : 1 < Real.exp c := by simpa only [Real.exp_zero] using Real.exp_strictMono hcm.1
  nlinarith

/-- Bài 2(c): hai cận ngặt của logarit khi `x > 1`. -/
theorem logarithm_bounds {x : ℝ} (hx : 1 < x) :
    (x - 1) / x < Real.log x ∧ Real.log x < x - 1 := by
  have hd (u : ℝ) (hu : u ∈ Ioo 1 x) : HasDerivAt Real.log u⁻¹ u :=
    Real.hasDerivAt_log (by linarith [hu.1])
  have hc : ContinuousOn Real.log (Icc 1 x) := by
    intro u hu
    exact (Real.continuousAt_log (by linarith [hu.1])).continuousWithinAt
  obtain ⟨c, hcm, he⟩ := lagrange_increment hx hc
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt)
  rw [(hd c hcm).deriv, Real.log_one, sub_zero] at he
  have hcpos : 0 < c := by linarith [hcm.1]
  have hxpos : 0 < x := by linarith
  have hlow : x⁻¹ < c⁻¹ := inv_strictAnti₀ hcpos hcm.2
  have hhigh : c⁻¹ < 1 := by
    simpa only [inv_one] using inv_strictAnti₀ (by norm_num : (0 : ℝ) < 1) hcm.1
  constructor
  · have := mul_lt_mul_of_pos_right hlow (sub_pos.mpr hx)
    rw [div_eq_mul_inv]
    nlinarith
  · have := mul_lt_mul_of_pos_right hhigh (sub_pos.mpr hx)
    nlinarith

/-- Bài 3: `|sin x − sin y| ≤ |x − y|`. -/
theorem sine_difference_bound (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| :=
  Real.abs_sin_sub_sin_le x y


/-
namespace calculus.SourceIssues

open Filter Topology

/-- Hàm afin dùng làm phản ví dụ cho Bài 4.3.5. -/
noncomputable def signChangingAffine (x : ℝ) : ℝ := x - 1 / 2

/-- Bài 4.3.5: hàm thỏa giả thiết liên tục và khả vi, nhưng công thức hàm mũ sai
tại mọi điểm có mẫu khác 0. -/
theorem exponential_ratio_counterexample :
    ContinuousOn signChangingAffine (Set.Icc 0 1) ∧
    DifferentiableOn ℝ signChangingAffine (Set.Ioo 0 1) ∧
    ∀ c ∈ Set.Ioo (0 : ℝ) 1, signChangingAffine c ≠ 0 →
      signChangingAffine 1 / signChangingAffine 0 ≠
        Real.exp ((1 - 0) * deriv signChangingAffine c / signChangingAffine c) := by
  refine ⟨(continuous_id.sub continuous_const).continuousOn,
    (differentiable_id.sub_const (1 / 2)).differentiableOn, ?_⟩
  intro c _ _ h
  have hratio : signChangingAffine 1 / signChangingAffine 0 = -1 := by
    norm_num [signChangingAffine]
  rw [hratio] at h
  have hpos := Real.exp_pos ((1 - 0) * deriv signChangingAffine c / signChangingAffine c)
  linarith

end calculus.SourceIssues

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- Bài 4.3.5, dòng 1112–1113: công thức tỉ số hàm mũ sai với `f(x) = x − 1/2` trên `[0, 1]`. -/
theorem source_exponential_ratio_witness {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b,
      f b / f a = Real.exp ((b - a) * (deriv f c / f c)) := by
  sorry

theorem endpoint_ratio_positive {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hne : ∀ x ∈ Icc a b, f x ≠ 0) :
    0 < f b / f a := by
  have ha := hne a (left_mem_Icc.mpr hab.le)
  have hb := hne b (right_mem_Icc.mpr hab.le)
  rcases lt_or_gt_of_ne ha with han | hap
  · have hbn : f b < 0 := by
      by_contra h
      have hbp : 0 < f b := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hb)
      obtain ⟨x, hx, he⟩ := intermediate_value_Icc hab.le hc ⟨han.le, hbp.le⟩
      exact hne x hx he
    exact div_pos_of_neg_of_neg hbn han
  · have hbp : 0 < f b := by
      by_contra h
      have hbn : f b < 0 := lt_of_le_of_ne (le_of_not_gt h) hb
      obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hab.le hc ⟨hbn.le, hap.le⟩
      exact hne x hx he
    exact div_pos hbp hap

/-- Bài 5: công thức tỉ số hàm mũ khi `f` khác 0 trên toàn đoạn `[a, b]`. -/
theorem exponential_ratio_witness {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hne : ∀ x ∈ Icc a b, f x ≠ 0) :
    ∃ c ∈ Ioo a b, f b / f a = Real.exp ((b - a) * (deriv f c / f c)) := by
  have hlog (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun x ↦ Real.log (f x)) (deriv f x / f x) x := by
    exact ((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.log
      (hne x (Ioo_subset_Icc_self hx))
  have hcl : ContinuousOn (fun x ↦ Real.log (f x)) (Icc a b) := by
    intro x hx
    exact (Real.continuousAt_log (hne x hx)).comp_continuousWithinAt (hc x hx)
  obtain ⟨c, hcm, he⟩ := lagrange_increment hab hcl
    (fun x hx ↦ (hlog x hx).differentiableAt.differentiableWithinAt)
  rw [(hlog c hcm).deriv, ← Real.log_div (hne b (right_mem_Icc.mpr hab.le))
    (hne a (left_mem_Icc.mpr hab.le))] at he
  refine ⟨c, hcm, ?_⟩
  rw [mul_comm, ← he, Real.exp_log (endpoint_ratio_positive hab hc hne)]

/-- Bài 4: tồn tại điểm có đạo hàm logarit bằng tổng hai nghịch đảo. -/
theorem logarithmic_derivative_witness {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hne : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∃ c ∈ Ioo a b, deriv f c / f c = 1 / (a - c) + 1 / (b - c) := by
  let g : ℝ → ℝ := fun x ↦ f x * (x - a) * (x - b)
  have hg (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt g
        ((deriv f x * (x - a) + f x) * (x - b) + f x * (x - a)) x := by
    simpa only [mul_one, id_eq] using
      (((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.fun_mul
        ((hasDerivAt_id x).sub_const a)).fun_mul ((hasDerivAt_id x).sub_const b)
  obtain ⟨c, hcm, he⟩ := rolle hab
    ((hc.mul (continuous_id.sub continuous_const).continuousOn).mul
      (continuous_id.sub continuous_const).continuousOn)
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt)
    (by simp)
  have hz := (hg c hcm).unique he
  have hfa := hne c hcm
  have ha : a - c ≠ 0 := sub_ne_zero.mpr hcm.1.ne
  have hb : b - c ≠ 0 := sub_ne_zero.mpr hcm.2.ne'
  refine ⟨c, hcm, ?_⟩
  field_simp [hfa, ha, hb]
  nlinarith [hz]

/-- Bài 6: tồn tại điểm thỏa phương trình đạo hàm, với `a > 0`. -/
theorem exponential_weight_witness {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : DifferentiableOn ℝ f (Icc 0 a)) (hz : f a = 0) :
    ∃ c ∈ Ioo 0 a, deriv f c = f c * (2024 - 1 / c) := by
  let g : ℝ → ℝ := fun x ↦ x * f x * Real.exp (-2024 * x)
  have hg (x : ℝ) (hx : x ∈ Ioo 0 a) :
      HasDerivAt g
        ((f x + x * deriv f x) * Real.exp (-2024 * x) +
          x * f x * (Real.exp (-2024 * x) * (-2024))) x := by
    have hdf := ((hf x (Ioo_subset_Icc_self hx)).differentiableAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivAt
    simpa only [one_mul, mul_one, id_eq] using
      ((hasDerivAt_id x).fun_mul hdf).fun_mul
        (((hasDerivAt_id x).const_mul (-2024)).exp)
  obtain ⟨c, hcm, he⟩ := rolle ha
    ((continuous_id.continuousOn.mul hf.continuousOn).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt)
    (by simp [hz])
  have heq := (hg c hcm).unique he
  have hzero : f c + c * deriv f c - 2024 * c * f c = 0 := by
    have hmul : (f c + c * deriv f c - 2024 * c * f c) *
        Real.exp (-2024 * c) = 0 := by nlinarith [heq]
    exact (mul_eq_zero.mp hmul).resolve_right (Real.exp_pos _).ne'
  refine ⟨c, hcm, ?_⟩
  have hne : c ≠ 0 := hcm.1.ne'
  field_simp [hne]
  nlinarith [hzero]

end calculus.Chapter04.Section03ExercisesBasic
