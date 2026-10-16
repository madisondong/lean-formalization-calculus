import calculus.Chapter04.Section03
import calculus.Chapter04.Section03ExercisesBasicSource
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bài tập 4.3.18: giá trị trung bình có trọng số cho hàm dương

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1168–1169. Hàm dương trên toàn đoạn; đạo hàm tại đầu mút là đạo hàm một bên, không cần `f′` liên tục.
-/

set_option autoImplicit false
noncomputable section

namespace calculus.Chapter04.Section03PositiveWeightedMeanExercise
open Set calculus.Chapter04.Section01Derivatives


theorem exp_neg_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using ((hasDerivAt_id x).neg.exp)


theorem weighted_cauchy_exact_witness {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 1))
    (hfd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo (0 : ℝ) 1,
      deriv f c - f c = (f 1 - Real.exp 1 * f 0) / (Real.exp 1 - 1) := by
  let F : ℝ → ℝ := fun x ↦ f x * Real.exp (-x)
  let G : ℝ → ℝ := fun x ↦ Real.exp (-x)
  have hF (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F ((deriv f x - f x) * Real.exp (-x)) x := by
    have ht := (hfd x hx).hasDerivAt.fun_mul (exp_neg_hasDerivAt x)
    apply ht.congr_deriv
    ring
  have hG (x : ℝ) : HasDerivAt G (-Real.exp (-x)) x :=
    exp_neg_hasDerivAt x
  have hGc : Continuous G := Real.continuous_exp.comp continuous_id.neg
  have hFc : ContinuousOn F (Icc 0 1) := hfc.mul hGc.continuousOn
  obtain ⟨c, hc, he⟩ := Section03.cauchy (by norm_num : (0 : ℝ) < 1)
    hFc (fun x hx ↦ (hF x hx).differentiableAt.differentiableWithinAt)
    hGc.continuousOn (fun x _ ↦ (hG x).differentiableAt.differentiableWithinAt)
  rw [(hG c).deriv, (hF c hc).deriv] at he
  have he' :
      (f 1 * Real.exp (-1) - f 0) * (-Real.exp (-c)) =
        (Real.exp (-1) - 1) * ((deriv f c - f c) * Real.exp (-c)) := by
    simpa only [F, G, neg_zero, Real.exp_zero, mul_one] using he
  have hcancel :
      -(f 1 * Real.exp (-1) - f 0) =
        (Real.exp (-1) - 1) * (deriv f c - f c) := by
    apply mul_right_cancel₀ (Real.exp_ne_zero (-c))
    calc
      -(f 1 * Real.exp (-1) - f 0) * Real.exp (-c) =
          (f 1 * Real.exp (-1) - f 0) * (-Real.exp (-c)) := by ring
      _ = (Real.exp (-1) - 1) *
          ((deriv f c - f c) * Real.exp (-c)) := he'
      _ = ((Real.exp (-1) - 1) * (deriv f c - f c)) * Real.exp (-c) := by ring
  have hlinear :
      (Real.exp 1 - 1) * (deriv f c - f c) = f 1 - Real.exp 1 * f 0 := by
    rw [Real.exp_neg] at hcancel
    field_simp [Real.exp_ne_zero 1] at hcancel
    nlinarith [hcancel]
  have hden : Real.exp 1 - 1 ≠ 0 := by
    have hp : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_two]
    exact hp.ne'
  refine ⟨c, hc, (eq_div_iff hden).2 ?_⟩
  nlinarith [hlinear]


theorem positive_endpoint_weight_bound {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (v - Real.exp 1 * u) / (Real.exp 1 - 1) ≤
      (2 / Real.pi) * (v - 2 * u) := by
  have heLower : (8 : ℝ) / 3 < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have heUpper : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpiLower : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    linarith [Real.pi_lt_d4]
  have hden : 0 < Real.exp 1 - 1 := by linarith
  have hA : 1 / (Real.exp 1 - 1) < 2 / Real.pi := by
    apply (div_lt_div_iff₀ hden Real.pi_pos).2
    nlinarith [heLower, hpiUpper]
  have hB : 4 / Real.pi < Real.exp 1 / (Real.exp 1 - 1) := by
    apply (div_lt_div_iff₀ Real.pi_pos hden).2
    have hm := mul_lt_mul_of_pos_left hpiLower (Real.exp_pos 1)
    nlinarith [heUpper, hm]
  have hAv := mul_lt_mul_of_pos_right hA hv
  have hBu := mul_lt_mul_of_pos_right hB hu
  have hsplit :
      (v - Real.exp 1 * u) / (Real.exp 1 - 1) =
        (1 / (Real.exp 1 - 1)) * v - (Real.exp 1 / (Real.exp 1 - 1)) * u := by
    ring
  have htarget : (2 / Real.pi) * (v - 2 * u) =
      (2 / Real.pi) * v - (4 / Real.pi) * u := by ring
  rw [hsplit, htarget]
  linarith [hAv, hBu]

/-- Bài 18: bất đẳng thức giá trị trung bình cho hàm dương trên toàn đoạn. -/
theorem source_positive_weighted_mean_witness {f : ℝ → ℝ}
    (hf : DifferentiableOnClosedInterval f 0 1)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x) :
    ∃ c ∈ Ioo (0 : ℝ) 1,
      deriv f c - f c ≤ (2 / Real.pi) * (f 1 - 2 * f 0) := by
  have hfc : ContinuousOn f (Icc 0 1) :=
    (Section03ExercisesBasicSource.source_closed_differentiableOn hf).continuousOn
  obtain ⟨c, hc, he⟩ := weighted_cauchy_exact_witness hfc hf.1
  refine ⟨c, hc, ?_⟩
  rw [he]
  exact positive_endpoint_weight_bound
    (hpos 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1))
    (hpos 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1))

end calculus.Chapter04.Section03PositiveWeightedMeanExercise
