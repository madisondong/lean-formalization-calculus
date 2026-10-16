import calculus.Chapter04.Section03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Bài tập 4.3.7: Rolle với trọng số cos

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1121–1122.
-/
namespace calculus.Chapter04.Section03WeightedRolleExercise
open Set calculus.Chapter04.Section03

/-- Bài 7: tồn tại điểm trong khoảng thỏa phương trình đạo hàm cấp hai. -/
theorem weighted_second_derivative_witness {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hff : Differentiable ℝ (deriv f)) (hzero : f 0 = 0) :
    ∃ c ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
      deriv (deriv f) c = f c * (1 + 2 * Real.tan c ^ 2) := by
  let h : ℝ → ℝ := fun x ↦ f x * Real.cos x
  have hh (x : ℝ) : HasDerivAt h (deriv f x * Real.cos x - f x * Real.sin x) x := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (hf x).hasDerivAt.fun_mul (Real.hasDerivAt_cos x)
  have hhc : ContinuousOn h (Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (hf.continuous.mul Real.continuous_cos).continuousOn
  obtain ⟨u, hu, hdu⟩ := rolle (by linarith [Real.pi_pos] : -(Real.pi / 2) < 0)
    (hhc.mono (Icc_subset_Icc le_rfl (by positivity)))
    (fun x _ ↦ (hh x).differentiableAt.differentiableWithinAt)
    (by simp [h, hzero, Real.cos_neg])
  obtain ⟨v, hv, hdv⟩ := rolle (by positivity : (0 : ℝ) < Real.pi / 2)
    (hhc.mono (Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl))
    (fun x _ ↦ (hh x).differentiableAt.differentiableWithinAt)
    (by simp [h, hzero])
  have huv : u < v := hu.2.trans hv.1
  have hsub : Icc u v ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    fun x hx ↦ ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
  let w : ℝ → ℝ := fun x ↦
    (deriv f x * Real.cos x - f x * Real.sin x) / Real.cos x ^ 2
  have hw (x : ℝ) (hx : x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
      HasDerivAt w
        ((deriv (deriv f) x - f x * (1 + 2 * Real.tan x ^ 2)) / Real.cos x) x := by
    have hcos : Real.cos x ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
    have hn := ((hff x).hasDerivAt.fun_mul (Real.hasDerivAt_cos x)).fun_sub
      ((hf x).hasDerivAt.fun_mul (Real.hasDerivAt_sin x))
    have hd := (Real.hasDerivAt_cos x).fun_pow 2
    have hh' := hn.div hd (pow_ne_zero 2 hcos)
    apply hh'.congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    ring
  have hwc : ContinuousOn w (Icc u v) := by
    apply ((hff.continuous.continuousOn.mul Real.continuous_cos.continuousOn).sub
      (hf.continuous.continuousOn.mul Real.continuous_sin.continuousOn)).div
        (Real.continuous_cos.pow 2).continuousOn
    intro x hx
    exact pow_ne_zero 2 (Real.cos_pos_of_mem_Ioo (hsub hx)).ne'
  have hwu : w u = 0 := by
    have he := (hh u).unique hdu
    simp only [w, he, zero_div]
  have hwv : w v = 0 := by
    have he := (hh v).unique hdv
    simp only [w, he, zero_div]
  obtain ⟨c, hc, hdc⟩ := rolle huv hwc
    (fun x hx ↦ (hw x (hsub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
    (hwu.trans hwv.symm)
  have hcm := hsub (Ioo_subset_Icc_self hc)
  have he := (hw c hcm).unique hdc
  have hn : deriv (deriv f) c - f c * (1 + 2 * Real.tan c ^ 2) = 0 :=
    (div_eq_zero_iff.mp he).resolve_right (Real.cos_pos_of_mem_Ioo hcm).ne'
  exact ⟨c, hcm, sub_eq_zero.mp hn⟩

end calculus.Chapter04.Section03WeightedRolleExercise
