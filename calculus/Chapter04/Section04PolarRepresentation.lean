import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith

/-!
# 4.4: biểu diễn trong tọa độ cực

Nguồn: `source/Ch4_hamsokhavi.tex` dòng 2450, dòng 2452, dòng 2482 và công thức 4.4.13 / nhãn `TDC`, dòng 2488–2493. Bán kính có dấu `r` cho khoảng cách `|r|`. Với điểm khác gốc, bán kính dương và góc trong `[0, 2π)` là duy nhất.
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section04PolarRepresentation

open Set


noncomputable def signedPolarPoint (r θ : ℝ) : ℂ :=
  (r : ℂ) * (Circle.exp θ : ℂ)


theorem signedPolarPoint_re (r θ : ℝ) :
    (signedPolarPoint r θ).re = r * Real.cos θ := by
  simp [signedPolarPoint, Circle.coe_exp]


theorem signedPolarPoint_im (r θ : ℝ) :
    (signedPolarPoint r θ).im = r * Real.sin θ := by
  simp [signedPolarPoint, Circle.coe_exp]


theorem signedPolarPoint_cartesian (r θ : ℝ) :
    ((signedPolarPoint r θ).re, (signedPolarPoint r θ).im) =
      (r * Real.cos θ, r * Real.sin θ) := by
  rw [signedPolarPoint_re, signedPolarPoint_im]


theorem norm_signedPolarPoint (r θ : ℝ) : ‖signedPolarPoint r θ‖ = |r| := by
  simp only [signedPolarPoint, norm_mul, Complex.norm_real, Circle.norm_coe,
    Real.norm_eq_abs, mul_one]


theorem dist_signedPolarPoint_origin (r θ : ℝ) :
    dist (signedPolarPoint r θ) 0 = |r| := by
  rw [dist_zero_right, norm_signedPolarPoint]


theorem source_nonnegative_radius_distance (r θ : ℝ) (hr : 0 ≤ r) :
    dist (signedPolarPoint r θ) 0 = r := by
  rw [dist_signedPolarPoint_origin, abs_of_nonneg hr]

/-- Dòng 2450: tại gốc, góc có thể chọn tùy ý. -/
theorem signedPolarPoint_zero_radius (θ : ℝ) : signedPolarPoint 0 θ = 0 := by
  simp [signedPolarPoint]


theorem signedPolarPoint_eq_zero_iff (r θ : ℝ) :
    signedPolarPoint r θ = 0 ↔ r = 0 := by
  rw [← norm_eq_zero, norm_signedPolarPoint, abs_eq_zero]


theorem signedPolarPoint_neg_radius (r θ : ℝ) :
    signedPolarPoint (-r) θ = -signedPolarPoint r θ := by
  simp [signedPolarPoint]

/-- Dòng 2452: đổi dấu bán kính tương đương cộng π vào góc. -/
theorem signedPolarPoint_neg_radius_eq_add_pi (r θ : ℝ) :
    signedPolarPoint (-r) θ = signedPolarPoint r (θ + Real.pi) := by
  apply Complex.ext
  · simp [signedPolarPoint_re, Real.cos_add_pi]
  · simp [signedPolarPoint_im, Real.sin_add_pi]


theorem signedPolarPoint_neg_radius_ne (r θ : ℝ) (hr : r ≠ 0) :
    signedPolarPoint (-r) θ ≠ signedPolarPoint r θ := by
  intro h
  have hz : signedPolarPoint r θ = 0 := by
    have he := signedPolarPoint_neg_radius r θ
    rw [h] at he
    exact CharZero.neg_eq_self_iff.mp he.symm
  exact hr ((signedPolarPoint_eq_zero_iff r θ).mp hz)


theorem norm_signedPolarPoint_neg_radius (r θ : ℝ) :
    ‖signedPolarPoint (-r) θ‖ = ‖signedPolarPoint r θ‖ := by
  rw [norm_signedPolarPoint, norm_signedPolarPoint, abs_neg]


theorem signedPolarPoint_re_pos_iff (r θ : ℝ) :
    0 < (signedPolarPoint r θ).re ↔
      (0 < r ∧ 0 < Real.cos θ) ∨ (r < 0 ∧ Real.cos θ < 0) := by
  rw [signedPolarPoint_re, mul_pos_iff]


theorem signedPolarPoint_im_pos_iff (r θ : ℝ) :
    0 < (signedPolarPoint r θ).im ↔
      (0 < r ∧ 0 < Real.sin θ) ∨ (r < 0 ∧ Real.sin θ < 0) := by
  rw [signedPolarPoint_im, mul_pos_iff]


theorem signedPolarPoint_add_two_pi (r θ : ℝ) :
    signedPolarPoint r (θ + 2 * Real.pi) = signedPolarPoint r θ := by
  rw [signedPolarPoint, Circle.exp_add_two_pi]
  rfl


theorem signedPolarPoint_parameters_not_unique (r θ : ℝ) :
    (r, θ + 2 * Real.pi) ≠ (r, θ) ∧
      signedPolarPoint r (θ + 2 * Real.pi) = signedPolarPoint r θ := by
  constructor
  · intro h
    have hθ := congrArg Prod.snd h
    linarith [Real.pi_pos]
  · exact signedPolarPoint_add_two_pi r θ


noncomputable def nonnegativePolarAngle (z : ℂ) : ℝ :=
  if 0 ≤ z.arg then z.arg else z.arg + 2 * Real.pi


theorem nonnegativePolarAngle_mem (z : ℂ) : nonnegativePolarAngle z ∈ Ico 0 (2 * Real.pi) := by
  unfold nonnegativePolarAngle
  split_ifs with h
  · exact ⟨h, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩
  · exact ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos],
      by linarith [not_le.mp h]⟩


theorem signedPolarPoint_norm_nonnegativePolarAngle (z : ℂ) :
    signedPolarPoint ‖z‖ (nonnegativePolarAngle z) = z := by
  apply Complex.ext
  · rw [signedPolarPoint_re]
    unfold nonnegativePolarAngle
    split_ifs
    · exact Complex.norm_mul_cos_arg z
    · rw [Real.cos_add_two_pi]
      exact Complex.norm_mul_cos_arg z
  · rw [signedPolarPoint_im]
    unfold nonnegativePolarAngle
    split_ifs
    · exact Complex.norm_mul_sin_arg z
    · rw [Real.sin_add_two_pi]
      exact Complex.norm_mul_sin_arg z


theorem signedPolarPoint_angle_injective (r : ℝ) (hr : 0 < r)
    {θ ψ : ℝ} (hθ : θ ∈ Ico 0 (2 * Real.pi)) (hψ : ψ ∈ Ico 0 (2 * Real.pi))
    (h : signedPolarPoint r θ = signedPolarPoint r ψ) : θ = ψ := by
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hθ hψ
  apply Circle.ext
  have hr₀ : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  exact mul_left_cancel₀ hr₀ h

/-- Dòng 2482: tại điểm khác gốc, biểu diễn với `r > 0`, `θ ∈ [0, 2π)` là duy nhất. -/
theorem existsUnique_positive_polar_coordinates (z : ℂ) (hz : z ≠ 0) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ p.2 ∈ Ico 0 (2 * Real.pi) ∧
      signedPolarPoint p.1 p.2 = z := by
  refine ⟨(‖z‖, nonnegativePolarAngle z),
    ⟨norm_pos_iff.mpr hz, nonnegativePolarAngle_mem z,
      signedPolarPoint_norm_nonnegativePolarAngle z⟩, ?_⟩
  rintro ⟨r, θ⟩ ⟨hr, hθ, hp⟩
  have hrz : r = ‖z‖ := by
    have hn := congrArg (fun w : ℂ ↦ ‖w‖) hp
    simpa only [norm_signedPolarPoint, abs_of_pos hr] using hn
  have hθz : θ = nonnegativePolarAngle z := by
    apply signedPolarPoint_angle_injective r hr hθ (nonnegativePolarAngle_mem z)
    rw [hp, hrz, signedPolarPoint_norm_nonnegativePolarAngle]
  exact Prod.ext hrz hθz

end calculus.Chapter04.Section04PolarRepresentation
