import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bài 11: hai hàm dao động gần 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 528–542, dòng 618–629.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01OscillatingExercises
open Filter Set
open scoped Topology


def linearSineReciprocal (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.sin (1 / x)


def quadraticSineReciprocal (x : ℝ) : ℝ := if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)


theorem quadraticSineReciprocal_zero : quadraticSineReciprocal 0 = 0 := by
  simp [quadraticSineReciprocal]


theorem quadratic_slope_bound (y : ℝ) :
    |(quadraticSineReciprocal y - quadraticSineReciprocal 0) / (y - 0)| ≤ |y| := by
  rw [quadraticSineReciprocal_zero]
  by_cases hy : y = 0
  · simp [hy, quadraticSineReciprocal]
  · rw [quadraticSineReciprocal, if_neg hy]
    simp only [sub_zero]
    have heq : y ^ 2 * Real.sin (1 / y) / y = y * Real.sin (1 / y) := by
      field_simp
    rw [heq, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / y)) (abs_nonneg y)

/-- Bài 11(b): đạo hàm tại 0 bằng 0. -/
theorem quadratic_hasDerivAt_zero : HasDerivAt quadraticSineReciprocal 0 0 := by
  have hb : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using (continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {(0 : ℝ)}ᶜ))
  have ha : Tendsto (fun y : ℝ ↦ |(quadraticSineReciprocal y - quadraticSineReciprocal 0) / (y - 0)|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun y ↦ abs_nonneg _)
      (Eventually.of_forall quadratic_slope_bound) hb
  have hlim : Tendsto (fun y : ℝ ↦ (quadraticSineReciprocal y - quadraticSineReciprocal 0) / (y - 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using ha)
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient]
  exact hlim


theorem reciprocal_sine_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.sin (1 / y))
      (-Real.cos (1 / x) / x ^ 2) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using (hasDerivAt_inv hx)
  apply ((Real.hasDerivAt_sin (1 / x)).comp x hi).congr_deriv
  ring

/-- Bài 11(b): đạo hàm tại mọi `x ≠ 0`. -/
theorem quadratic_hasDerivAt_nonzero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt quadraticSineReciprocal (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
  have hp := (hasDerivAt_id x).fun_pow 2
  have hs := hp.mul (reciprocal_sine_hasDerivAt x hx)
  have heq : quadraticSineReciprocal =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ 2 * Real.sin (1 / y)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [quadraticSineReciprocal, if_neg hy]
  apply (hs.congr_of_eventuallyEq heq).congr_deriv
  norm_num
  field_simp
  ring

/-- Bài 11(b): khả vi tại mọi điểm, kể cả 0. -/
theorem quadratic_differentiable : Differentiable ℝ quadraticSineReciprocal := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact quadratic_hasDerivAt_zero.differentiableAt
  · exact (quadratic_hasDerivAt_nonzero x hx).differentiableAt


theorem quadratic_derivative (x : ℝ) :
    deriv quadraticSineReciprocal x =
      if x = 0 then 0 else 2 * x * Real.sin (1 / x) - Real.cos (1 / x) := by
  by_cases hx : x = 0
  · subst x
    simpa using quadratic_hasDerivAt_zero.deriv
  · rw [if_neg hx]
    exact (quadratic_hasDerivAt_nonzero x hx).deriv


def periodicApproach (n : ℕ) : ℝ := 1 / (((n + 1 : ℕ) : ℝ) * (2 * Real.pi))


theorem periodicApproach_pos (n : ℕ) : 0 < periodicApproach n := by
  unfold periodicApproach
  positivity


theorem periodicApproach_tendsto_zero : Tendsto periodicApproach atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlim := hn.div_const (2 * Real.pi)
  change Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) * (2 * Real.pi))) atTop (𝓝 0)
  simpa only [zero_div, div_div] using hlim


theorem quadratic_derivative_periodicApproach (n : ℕ) :
    deriv quadraticSineReciprocal (periodicApproach n) = -1 := by
  have hx0 : periodicApproach n ≠ 0 := (periodicApproach_pos n).ne'
  rw [quadratic_derivative, if_neg hx0]
  have hi : 1 / periodicApproach n = (((n + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
    simp only [periodicApproach, one_div, inv_inv]
  rw [hi, Real.cos_nat_mul_two_pi]
  have hsin : Real.sin ((((n + 1 : ℕ) : ℝ) * (2 * Real.pi))) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 (n + 1)
  rw [hsin]
  ring


theorem quadratic_derivative_not_continuousAt_zero :
    ¬ ContinuousAt (deriv quadraticSineReciprocal) 0 := by
  intro hc
  have hlim := hc.tendsto.comp periodicApproach_tendsto_zero
  have heq : (fun n : ℕ ↦ deriv quadraticSineReciprocal (periodicApproach n)) =
      (fun _ : ℕ ↦ (-1 : ℝ)) := funext quadratic_derivative_periodicApproach
  simp only [Function.comp_def] at hlim
  rw [heq, quadratic_hasDerivAt_zero.deriv] at hlim
  have hn : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1 : ℝ)) := tendsto_const_nhds
  have hfalse := tendsto_nhds_unique hlim hn
  norm_num at hfalse


theorem quadratic_differentiable_not_continuous_derivative :
    Differentiable ℝ quadraticSineReciprocal ∧ ¬ Continuous (deriv quadraticSineReciprocal) := by
  refine ⟨quadratic_differentiable, ?_⟩
  intro hc
  exact quadratic_derivative_not_continuousAt_zero hc.continuousAt


/-- Bài 11(a): đạo hàm tại mọi điểm khác 0. -/
theorem linear_hasDerivAt_nonzero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt linearSineReciprocal (Real.sin (1 / x) - Real.cos (1 / x) / x) x := by
  have hs := (hasDerivAt_id x).mul (reciprocal_sine_hasDerivAt x hx)
  have heq : linearSineReciprocal =ᶠ[𝓝 x] (fun y : ℝ ↦ y * Real.sin (1 / y)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [linearSineReciprocal, if_neg hy]
  apply (hs.congr_of_eventuallyEq heq).congr_deriv
  norm_num
  field_simp
  ring


def quarterPeriodApproach (n : ℕ) : ℝ :=
  1 / (Real.pi / 2 + (((n + 1 : ℕ) : ℝ) * (2 * Real.pi)))


theorem quarterPeriodApproach_pos (n : ℕ) : 0 < quarterPeriodApproach n := by
  unfold quarterPeriodApproach
  positivity


theorem quarterPeriodApproach_tendsto_zero : Tendsto quarterPeriodApproach atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ 1 + Real.pi / 2 * periodicApproach n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul periodicApproach_tendsto_zero)
  have hlim := periodicApproach_tendsto_zero.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : quarterPeriodApproach =
      (fun n : ℕ ↦ periodicApproach n / (1 + Real.pi / 2 * periodicApproach n)) := by
    funext n
    unfold quarterPeriodApproach periodicApproach
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hpi := Real.pi_pos
    field_simp
    ring
  rw [heq]
  have hzero : Tendsto (periodicApproach / (fun n : ℕ ↦ 1 + Real.pi / 2 * periodicApproach n))
      atTop (𝓝 (0 : ℝ)) := by simpa only [zero_div] using hlim
  exact hzero.congr' (Eventually.of_forall fun _ ↦ rfl)


theorem linear_slope_value (y : ℝ) (hy : y ≠ 0) :
    (linearSineReciprocal y - linearSineReciprocal 0) / (y - 0) = Real.sin (1 / y) := by
  have hz : linearSineReciprocal 0 = 0 := by simp [linearSineReciprocal]
  rw [hz, linearSineReciprocal, if_neg hy]
  simp only [sub_zero]
  field_simp


theorem linear_slope_periodicApproach (n : ℕ) :
    (linearSineReciprocal (periodicApproach n) - linearSineReciprocal 0) /
      (periodicApproach n - 0) = 0 := by
  rw [linear_slope_value _ (periodicApproach_pos n).ne']
  simp only [periodicApproach, one_div, inv_inv]
  simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 (n + 1)


theorem linear_slope_quarterPeriodApproach (n : ℕ) :
    (linearSineReciprocal (quarterPeriodApproach n) - linearSineReciprocal 0) /
      (quarterPeriodApproach n - 0) = 1 := by
  rw [linear_slope_value _ (quarterPeriodApproach_pos n).ne']
  simp only [quarterPeriodApproach, one_div, inv_inv]
  simpa only [Real.sin_pi_div_two] using Real.sin_add_nat_mul_two_pi (Real.pi / 2) (n + 1)

/-- Bài 11(a): hàm không khả vi tại 0. -/
theorem linear_not_differentiableAt_zero : ¬ DifferentiableAt ℝ linearSineReciprocal 0 := by
  intro h
  have hs := h.hasDerivAt.tendsto_slope
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient] at hs
  have hp : Tendsto periodicApproach atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨periodicApproach_tendsto_zero, Eventually.of_forall fun n ↦ ?_⟩
    exact (periodicApproach_pos n).ne'
  have hq : Tendsto quarterPeriodApproach atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨quarterPeriodApproach_tendsto_zero, Eventually.of_forall fun n ↦ ?_⟩
    exact (quarterPeriodApproach_pos n).ne'
  have h0 := hs.comp hp
  have h1 := hs.comp hq
  have heq0 : (fun n : ℕ ↦
      (linearSineReciprocal (periodicApproach n) - linearSineReciprocal 0) /
        (periodicApproach n - 0)) = (fun _ : ℕ ↦ (0 : ℝ)) := funext linear_slope_periodicApproach
  have heq1 : (fun n : ℕ ↦
      (linearSineReciprocal (quarterPeriodApproach n) - linearSineReciprocal 0) /
        (quarterPeriodApproach n - 0)) = (fun _ : ℕ ↦ (1 : ℝ)) := funext linear_slope_quarterPeriodApproach
  simp only [Function.comp_def] at h0 h1
  rw [heq0] at h0
  rw [heq1] at h1
  have hz : deriv linearSineReciprocal 0 = 0 := tendsto_nhds_unique h0 tendsto_const_nhds
  have ho : deriv linearSineReciprocal 0 = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
  linarith

/-- Bài 11(a): hàm khả vi khi và chỉ khi `x ≠ 0`. -/
theorem linear_differentiableAt_iff (x : ℝ) : DifferentiableAt ℝ linearSineReciprocal x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    exact linear_not_differentiableAt_zero h
  · intro hx
    exact (linear_hasDerivAt_nonzero x hx).differentiableAt


/-- Bài 17: cộng hàm `cx` vào hàm của Bài 11(b). -/
def tiltedQuadraticSineReciprocal (c x : ℝ) : ℝ := quadraticSineReciprocal x + c * x


theorem tiltedQuadratic_eq_source (c x : ℝ) :
    tiltedQuadraticSineReciprocal c x =
      if x = 0 then 0 else x ^ 2 * Real.sin (1 / x) + c * x := by
  by_cases hx : x = 0
  · simp [tiltedQuadraticSineReciprocal, hx, quadraticSineReciprocal_zero]
  · simp only [tiltedQuadraticSineReciprocal, quadraticSineReciprocal, if_neg hx]


theorem tiltedQuadratic_hasDerivAt (c x : ℝ) :
    HasDerivAt (tiltedQuadraticSineReciprocal c) (deriv quadraticSineReciprocal x + c) x := by
  have h := (quadratic_differentiable x).hasDerivAt.add ((hasDerivAt_id x).const_mul c)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp only [mul_one]

/-- Bài 17(a): hàm khả vi trên ℝ với `c ∈ (0, 1)`. -/
theorem tiltedQuadratic_differentiable (c : ℝ) (_hc : c ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℝ (tiltedQuadraticSineReciprocal c) :=
  fun x ↦ (tiltedQuadratic_hasDerivAt c x).differentiableAt


theorem tiltedQuadratic_derivative (c x : ℝ) :
    deriv (tiltedQuadraticSineReciprocal c) x = deriv quadraticSineReciprocal x + c :=
  (tiltedQuadratic_hasDerivAt c x).deriv


theorem quadratic_derivative_quarterPeriodApproach (n : ℕ) :
    deriv quadraticSineReciprocal (quarterPeriodApproach n) = 2 * quarterPeriodApproach n := by
  have hn : quarterPeriodApproach n ≠ 0 := (quarterPeriodApproach_pos n).ne'
  rw [quadratic_derivative, if_neg hn]
  have hi : 1 / quarterPeriodApproach n =
      Real.pi / 2 + (((n + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
    simp only [quarterPeriodApproach, one_div, inv_inv]
  rw [hi, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- Bài 17(b): đạo hàm nhận cả hai dấu trong mỗi khoảng đối xứng quanh 0, dù không liên tục. -/
theorem tiltedQuadratic_derivative_changes_sign (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∀ α : ℝ, 0 < α → ∃ s ∈ Ioo (-α) α, ∃ t ∈ Ioo (-α) α,
      deriv (tiltedQuadraticSineReciprocal c) s < 0 ∧
        0 < deriv (tiltedQuadraticSineReciprocal c) t := by
  intro α hα
  have hsmallp : ∀ᶠ n : ℕ in atTop, periodicApproach n < α :=
    periodicApproach_tendsto_zero.eventually (Iio_mem_nhds hα)
  have hsmallq : ∀ᶠ n : ℕ in atTop, quarterPeriodApproach n < α :=
    quarterPeriodApproach_tendsto_zero.eventually (Iio_mem_nhds hα)
  obtain ⟨n, hnp, hnq⟩ := (hsmallp.and hsmallq).exists
  have hp := periodicApproach_pos n
  have hq := quarterPeriodApproach_pos n
  refine ⟨periodicApproach n, ⟨by linarith, hnp⟩,
    quarterPeriodApproach n, ⟨by linarith, hnq⟩, ?_, ?_⟩
  · rw [tiltedQuadratic_derivative, quadratic_derivative_periodicApproach]
    linarith [hc.2]
  · rw [tiltedQuadratic_derivative, quadratic_derivative_quarterPeriodApproach]
    linarith [hc.1]

end calculus.Chapter04.Section01OscillatingExercises
