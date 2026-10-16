import calculus.Chapter04.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §4.4: thương dao động và hiệu cot

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1548–1554 (Ví dụ 4.4.7), dòng 1621–1640 (Ví dụ 4.4.9).
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section04OscillatoryCotangentExamples
open Set Filter
open scoped Topology


theorem eventually_identity_ne_zero : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa only [mem_compl_iff, mem_singleton_iff] using hx


theorem sine_div_identity_tendsto_one :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa only [zero_add, Real.sin_zero, Real.cos_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_sin 0).tendsto_slope_zero


theorem eventually_sine_ne_zero : ∀ᶠ x : ℝ in 𝓝[≠] 0, Real.sin x ≠ 0 := by
  filter_upwards [sine_div_identity_tendsto_one.eventually_ne one_ne_zero] with x hx
  exact (div_ne_zero_iff.mp hx).1


theorem eventually_cosine_ne_zero : ∀ᶠ x : ℝ in 𝓝[≠] 0, Real.cos x ≠ 0 := by
  have hc : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  exact hc.eventually_ne one_ne_zero

/-- Tử số chỉ xét trên `x ≠ 0`. -/
noncomputable def oscillatoryNumerator (x : ℝ) : ℝ :=
  x - x ^ 2 * Real.sin (1 / x)


theorem oscillatoryNumerator_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt oscillatoryNumerator
      (1 - 2 * x * Real.sin (1 / x) + Real.cos (1 / x)) x := by
  have hs : HasDerivAt (fun y : ℝ ↦ Real.sin (y⁻¹))
      (Real.cos (x⁻¹) * (-1 / x ^ 2)) x :=
    (Real.hasDerivAt_sin (x⁻¹)).comp x ((hasDerivAt_id x).fun_inv hx)
  have hsq : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using
      (hasDerivAt_id x).fun_pow 2
  have h := (hasDerivAt_id x).fun_sub (hsq.fun_mul hs)
  have he : 1 - (2 * x * Real.sin (x⁻¹) +
      x ^ 2 * (Real.cos (x⁻¹) * (-1 / x ^ 2))) =
      1 - 2 * x * Real.sin (x⁻¹) + Real.cos (x⁻¹) := by
    field_simp [hx]
    ring
  rw [he] at h
  change HasDerivAt (fun y : ℝ ↦ y - y ^ 2 * Real.sin (1 / y))
    (1 - 2 * x * Real.sin (1 / x) + Real.cos (1 / x)) x
  simpa only [one_div, id_eq] using h

/-- Dòng 1551: công thức thương đạo hàm. -/
theorem oscillatory_derivative_ratio_formula {x : ℝ} (hx : x ≠ 0) :
    deriv oscillatoryNumerator x / deriv Real.sin x =
      (1 - 2 * x * Real.sin (1 / x) + Real.cos (1 / x)) / Real.cos x := by
  rw [(oscillatoryNumerator_hasDerivAt hx).deriv, Real.deriv_sin]


theorem identity_mul_sine_inverse_tendsto_zero :
    Tendsto (fun x : ℝ ↦ x * Real.sin (1 / x)) (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero_norm (a := fun x : ℝ ↦ |x|)
  · intro x
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg x)
  · simpa only [id_eq, Real.norm_eq_abs, norm_zero] using
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).norm


theorem oscillatoryNumerator_tendsto_zero :
    Tendsto oscillatoryNumerator (𝓝[≠] 0) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ ↦ x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := hx.sub (hx.mul identity_mul_sine_inverse_tendsto_zero)
  change Tendsto (fun x : ℝ ↦ x - x ^ 2 * Real.sin (1 / x)) (𝓝[≠] 0) (𝓝 0)
  simpa only [pow_two, mul_assoc, sub_zero, zero_mul] using h

/-- Ví dụ 4.4.7: thương ban đầu có giới hạn bằng 1. -/
theorem oscillatory_quotient_tendsto_one :
    Tendsto (fun x ↦ oscillatoryNumerator x / Real.sin x) (𝓝[≠] 0) (𝓝 1) := by
  have hn : Tendsto (fun x : ℝ ↦ 1 - x * Real.sin (1 / x)) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[≠] 0) (𝓝 1)).sub
        identity_mul_sine_inverse_tendsto_zero
  have h := hn.div sine_div_identity_tendsto_one one_ne_zero
  have hlim : Tendsto (fun x : ℝ ↦ (1 - x * Real.sin (1 / x)) /
      (Real.sin x / x)) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [Pi.div_def, div_one] using h
  apply hlim.congr'
  filter_upwards [eventually_identity_ne_zero, eventually_sine_ne_zero] with x hx hs
  unfold oscillatoryNumerator
  field_simp [hx, hs]


noncomputable def evenReciprocalSequence (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) * (2 * Real.pi))⁻¹


noncomputable def oddReciprocalSequence (n : ℕ) : ℝ :=
  (Real.pi + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi))⁻¹

theorem evenReciprocalSequence_positive (n : ℕ) : 0 < evenReciprocalSequence n := by
  unfold evenReciprocalSequence
  positivity

theorem oddReciprocalSequence_positive (n : ℕ) : 0 < oddReciprocalSequence n := by
  unfold oddReciprocalSequence
  positivity


theorem evenReciprocalSequence_tendsto_zero :
    Tendsto evenReciprocalSequence atTop (𝓝[≠] 0) := by
  have hn : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact tendsto_inv_atTop_zero.comp (hn.atTop_mul_const (by positivity))
  · exact Eventually.of_forall fun n ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        (evenReciprocalSequence_positive n).ne'

theorem oddReciprocalSequence_tendsto_zero :
    Tendsto oddReciprocalSequence atTop (𝓝[≠] 0) := by
  have hn : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop Real.pi (hn.atTop_mul_const (by positivity)))
  · exact Eventually.of_forall fun n ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        (oddReciprocalSequence_positive n).ne'


theorem oscillatory_derivative_ratio_even_value (n : ℕ) :
    deriv oscillatoryNumerator (evenReciprocalSequence n) /
        deriv Real.sin (evenReciprocalSequence n) =
      2 / Real.cos (evenReciprocalSequence n) := by
  rw [(oscillatoryNumerator_hasDerivAt (evenReciprocalSequence_positive n).ne').deriv,
    Real.deriv_sin]
  have hs : Real.sin (((n + 1 : ℕ) : ℝ) * (2 * Real.pi)) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 (n + 1)
  simp only [evenReciprocalSequence, one_div, inv_inv, hs,
    Real.cos_nat_mul_two_pi, mul_zero, sub_zero]
  norm_num


theorem oscillatory_derivative_ratio_odd_value (n : ℕ) :
    deriv oscillatoryNumerator (oddReciprocalSequence n) /
        deriv Real.sin (oddReciprocalSequence n) = 0 := by
  rw [(oscillatoryNumerator_hasDerivAt (oddReciprocalSequence_positive n).ne').deriv,
    Real.deriv_sin]
  simp only [oddReciprocalSequence, one_div, inv_inv, Real.sin_add_nat_mul_two_pi,
    Real.cos_add_nat_mul_two_pi, Real.sin_pi, Real.cos_pi, mul_zero, sub_zero]
  norm_num

theorem oscillatory_derivative_ratio_even_tendsto_two :
    Tendsto (fun n ↦ deriv oscillatoryNumerator (evenReciprocalSequence n) /
      deriv Real.sin (evenReciprocalSequence n)) atTop (𝓝 (2 : ℝ)) := by
  have he : (fun n ↦ deriv oscillatoryNumerator (evenReciprocalSequence n) /
      deriv Real.sin (evenReciprocalSequence n)) =
      (fun n ↦ 2 / Real.cos (evenReciprocalSequence n)) :=
    funext oscillatory_derivative_ratio_even_value
  rw [he]
  have hc : Tendsto (fun n ↦ Real.cos (evenReciprocalSequence n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp
      (tendsto_nhds_of_tendsto_nhdsWithin evenReciprocalSequence_tendsto_zero)
  simpa only [Pi.div_def, div_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).div hc one_ne_zero

theorem oscillatory_derivative_ratio_odd_tendsto_zero :
    Tendsto (fun n ↦ deriv oscillatoryNumerator (oddReciprocalSequence n) /
      deriv Real.sin (oddReciprocalSequence n)) atTop (𝓝 (0 : ℝ)) := by
  have he : (fun n ↦ deriv oscillatoryNumerator (oddReciprocalSequence n) /
      deriv Real.sin (oddReciprocalSequence n)) = (fun _ : ℕ ↦ (0 : ℝ)) :=
    funext oscillatory_derivative_ratio_odd_value
  rw [he]
  exact tendsto_const_nhds


theorem oscillatory_derivative_ratio_no_finite_limit :
    ¬ ∃ l : ℝ, Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
      (𝓝[≠] 0) (𝓝 l) := by
  rintro ⟨l, hl⟩
  have h2 : (2 : ℝ) = l := tendsto_nhds_unique
    oscillatory_derivative_ratio_even_tendsto_two (hl.comp evenReciprocalSequence_tendsto_zero)
  have h0 : (0 : ℝ) = l := tendsto_nhds_unique
    oscillatory_derivative_ratio_odd_tendsto_zero (hl.comp oddReciprocalSequence_tendsto_zero)
  linarith

theorem oscillatory_derivative_ratio_not_atTop :
    ¬ Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
      (𝓝[≠] 0) atTop := by
  intro hl
  exact (not_tendsto_atTop_of_tendsto_nhds oscillatory_derivative_ratio_odd_tendsto_zero)
    (hl.comp oddReciprocalSequence_tendsto_zero)

theorem oscillatory_derivative_ratio_not_atBot :
    ¬ Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
      (𝓝[≠] 0) atBot := by
  intro hl
  exact (not_tendsto_atBot_of_tendsto_nhds oscillatory_derivative_ratio_odd_tendsto_zero)
    (hl.comp oddReciprocalSequence_tendsto_zero)


theorem oscillatory_eventual_derivative_domain :
    ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 ∧ Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 ∧
      HasDerivAt oscillatoryNumerator
        (1 - 2 * x * Real.sin (1 / x) + Real.cos (1 / x)) x ∧
      HasDerivAt Real.sin (Real.cos x) x := by
  filter_upwards [eventually_identity_ne_zero, eventually_sine_ne_zero,
    eventually_cosine_ne_zero] with x hx hs hc
  exact ⟨hx, hs, hc, oscillatoryNumerator_hasDerivAt hx, Real.hasDerivAt_sin x⟩


theorem oscillatory_source_example :
    Tendsto oscillatoryNumerator (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto Real.sin (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x ↦ oscillatoryNumerator x / Real.sin x) (𝓝[≠] 0) (𝓝 1) ∧
      (¬ ∃ l : ℝ, Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
        (𝓝[≠] 0) (𝓝 l)) ∧
      (¬ Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
        (𝓝[≠] 0) atTop) ∧
      (¬ Tendsto (fun x ↦ deriv oscillatoryNumerator x / deriv Real.sin x)
        (𝓝[≠] 0) atBot) := by
  refine ⟨oscillatoryNumerator_tendsto_zero, ?_, oscillatory_quotient_tendsto_one,
    oscillatory_derivative_ratio_no_finite_limit, oscillatory_derivative_ratio_not_atTop,
    oscillatory_derivative_ratio_not_atBot⟩
  simpa only [Real.sin_zero] using
    Real.continuous_sin.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)


theorem cotangent_factor_numerator_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * Real.cos y - Real.sin y) (-x * Real.sin x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ y * Real.cos y - Real.sin y)
      (1 * Real.cos x + x * (-Real.sin x) - Real.cos x) x := by
    simpa only [id_eq] using
      ((hasDerivAt_id x).fun_mul (Real.hasDerivAt_cos x)).fun_sub (Real.hasDerivAt_sin x)
  exact h.congr_deriv (by ring)


theorem cotangent_factor_denominator_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * (Real.sin y) ^ 2)
      ((Real.sin x) ^ 2 + 2 * x * Real.sin x * Real.cos x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ y * (Real.sin y) ^ 2)
      ((Real.sin x) ^ 2 + x * (2 * Real.sin x * Real.cos x)) x := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul] using
      (hasDerivAt_id x).fun_mul ((Real.hasDerivAt_sin x).fun_pow 2)
  exact h.congr_deriv (by ring)


theorem cotangent_normalized_denominator_tendsto_three :
    Tendsto (fun x : ℝ ↦ Real.sin x / x + 2 * Real.cos x) (𝓝[≠] 0) (𝓝 3) := by
  have hc : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  simpa only [mul_one, show (1 + 2 : ℝ) = 3 by norm_num] using
    sine_div_identity_tendsto_one.add (hc.const_mul 2)


theorem cotangent_eventual_denominator_derivative_ne_zero :
    ∀ᶠ x : ℝ in 𝓝[≠] 0,
      (Real.sin x) ^ 2 + 2 * x * Real.sin x * Real.cos x ≠ 0 := by
  filter_upwards [eventually_identity_ne_zero, eventually_sine_ne_zero,
    cotangent_normalized_denominator_tendsto_three.eventually_ne (by norm_num : (3 : ℝ) ≠ 0)]
      with x hx hs hd
  have he : (Real.sin x) ^ 2 + 2 * x * Real.sin x * Real.cos x =
      x * Real.sin x * (Real.sin x / x + 2 * Real.cos x) := by
    field_simp [hx]
  rw [he]
  exact mul_ne_zero (mul_ne_zero hx hs) hd


theorem cotangent_factor_derivative_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (-x * Real.sin x) /
      ((Real.sin x) ^ 2 + 2 * x * Real.sin x * Real.cos x))
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (-1 : ℝ))
    (𝓝[≠] 0) (𝓝 (-1))).div cotangent_normalized_denominator_tendsto_three (by norm_num)
  change Tendsto (fun x : ℝ ↦ -1 / (Real.sin x / x + 2 * Real.cos x))
    (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) at h
  apply h.congr'
  filter_upwards [eventually_identity_ne_zero, eventually_sine_ne_zero,
    cotangent_normalized_denominator_tendsto_three.eventually_ne (by norm_num : (3 : ℝ) ≠ 0),
    cotangent_eventual_denominator_derivative_ne_zero] with x hx hs hd hgd
  field_simp [hx, hs, hd, hgd]


theorem cotangent_second_factor_tendsto :
    Tendsto (fun x : ℝ ↦ (x * Real.cos x - Real.sin x) / (x * (Real.sin x) ^ 2))
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall cotangent_factor_numerator_hasDerivAt)
    (Eventually.of_forall cotangent_factor_denominator_hasDerivAt)
    cotangent_eventual_denominator_derivative_ne_zero
  · simpa only [zero_mul, Real.sin_zero, sub_zero] using
      (cotangent_factor_numerator_hasDerivAt 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · simpa only [zero_mul] using
      (cotangent_factor_denominator_hasDerivAt 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · exact cotangent_factor_derivative_quotient_tendsto


theorem cotangent_square_sub_inverse_square_factorization {x : ℝ}
    (hx : x ≠ 0) (hs : Real.sin x ≠ 0) :
    (Real.cot x) ^ 2 - 1 / x ^ 2 =
      (Real.cos x + Real.sin x / x) *
        ((x * Real.cos x - Real.sin x) / (x * (Real.sin x) ^ 2)) := by
  calc
    (Real.cot x) ^ 2 - 1 / x ^ 2 =
        (x ^ 2 * (Real.cos x) ^ 2 - (Real.sin x) ^ 2) /
          (x ^ 2 * (Real.sin x) ^ 2) := by
      rw [Real.cot_eq_cos_div_sin]
      field_simp [hx, hs]
    _ = ((x * Real.cos x + Real.sin x) / x) *
        ((x * Real.cos x - Real.sin x) / (x * (Real.sin x) ^ 2)) := by
      field_simp [hx, hs]
      ring
    _ = _ := by
      field_simp [hx, hs]

/-- Ví dụ 4.4.9: `cot²x − 1/x² → −2/3` khi `x → 0`. -/
theorem cotangent_square_sub_inverse_square_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.cot x) ^ 2 - 1 / x ^ 2)
      (𝓝[≠] 0) (𝓝 (-2 / 3 : ℝ)) := by
  have hc : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hfirst : Tendsto (fun x : ℝ ↦ Real.cos x + Real.sin x / x)
      (𝓝[≠] 0) (𝓝 2) := by
    simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hc.add sine_div_identity_tendsto_one
  have h := hfirst.mul cotangent_second_factor_tendsto
  have hvalue : (2 : ℝ) * (-1 / 3) = -2 / 3 := by norm_num
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_identity_ne_zero, eventually_sine_ne_zero] with x hx hs
  exact (cotangent_square_sub_inverse_square_factorization hx hs).symm

end calculus.Chapter04.Section04OscillatoryCotangentExamples
