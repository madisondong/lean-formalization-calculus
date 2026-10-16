import calculus.Chapter04.Section04ElementaryLimitExamples
import calculus.Chapter04.Section04OscillatoryCotangentExamples
import calculus.Chapter03.Section01Powers
import calculus.Chapter03.Section02OneSided
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# §4.4 Bài 3(b): giới hạn lũy thừa với thương đạo hàm dao động

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1690–1694. Xét thương `log B/(1/x)`; thương đạo hàm không có giới hạn hữu hạn hay vô cùng.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04OscillatingPowerLHospitalExercise
open calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section02
open calculus.Chapter03.Section02OneSided
open calculus.Chapter04.Section04ElementaryLimitExamples
open calculus.Chapter04.Section04OscillatoryCotangentExamples


def oscillatingPowerBase (x : ℝ) : ℝ :=
  2 * Real.sin (Real.sqrt x) + Real.sqrt x * Real.sin (1 / x)

/-- Miền xác định của căn bậc hai, `1/x` và lũy thừa thực theo từng loại số mũ. -/
def oscillatingPowerDomain : Set ℝ :=
  {x | 0 ≤ x ∧ x ≠ 0 ∧ oscillatingPowerBase x ∈ realPowerDomain x}


def oscillatingPowerNormalizedFactor (x : ℝ) : ℝ :=
  2 * Real.sin (Real.sqrt x) / Real.sqrt x + Real.sin (1 / x)


def oscillatingPowerBaseDerivative (x : ℝ) : ℝ :=
  2 * (Real.cos (Real.sqrt x) * (1 / (2 * Real.sqrt x))) +
    ((1 / (2 * Real.sqrt x)) * Real.sin (1 / x) +
      Real.sqrt x * (Real.cos (1 / x) * (-1 / x ^ 2)))


def oscillatingPowerLogDerivativeRatio (x : ℝ) : ℝ :=
  deriv (fun y : ℝ ↦ Real.log (oscillatingPowerBase y)) x /
    deriv (fun y : ℝ ↦ 1 / y) x


def oscillatingPowerNormalizedDerivativeRatio (x : ℝ) : ℝ :=
  (Real.cos (1 / x) - x * Real.cos (Real.sqrt x) -
    (x / 2) * Real.sin (1 / x)) / oscillatingPowerNormalizedFactor x


theorem oscillating_power_sqrt_right_tendsto :
    Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [Real.sqrt_zero] using!
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact Real.sqrt_pos.2 hx

theorem oscillating_power_sine_sqrt_quotient_tendsto_one :
    Tendsto (fun x : ℝ ↦ Real.sin (Real.sqrt x) / Real.sqrt x)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa only [Function.comp_def] using!
    (sine_div_identity_tendsto_one.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))).comp
      oscillating_power_sqrt_right_tendsto


theorem oscillating_power_factor_eventual_bounds :
    ∀ᶠ x : ℝ in 𝓝[>] 0,
      (1 / 2 : ℝ) < oscillatingPowerNormalizedFactor x ∧
        oscillatingPowerNormalizedFactor x < 4 := by
  have hs : ∀ᶠ x : ℝ in 𝓝[>] 0,
      (3 / 4 : ℝ) < Real.sin (Real.sqrt x) / Real.sqrt x ∧
        Real.sin (Real.sqrt x) / Real.sqrt x < 3 / 2 :=
    oscillating_power_sine_sqrt_quotient_tendsto_one.eventually
      (Ioo_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
  filter_upwards [hs] with x hx
  unfold oscillatingPowerNormalizedFactor
  simp only [mul_div_assoc]
  constructor
  · linarith [Real.neg_one_le_sin (1 / x), hx.1]
  · linarith [Real.sin_le_one (1 / x), hx.2]

theorem oscillating_power_base_factorization {x : ℝ} (hx : 0 < x) :
    oscillatingPowerBase x = Real.sqrt x * oscillatingPowerNormalizedFactor x := by
  have ht : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  unfold oscillatingPowerBase oscillatingPowerNormalizedFactor
  rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ ht]

theorem oscillating_power_base_eventually_positive :
    ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < oscillatingPowerBase x := by
  filter_upwards [self_mem_nhdsWithin, oscillating_power_factor_eventual_bounds]
    with x (hx : 0 < x) hU
  rw [oscillating_power_base_factorization hx]
  exact mul_pos (Real.sqrt_pos.2 hx) (by linarith [hU.1])


theorem oscillating_power_identity_mul_log_factor_tendsto_zero :
    Tendsto (fun x : ℝ ↦ x * Real.log (oscillatingPowerNormalizedFactor x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C : ℝ := |Real.log (1 / 2 : ℝ)| + |Real.log (4 : ℝ)|
  have hxlim : Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ |x| * C) _
    (by simpa only [abs_zero, zero_mul] using! hxlim.abs.mul_const C)
  filter_upwards [oscillating_power_factor_eventual_bounds] with x hU
  have hu : 0 < oscillatingPowerNormalizedFactor x := by linarith [hU.1]
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hU.1.le
  have hh := Real.log_le_log hu hU.2.le
  have habs : |Real.log (oscillatingPowerNormalizedFactor x)| ≤ C := by
    apply abs_le.mpr
    constructor
    · dsimp only [C]
      linarith [neg_abs_le (Real.log (1 / 2 : ℝ)), abs_nonneg (Real.log (4 : ℝ))]
    · dsimp only [C]
      linarith [le_abs_self (Real.log (4 : ℝ)), abs_nonneg (Real.log (1 / 2 : ℝ))]
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_left habs (abs_nonneg x)


theorem oscillating_power_identity_mul_log_base_tendsto_zero :
    Tendsto (fun x : ℝ ↦ x * Real.log (oscillatingPowerBase x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsum : Tendsto (fun x : ℝ ↦ (x * Real.log x) / 2 +
      x * Real.log (oscillatingPowerNormalizedFactor x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_div, zero_add] using!
      (source_identity_mul_log_right.div_const 2).add
        oscillating_power_identity_mul_log_factor_tendsto_zero
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, oscillating_power_factor_eventual_bounds]
    with x (hx : 0 < x) hU
  have hu : 0 < oscillatingPowerNormalizedFactor x := by linarith [hU.1]
  rw [oscillating_power_base_factorization hx,
    Real.log_mul (Real.sqrt_pos.2 hx).ne' hu.ne', Real.log_sqrt hx.le]
  ring

theorem oscillating_power_right_tendsto_one :
    Tendsto (fun x : ℝ ↦ (oscillatingPowerBase x) ^ x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h : Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log (oscillatingPowerBase x)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using!
      Real.continuous_exp.continuousAt.tendsto.comp
        oscillating_power_identity_mul_log_base_tendsto_zero
  apply h.congr'
  filter_upwards [oscillating_power_base_eventually_positive] with x hx
  rw [Real.rpow_def_of_pos hx, mul_comm]

theorem oscillating_power_eventual_full_source_domain :
    ∀ᶠ x : ℝ in 𝓝[>] 0, x ∈ oscillatingPowerDomain := by
  filter_upwards [self_mem_nhdsWithin, oscillating_power_base_eventually_positive]
    with x (hx : 0 < x) hb
  refine ⟨hx.le, hx.ne', ?_⟩
  unfold realPowerDomain
  split_ifs
  · exact mem_univ _
  · exact hb


theorem source_oscillating_power_right_limit :
    DomainRightLimit oscillatingPowerDomain
      (fun x : ℝ ↦ (oscillatingPowerBase x) ^ x) 0 1 := by
  have hfilter : 𝓝[oscillatingPowerDomain ∩ Ioi (0 : ℝ)] 0 = 𝓝[>] 0 :=
    nhdsWithin_inter_of_mem oscillating_power_eventual_full_source_domain
  have hacc : RightAccumulationPointOf oscillatingPowerDomain 0 := by
    intro δ hδ
    obtain ⟨x, hD, hx⟩ := (oscillating_power_eventual_full_source_domain.and
      (Ioo_mem_nhdsGT hδ)).exists
    exact ⟨x, hD, hx.1, by simpa only [zero_add] using hx.2⟩
  apply (domainRightLimit_iff_tendsto hacc).mpr
  rw [hfilter]
  exact oscillating_power_right_tendsto_one


theorem oscillating_power_base_has_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt oscillatingPowerBase (oscillatingPowerBaseDerivative x) x := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have hinv : HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, id_eq] using! (hasDerivAt_id x).fun_inv hx.ne'
  have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin (1 / y))
      (Real.cos (1 / x) * (-1 / x ^ 2)) x :=
    (Real.hasDerivAt_sin (1 / x)).comp x hinv
  simpa only [oscillatingPowerBase, oscillatingPowerBaseDerivative] using!
    (hsqrt.sin.const_mul 2).fun_add (hsqrt.fun_mul hsin)


theorem oscillating_power_eventual_logarithmic_actual_derivatives :
    ∀ᶠ x : ℝ in 𝓝[>] 0,
      HasDerivAt (fun y : ℝ ↦ Real.log (oscillatingPowerBase y))
        (oscillatingPowerBaseDerivative x / oscillatingPowerBase x) x ∧
      HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x ∧ (-1 / x ^ 2) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin, oscillating_power_base_eventually_positive]
    with x (hx : 0 < x) hb
  have hinv : HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, id_eq] using! (hasDerivAt_id x).fun_inv hx.ne'
  exact ⟨(oscillating_power_base_has_deriv hx).log hb.ne', hinv,
    div_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) (pow_ne_zero 2 hx.ne')⟩


theorem oscillating_power_actual_derivative_ratio_formula {x : ℝ}
    (hx : 0 < x) (hU : 0 < oscillatingPowerNormalizedFactor x) :
    oscillatingPowerLogDerivativeRatio x = oscillatingPowerNormalizedDerivativeRatio x := by
  have ht : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hb : 0 < oscillatingPowerBase x := by
    rw [oscillating_power_base_factorization hx]
    exact mul_pos (Real.sqrt_pos.2 hx) hU
  have hlog := (oscillating_power_base_has_deriv hx).log hb.ne'
  have hinv : HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, id_eq] using! (hasDerivAt_id x).fun_inv hx.ne'
  unfold oscillatingPowerLogDerivativeRatio
  rw [hlog.deriv, hinv.deriv, oscillating_power_base_factorization hx]
  unfold oscillatingPowerBaseDerivative oscillatingPowerNormalizedDerivativeRatio
  have hsquare := Real.sq_sqrt hx.le
  generalize oscillatingPowerNormalizedFactor x = u at hU ⊢
  generalize Real.cos (1 / x) = a
  generalize Real.cos (Real.sqrt x) = b
  generalize Real.sin (1 / x) = d
  generalize Real.sqrt x = t at ht hsquare ⊢
  rw [← hsquare]
  field_simp [ht, hU.ne']
  ring

theorem oscillating_power_eventual_actual_derivative_ratio :
    ∀ᶠ x : ℝ in 𝓝[>] 0,
      oscillatingPowerLogDerivativeRatio x = oscillatingPowerNormalizedDerivativeRatio x := by
  filter_upwards [self_mem_nhdsWithin, oscillating_power_factor_eventual_bounds]
    with x (hx : 0 < x) hU
  exact oscillating_power_actual_derivative_ratio_formula hx (by linarith [hU.1])


theorem oscillating_power_identity_mul_cosine_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ ↦ x * Real.cos (Real.sqrt x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm (a := fun x : ℝ ↦ |x|)
  · intro x
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (Real.sqrt x)) (abs_nonneg x)
  · simpa only [abs_zero] using!
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).abs

theorem oscillating_power_even_sequence_right_tendsto :
    Tendsto evenReciprocalSequence atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhds_of_tendsto_nhdsWithin
    evenReciprocalSequence_tendsto_zero, Eventually.of_forall evenReciprocalSequence_positive⟩

theorem oscillating_power_odd_sequence_right_tendsto :
    Tendsto oddReciprocalSequence atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhds_of_tendsto_nhdsWithin
    oddReciprocalSequence_tendsto_zero, Eventually.of_forall oddReciprocalSequence_positive⟩


theorem oscillating_power_even_normalized_ratio_value (n : ℕ) :
    oscillatingPowerNormalizedDerivativeRatio (evenReciprocalSequence n) =
      (1 - evenReciprocalSequence n * Real.cos (Real.sqrt (evenReciprocalSequence n))) /
        (2 * (Real.sin (Real.sqrt (evenReciprocalSequence n)) / Real.sqrt (evenReciprocalSequence n))) := by
  have hs : Real.sin (1 / evenReciprocalSequence n) = 0 := by
    simpa only [evenReciprocalSequence, one_div, inv_inv, zero_add, Real.sin_zero] using
      Real.sin_add_nat_mul_two_pi 0 (n + 1)
  have hc : Real.cos (1 / evenReciprocalSequence n) = 1 := by
    simp only [evenReciprocalSequence, one_div, inv_inv, Real.cos_nat_mul_two_pi]
  unfold oscillatingPowerNormalizedDerivativeRatio oscillatingPowerNormalizedFactor
  rw [hs, hc]
  simp only [mul_zero, sub_zero, add_zero, mul_div_assoc]


theorem oscillating_power_odd_normalized_ratio_value (n : ℕ) :
    oscillatingPowerNormalizedDerivativeRatio (oddReciprocalSequence n) =
      (-1 - oddReciprocalSequence n * Real.cos (Real.sqrt (oddReciprocalSequence n))) /
        (2 * (Real.sin (Real.sqrt (oddReciprocalSequence n)) / Real.sqrt (oddReciprocalSequence n))) := by
  have hs : Real.sin (1 / oddReciprocalSequence n) = 0 := by
    simp only [oddReciprocalSequence, one_div, inv_inv, Real.sin_add_nat_mul_two_pi, Real.sin_pi]
  have hc : Real.cos (1 / oddReciprocalSequence n) = -1 := by
    simp only [oddReciprocalSequence, one_div, inv_inv, Real.cos_add_nat_mul_two_pi, Real.cos_pi]
  unfold oscillatingPowerNormalizedDerivativeRatio oscillatingPowerNormalizedFactor
  rw [hs, hc]
  simp only [mul_zero, sub_zero, add_zero, mul_div_assoc]

theorem oscillating_power_actual_ratio_even_tendsto_half :
    Tendsto (fun n : ℕ ↦ oscillatingPowerLogDerivativeRatio (evenReciprocalSequence n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hn := (oscillating_power_identity_mul_cosine_sqrt_tendsto_zero.comp
    oscillating_power_even_sequence_right_tendsto).const_sub 1
  have hd := (oscillating_power_sine_sqrt_quotient_tendsto_one.comp
    oscillating_power_even_sequence_right_tendsto).const_mul 2
  have hq : Tendsto (fun n : ℕ ↦ oscillatingPowerNormalizedDerivativeRatio (evenReciprocalSequence n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simp_rw [oscillating_power_even_normalized_ratio_value]
    simpa only [Function.comp_def, sub_zero, mul_one] using! hn.div hd (by norm_num)
  apply hq.congr'
  exact (oscillating_power_even_sequence_right_tendsto.eventually
    oscillating_power_eventual_actual_derivative_ratio).mono (fun _ h ↦ h.symm)

theorem oscillating_power_actual_ratio_odd_tendsto_negative_half :
    Tendsto (fun n : ℕ ↦ oscillatingPowerLogDerivativeRatio (oddReciprocalSequence n))
      atTop (𝓝 (-1 / 2 : ℝ)) := by
  have hn := (oscillating_power_identity_mul_cosine_sqrt_tendsto_zero.comp
    oscillating_power_odd_sequence_right_tendsto).const_sub (-1)
  have hd := (oscillating_power_sine_sqrt_quotient_tendsto_one.comp
    oscillating_power_odd_sequence_right_tendsto).const_mul 2
  have hq : Tendsto (fun n : ℕ ↦ oscillatingPowerNormalizedDerivativeRatio (oddReciprocalSequence n))
      atTop (𝓝 (-1 / 2 : ℝ)) := by
    simp_rw [oscillating_power_odd_normalized_ratio_value]
    simpa only [Function.comp_def, sub_zero, mul_one] using! hn.div hd (by norm_num)
  apply hq.congr'
  exact (oscillating_power_odd_sequence_right_tendsto.eventually
    oscillating_power_eventual_actual_derivative_ratio).mono (fun _ h ↦ h.symm)

theorem oscillating_power_actual_derivative_ratio_no_finite_limit :
    ¬ ∃ L : ℝ, Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have he : (1 / 2 : ℝ) = L := tendsto_nhds_unique
    oscillating_power_actual_ratio_even_tendsto_half (hL.comp oscillating_power_even_sequence_right_tendsto)
  have ho : (-1 / 2 : ℝ) = L := tendsto_nhds_unique
    oscillating_power_actual_ratio_odd_tendsto_negative_half (hL.comp oscillating_power_odd_sequence_right_tendsto)
  linarith

theorem oscillating_power_actual_derivative_ratio_no_infinite_limit :
    ¬ Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) atTop ∧
      ¬ Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) atBot := by
  constructor
  · intro h
    exact (not_tendsto_atTop_of_tendsto_nhds oscillating_power_actual_ratio_even_tendsto_half)
      (h.comp oscillating_power_even_sequence_right_tendsto)
  · intro h
    exact (not_tendsto_atBot_of_tendsto_nhds oscillating_power_actual_ratio_even_tendsto_half)
      (h.comp oscillating_power_even_sequence_right_tendsto)


theorem oscillating_power_logarithmic_numerator_denominator_infinite :
    Tendsto (fun x : ℝ ↦ Real.log (oscillatingPowerBase x)) (𝓝[>] (0 : ℝ)) atBot ∧
      Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] (0 : ℝ)) atTop := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhds_of_tendsto_nhdsWithin oscillating_power_sqrt_right_tendsto
  have hsine : Tendsto (fun x : ℝ ↦ Real.sin (Real.sqrt x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero] using! Real.continuous_sin.continuousAt.tendsto.comp hsqrt
  have hnoise : Tendsto (fun x : ℝ ↦ Real.sqrt x * Real.sin (1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun x : ℝ ↦ |Real.sqrt x|)
    · intro x
      simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg (Real.sqrt x))
    · simpa only [abs_zero] using! hsqrt.abs
  have hb : Tendsto oscillatingPowerBase (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [oscillatingPowerBase, mul_zero, zero_add] using! (hsine.const_mul 2).add hnoise
  have hbRight : Tendsto oscillatingPowerBase (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb, oscillating_power_base_eventually_positive⟩
  refine ⟨?_, reciprocal_right_atTop⟩
  simpa only [Function.comp_def] using! Real.tendsto_log_nhdsGT_zero.comp hbRight

/-- Bài 3(b): giới hạn lũy thừa bằng 1, nhưng thương đạo hàm không có giới hạn hữu hạn hay vô cùng. -/
theorem source_oscillating_power_lhospital_answer :
    DomainRightLimit oscillatingPowerDomain
      (fun x : ℝ ↦ (oscillatingPowerBase x) ^ x) 0 1 ∧
    (Tendsto (fun x : ℝ ↦ Real.log (oscillatingPowerBase x)) (𝓝[>] (0 : ℝ)) atBot ∧
      Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] (0 : ℝ)) atTop) ∧
    (∀ᶠ x : ℝ in 𝓝[>] 0,
      HasDerivAt (fun y : ℝ ↦ Real.log (oscillatingPowerBase y))
        (oscillatingPowerBaseDerivative x / oscillatingPowerBase x) x ∧
      HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x ∧ (-1 / x ^ 2) ≠ 0) ∧
    (¬ ∃ L : ℝ, Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    ¬ Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) atTop ∧
      ¬ Tendsto oscillatingPowerLogDerivativeRatio (𝓝[>] (0 : ℝ)) atBot := by
  exact ⟨source_oscillating_power_right_limit,
    oscillating_power_logarithmic_numerator_denominator_infinite,
    oscillating_power_eventual_logarithmic_actual_derivatives,
    oscillating_power_actual_derivative_ratio_no_finite_limit,
    oscillating_power_actual_derivative_ratio_no_infinite_limit.1,
    oscillating_power_actual_derivative_ratio_no_infinite_limit.2⟩

end calculus.Chapter04.Section04OscillatingPowerLHospitalExercise
