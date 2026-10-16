import calculus.Chapter04.Section03DerivativeRatioExercises
import calculus.Chapter03.Section02Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 3(a): thương có giới hạn, thương đạo hàm không có giới hạn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1690–1693.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04OscillatingDerivativeRatioExercise
open calculus.Chapter04.Section03DerivativeRatioExercises
open calculus.Chapter03.Section02Infinite


def oscillatingRatioDomain : Set ℝ := {x | 2 * x + Real.sin x ≠ 0}


theorem oscillating_ratio_actual_derivatives (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y - Real.sin y) (1 - Real.cos x) x ∧
    HasDerivAt (fun y : ℝ ↦ 2 * y + Real.sin y) (2 + Real.cos x) x ∧
    0 < 2 + Real.cos x := by
  refine ⟨(hasDerivAt_id x).fun_sub (Real.hasDerivAt_sin x), ?_, ?_⟩
  · simpa using! ((hasDerivAt_id x).const_mul 2).fun_add (Real.hasDerivAt_sin x)
  · linarith [Real.neg_one_le_cos x]


theorem oscillating_ratio_numerator_denominator_atTop :
    Tendsto (fun x : ℝ ↦ x - Real.sin x) atTop atTop ∧
    Tendsto (fun x : ℝ ↦ 2 * x + Real.sin x) atTop atTop := by
  constructor
  · apply tendsto_atTop_mono (fun x : ℝ ↦ ?_)
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    dsimp only [id_eq]
    linarith [Real.sin_le_one x]
  · apply tendsto_atTop_mono (fun x : ℝ ↦ ?_)
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    dsimp only [id_eq]
    linarith [Real.neg_one_le_sin x]


theorem oscillating_derivative_ratio_no_finite_limit :
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x))
      atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h0 : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 L) := by
    simpa only [Function.comp_def, twoPiSequence, Real.cos_nat_mul_two_pi,
      sub_self, zero_div] using hL.comp twoPiSequence_tendsto_atTop
  have h2 : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 L) := by
    simpa only [Function.comp_def, oddPiSequence, Real.cos_add_nat_mul_two_pi,
      Real.cos_pi, sub_neg_eq_add, show (1 : ℝ) + 1 = 2 by norm_num,
      show (2 : ℝ) + -1 = 1 by norm_num, div_one] using hL.comp oddPiSequence_tendsto_atTop
  have hz : (0 : ℝ) = L := tendsto_nhds_unique tendsto_const_nhds h0
  have ht : (2 : ℝ) = L := tendsto_nhds_unique tendsto_const_nhds h2
  linarith


theorem oscillating_derivative_ratio_bounds (x : ℝ) :
    0 ≤ (1 - Real.cos x) / (2 + Real.cos x) ∧
      (1 - Real.cos x) / (2 + Real.cos x) ≤ 2 := by
  have hp : 0 < 2 + Real.cos x := by linarith [Real.neg_one_le_cos x]
  constructor
  · exact div_nonneg (by linarith [Real.cos_le_one x]) hp.le
  · apply (div_le_iff₀ hp).mpr
    linarith [Real.neg_one_le_cos x]


theorem oscillating_derivative_ratio_no_infinite_limit :
    ¬ Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x)) atTop atTop ∧
    ¬ Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x)) atTop atBot := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (h.eventually (eventually_gt_atTop (2 : ℝ))).exists
    exact (not_lt_of_ge (oscillating_derivative_ratio_bounds x).2) hx
  · intro h
    obtain ⟨x, hx⟩ := (h.eventually (eventually_lt_atBot (0 : ℝ))).exists
    exact (not_lt_of_ge (oscillating_derivative_ratio_bounds x).1) hx

/-- Bài 3(a): giới hạn bằng `1/2`, nhưng thương đạo hàm không có giới hạn. -/
theorem source_oscillating_ratio_answer :
    DomainAtTopLimit oscillatingRatioDomain
      (fun x : ℝ ↦ (x - Real.sin x) / (2 * x + Real.sin x)) (1 / 2) ∧
    (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ y - Real.sin y) (1 - Real.cos x) x ∧
      HasDerivAt (fun y : ℝ ↦ 2 * y + Real.sin y) (2 + Real.cos x) x ∧
      0 < 2 + Real.cos x) ∧
    (Tendsto (fun x : ℝ ↦ x - Real.sin x) atTop atTop ∧
      Tendsto (fun x : ℝ ↦ 2 * x + Real.sin x) atTop atTop) ∧
    (¬ ∃ L : ℝ, Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x))
      atTop (𝓝 L)) ∧
    ¬ Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x)) atTop atTop ∧
    ¬ Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (2 + Real.cos x)) atTop atBot := by
  refine ⟨?_, oscillating_ratio_actual_derivatives,
    oscillating_ratio_numerator_denominator_atTop, oscillating_derivative_ratio_no_finite_limit,
    oscillating_derivative_ratio_no_infinite_limit.1, oscillating_derivative_ratio_no_infinite_limit.2⟩
  have hn := sine_div_identity_tendsto_zero.const_sub 1
  have hd := sine_div_identity_tendsto_zero.const_add 2
  have ht : Tendsto (fun x : ℝ ↦ (1 - Real.sin x / x) / (2 + Real.sin x / x))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [sub_zero, add_zero] using! hn.div hd (by norm_num)
  have hD : ∀ᶠ x : ℝ in atTop, x ∈ oscillatingRatioDomain := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change 2 * x + Real.sin x ≠ 0
    have hp : 0 < 2 * x + Real.sin x := by linarith [Real.neg_one_le_sin x]
    exact hp.ne'
  have hU : ¬ BddAbove oscillatingRatioDomain := by
    rw [not_bddAbove_iff]
    intro M
    exact (hD.and (eventually_gt_atTop M)).exists
  apply (domainAtTopLimit_iff_tendsto hU).mpr
  apply (ht.mono_left inf_le_left).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℝ)).filter_mono inf_le_left] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hp : 2 * x + Real.sin x ≠ 0 := by
    have hh : 0 < 2 * x + Real.sin x := by linarith [Real.neg_one_le_sin x]
    exact hh.ne'
  have hn : 2 + Real.sin x / x ≠ 0 := by
    intro he
    apply hp
    have hm := congrArg (fun z : ℝ ↦ z * x) he
    field_simp [hx0] at hm
    linarith
  field_simp [hx0, hp, hn]

end calculus.Chapter04.Section04OscillatingDerivativeRatioExercise
