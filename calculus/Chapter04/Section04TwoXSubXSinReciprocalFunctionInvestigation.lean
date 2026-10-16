import calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport
import calculus.Chapter04.Section01OscillatingExercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp

/-!
# Bài 4.4.12(a): khảo sát hàm 2x−x sin(1/x)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2734–2740.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04TwoXSubXSinReciprocalFunctionInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03 calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport
open calculus.Chapter04.Section01OscillatingExercises


def twoXSubXSinReciprocal (x : ℝ) : ℝ := 2 * x - linearSineReciprocal x


def twoXSubXSinReciprocalFirstDeriv (x : ℝ) : ℝ := 2 - Real.sin (1 / x) + Real.cos (1 / x) / x


def twoXSubXSinReciprocalSecondDeriv (x : ℝ) : ℝ := Real.sin (1 / x) / x ^ 3


def twoXSubXSinReciprocalThirdDeriv (x : ℝ) : ℝ :=
  -(3 * Real.sin (1 / x) + Real.cos (1 / x) / x) / x ^ 4

theorem twoXSubXSinReciprocal_eq_source (x : ℝ) :
    twoXSubXSinReciprocal x = if x = 0 then 0 else x * (2 - Real.sin (1 / x)) := by
  by_cases hx : x = 0
  · simp [hx, twoXSubXSinReciprocal, linearSineReciprocal]
  · simp only [twoXSubXSinReciprocal, linearSineReciprocal, if_neg hx]
    ring

theorem twoXSubXSinReciprocal_zero : twoXSubXSinReciprocal 0 = 0 := by
  simp [twoXSubXSinReciprocal, linearSineReciprocal]

theorem twoXSubXSinReciprocal_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt twoXSubXSinReciprocal (twoXSubXSinReciprocalFirstDeriv x) x := by
  have h := ((hasDerivAt_id x).const_mul (2 : ℝ)).sub (linear_hasDerivAt_nonzero x hx)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp only [twoXSubXSinReciprocalFirstDeriv]
  ring

theorem twoXSubXSinReciprocal_differentiableAt_iff (x : ℝ) :
    DifferentiableAt ℝ twoXSubXSinReciprocal x ↔ x ≠ 0 := by
  constructor
  · intro h
    apply (linear_differentiableAt_iff x).mp
    have h' := ((differentiableAt_id.const_mul (2 : ℝ)).sub h)
    apply h'.congr_of_eventuallyEq
    exact Eventually.of_forall fun y ↦ by dsimp [twoXSubXSinReciprocal]; ring
  · intro hx
    exact (twoXSubXSinReciprocal_hasDerivAt x hx).differentiableAt

theorem twoXSubXSinReciprocal_bound (x : ℝ) : |twoXSubXSinReciprocal x| ≤ 3 * |x| := by
  by_cases hx : x = 0
  · simp [hx, twoXSubXSinReciprocal_zero]
  rw [twoXSubXSinReciprocal_eq_source, if_neg hx, abs_mul]
  have hf : |2 - Real.sin (1 / x)| ≤ 3 := by
    calc
      |2 - Real.sin (1 / x)| ≤ |(2 : ℝ)| + |Real.sin (1 / x)| := abs_sub _ _
      _ ≤ 3 := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.abs_sin_le_one (1 / x)]
  nlinarith [mul_le_mul_of_nonneg_left hf (abs_nonneg x)]

theorem twoXSubXSinReciprocal_continuousAt_zero : ContinuousAt twoXSubXSinReciprocal 0 := by
  have hb : Tendsto (fun x : ℝ ↦ 3 * |x|) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_abs : Continuous (abs : ℝ → ℝ)).const_mul 3).tendsto 0
  have ha : Tendsto (fun x : ℝ ↦ |twoXSubXSinReciprocal x|) (𝓝 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Eventually.of_forall twoXSubXSinReciprocal_bound) hb
  change Tendsto twoXSubXSinReciprocal (𝓝 0) (𝓝 (twoXSubXSinReciprocal 0))
  rw [twoXSubXSinReciprocal_zero]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using ha)

theorem twoXSubXSinReciprocalFirstDeriv_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt twoXSubXSinReciprocalFirstDeriv (twoXSubXSinReciprocalSecondDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have hs := (Real.hasDerivAt_sin (1 / x)).comp x hi
  have hc := (Real.hasDerivAt_cos (1 / x)).comp x hi
  have h := ((hasDerivAt_const x (2 : ℝ)).sub hs).add (hc.div (hasDerivAt_id x) hx)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  dsimp [twoXSubXSinReciprocalSecondDeriv]
  field_simp [hx]
  ring

theorem twoXSubXSinReciprocalSecondDeriv_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt twoXSubXSinReciprocalSecondDeriv (twoXSubXSinReciprocalThirdDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have hs := (Real.hasDerivAt_sin (1 / x)).comp x hi
  have h := hs.div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  dsimp [twoXSubXSinReciprocalThirdDeriv]
  field_simp [hx]
  ring


theorem twoXSubXSinReciprocal_sign (x : ℝ) :
    (0 < x → 0 < twoXSubXSinReciprocal x) ∧ (x < 0 → twoXSubXSinReciprocal x < 0) := by
  have hf : 0 < 2 - Real.sin (1 / x) := by linarith [Real.sin_le_one (1 / x)]
  constructor
  · intro hx
    rw [twoXSubXSinReciprocal_eq_source, if_neg hx.ne']
    exact mul_pos hx hf
  · intro hx
    rw [twoXSubXSinReciprocal_eq_source, if_neg hx.ne]
    exact mul_neg_of_neg_of_pos hx hf

theorem twoXSubXSinReciprocal_no_extremum_zero :
    ¬ IsLocalMinimumOn twoXSubXSinReciprocal univ 0 ∧ ¬ IsLocalMaximumOn twoXSubXSinReciprocal univ 0 := by
  have hl : ∀ᶠ x : ℝ in 𝓝[<] 0, twoXSubXSinReciprocal x < 0 :=
    Filter.Eventually.mono (f := 𝓝[<] (0 : ℝ)) (p := fun x : ℝ ↦ x < 0)
      (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[<] 0, x < 0)
      (fun x hx ↦ (twoXSubXSinReciprocal_sign x).2 hx)
  have hr : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < twoXSubXSinReciprocal x :=
    Filter.Eventually.mono (f := 𝓝[>] (0 : ℝ)) (p := fun x : ℝ ↦ 0 < x)
      (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x)
      (fun x hx ↦ (twoXSubXSinReciprocal_sign x).1 hx)
  constructor
  · intro hm
    have hm' := (source_minimum_univ_iff twoXSubXSinReciprocal 0).mp hm
    change ∀ᶠ x in 𝓝 (0 : ℝ), twoXSubXSinReciprocal 0 ≤ twoXSubXSinReciprocal x at hm'
    obtain ⟨x, hx, hneg⟩ := ((hm'.filter_mono nhdsWithin_le_nhds).and hl).exists
    rw [twoXSubXSinReciprocal_zero] at hx
    exact hneg.not_ge hx
  · intro hm
    have hm' := (source_maximum_univ_iff twoXSubXSinReciprocal 0).mp hm
    change ∀ᶠ x in 𝓝 (0 : ℝ), twoXSubXSinReciprocal x ≤ twoXSubXSinReciprocal 0 at hm'
    obtain ⟨x, hx, hpos⟩ := ((hm'.filter_mono nhdsWithin_le_nhds).and hr).exists
    rw [twoXSubXSinReciprocal_zero] at hx
    exact not_le_of_gt hpos hx


theorem twoXSubXSinReciprocal_stationary_sin_reciprocal_ne_zero {x : ℝ} (hz : twoXSubXSinReciprocalFirstDeriv x = 0) :
    Real.sin (1 / x) ≠ 0 := by
  intro hs
  have hcos : Real.cos (1 / x) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (1 / x)]
  have hp : (1 / x) * Real.cos (1 / x) = -2 := by
    dsimp [twoXSubXSinReciprocalFirstDeriv] at hz
    rw [hs] at hz
    have he : Real.cos (1 / x) / x = (1 / x) * Real.cos (1 / x) := by ring
    rw [he] at hz
    linarith
  have hsq : (1 / x) ^ 2 = (2 : ℝ) ^ 2 := by
    have h := congrArg (fun z : ℝ ↦ z ^ 2) hp
    rw [mul_pow, hcos] at h
    norm_num at h
    convert h using 1 <;> norm_num
  have hsin2 : 0 < Real.sin (2 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hp
  · rw [hp] at hs
    exact hsin2.ne' hs
  · rw [hp, Real.sin_neg] at hs
    linarith

theorem twoXSubXSinReciprocal_stationary_second_deriv_ne_zero {x : ℝ} (hx : x ≠ 0)
    (hz : twoXSubXSinReciprocalFirstDeriv x = 0) : twoXSubXSinReciprocalSecondDeriv x ≠ 0 := by
  exact div_ne_zero (twoXSubXSinReciprocal_stationary_sin_reciprocal_ne_zero hz) (pow_ne_zero 3 hx)


theorem twoXSubXSinReciprocal_extrema_iff (x : ℝ) :
    (IsLocalMinimumOn twoXSubXSinReciprocal univ x ↔
      x ≠ 0 ∧ twoXSubXSinReciprocalFirstDeriv x = 0 ∧ 0 < twoXSubXSinReciprocalSecondDeriv x) ∧
    (IsLocalMaximumOn twoXSubXSinReciprocal univ x ↔
      x ≠ 0 ∧ twoXSubXSinReciprocalFirstDeriv x = 0 ∧ twoXSubXSinReciprocalSecondDeriv x < 0) := by
  by_cases hx : x = 0
  · subst x
    constructor
    · constructor
      · intro hm; exact (twoXSubXSinReciprocal_no_extremum_zero.1 hm).elim
      · rintro ⟨hne, _⟩; exact (hne rfl).elim
    · constructor
      · intro hm; exact (twoXSubXSinReciprocal_no_extremum_zero.2 hm).elim
      · rintro ⟨hne, _⟩; exact (hne rfl).elim
  · have hs := second_hasDerivAt_off_zero twoXSubXSinReciprocal_hasDerivAt twoXSubXSinReciprocalFirstDeriv_hasDerivAt hx
    have hn : deriv twoXSubXSinReciprocal x = 0 → deriv (deriv twoXSubXSinReciprocal) x ≠ 0 := by
      intro hz
      rw [hs.deriv]
      apply twoXSubXSinReciprocal_stationary_second_deriv_ne_zero hx
      rwa [(twoXSubXSinReciprocal_hasDerivAt x hx).deriv] at hz
    have h := nondegenerate_extrema_iff (twoXSubXSinReciprocal_hasDerivAt x hx).differentiableAt hn
    rw [(twoXSubXSinReciprocal_hasDerivAt x hx).deriv, hs.deriv] at h
    exact ⟨⟨fun hm ↦ ⟨hx, h.1.mp hm⟩, fun hm ↦ h.1.mpr hm.2⟩,
      ⟨fun hM ↦ ⟨hx, h.2.mp hM⟩, fun hM ↦ h.2.mpr hM.2⟩⟩


theorem twoXSubXSinReciprocal_second_deriv_signs_oscillate_near_zero (b : ℝ) (hb : 0 < b) :
    (∃ u ∈ Ioo 0 b, 0 < twoXSubXSinReciprocalSecondDeriv u) ∧
      (∃ v ∈ Ioo 0 b, twoXSubXSinReciprocalSecondDeriv v < 0) := by
  have hp := (reciprocalPhase_tendsto_zero (Real.pi / 2)).eventually (eventually_lt_nhds hb)
  have hm := (reciprocalPhase_tendsto_zero (Real.pi / 2 + Real.pi)).eventually (eventually_lt_nhds hb)
  obtain ⟨n, hn, hn'⟩ := (hp.and hm).exists
  have hpos := reciprocalPhase_pos (by positivity : 0 < Real.pi / 2) n
  have hneg := reciprocalPhase_pos (by positivity : 0 < Real.pi / 2 + Real.pi) n
  constructor
  · refine ⟨reciprocalPhase (Real.pi / 2) n, ⟨hpos, hn⟩, ?_⟩
    rw [twoXSubXSinReciprocalSecondDeriv, (reciprocalPhase_trig (Real.pi / 2) n).1, Real.sin_pi_div_two]
    positivity
  · refine ⟨reciprocalPhase (Real.pi / 2 + Real.pi) n, ⟨hneg, hn'⟩, ?_⟩
    rw [twoXSubXSinReciprocalSecondDeriv, (reciprocalPhase_trig (Real.pi / 2 + Real.pi) n).1,
      Real.sin_add_pi, Real.sin_pi_div_two]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos hneg 3)

theorem twoXSubXSinReciprocal_convexity_intervals (a b : ℝ) :
    (ConvexOnOpenInterval twoXSubXSinReciprocal a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, 0 ≤ twoXSubXSinReciprocalSecondDeriv x) ∧
    (ConcaveOnOpenInterval twoXSubXSinReciprocal a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, twoXSubXSinReciprocalSecondDeriv x ≤ 0) :=
  convexity_intervals_iff_second_deriv_sign twoXSubXSinReciprocal_hasDerivAt twoXSubXSinReciprocalFirstDeriv_hasDerivAt
    twoXSubXSinReciprocal_second_deriv_signs_oscillate_near_zero a b

theorem twoXSubXSinReciprocal_second_deriv_zero_is_simple {x : ℝ} (hx : x ≠ 0)
    (hz : twoXSubXSinReciprocalSecondDeriv x = 0) : twoXSubXSinReciprocalThirdDeriv x ≠ 0 := by
  have hs : Real.sin (1 / x) = 0 := (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 3 hx)
  have hc : Real.cos (1 / x) ≠ 0 := by
    intro hc
    have h := Real.sin_sq_add_cos_sq (1 / x)
    rw [hs, hc] at h
    norm_num at h
  dsimp [twoXSubXSinReciprocalThirdDeriv]
  rw [hs]
  simp only [mul_zero, zero_add]
  exact div_ne_zero (neg_ne_zero.mpr (div_ne_zero hc hx)) (pow_ne_zero 4 hx)

theorem twoXSubXSinReciprocal_inflection_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn twoXSubXSinReciprocal a b x) ↔
      x ≠ 0 ∧ Real.sin (1 / x) = 0 := by
  have h := complete_inflection_points twoXSubXSinReciprocal_hasDerivAt twoXSubXSinReciprocalFirstDeriv_hasDerivAt
    twoXSubXSinReciprocalSecondDeriv_hasDerivAt twoXSubXSinReciprocal_second_deriv_signs_oscillate_near_zero
    (fun _ hx hz ↦ twoXSubXSinReciprocal_second_deriv_zero_is_simple hx hz) x
  constructor
  · intro hi
    obtain ⟨hx, hz⟩ := h.mp hi
    exact ⟨hx, (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 3 hx)⟩
  · rintro ⟨hx, hs⟩
    apply h.mpr
    refine ⟨hx, ?_⟩
    dsimp only [twoXSubXSinReciprocalSecondDeriv]
    rw [hs, zero_div]


theorem twoXSubXSinReciprocal_inflection_integer_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn twoXSubXSinReciprocal a b x) ↔
      ∃ n : ℤ, n ≠ 0 ∧ x = ((n : ℝ) * Real.pi)⁻¹ := by
  rw [twoXSubXSinReciprocal_inflection_iff]
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    have hn0 : n ≠ 0 := by
      intro h; subst n
      simp only [Int.cast_zero, zero_mul] at hn
      exact one_div_ne_zero hx hn.symm
    refine ⟨n, hn0, ?_⟩
    rw [hn]
    simp
  · rintro ⟨n, hn0, rfl⟩
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hnp : (n : ℝ) * Real.pi ≠ 0 := mul_ne_zero hn Real.pi_ne_zero
    refine ⟨inv_ne_zero hnp, ?_⟩
    simp only [one_div, inv_inv]
    exact Real.sin_int_mul_pi n


theorem exercise12_two_x_sub_x_sin_reciprocal_function_investigation :
    (∀ x : ℝ, twoXSubXSinReciprocal x = if x = 0 then 0 else x * (2 - Real.sin (1 / x))) ∧
    ContinuousAt twoXSubXSinReciprocal 0 ∧
    (∀ x : ℝ, DifferentiableAt ℝ twoXSubXSinReciprocal x ↔ x ≠ 0) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt twoXSubXSinReciprocal (twoXSubXSinReciprocalFirstDeriv x) x) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt (deriv twoXSubXSinReciprocal) (twoXSubXSinReciprocalSecondDeriv x) x) ∧
    (∀ x : ℝ, (IsLocalMinimumOn twoXSubXSinReciprocal univ x ↔
      x ≠ 0 ∧ twoXSubXSinReciprocalFirstDeriv x = 0 ∧ 0 < twoXSubXSinReciprocalSecondDeriv x) ∧
      (IsLocalMaximumOn twoXSubXSinReciprocal univ x ↔
      x ≠ 0 ∧ twoXSubXSinReciprocalFirstDeriv x = 0 ∧ twoXSubXSinReciprocalSecondDeriv x < 0)) ∧
    (∀ a b : ℝ, (ConvexOnOpenInterval twoXSubXSinReciprocal a b ↔
      0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, 0 ≤ twoXSubXSinReciprocalSecondDeriv x) ∧
      (ConcaveOnOpenInterval twoXSubXSinReciprocal a b ↔
      0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, twoXSubXSinReciprocalSecondDeriv x ≤ 0)) ∧
    (∀ x : ℝ, (∃ a b : ℝ, SourceInflectionOn twoXSubXSinReciprocal a b x) ↔
      ∃ n : ℤ, n ≠ 0 ∧ x = ((n : ℝ) * Real.pi)⁻¹) := by
  exact ⟨twoXSubXSinReciprocal_eq_source, twoXSubXSinReciprocal_continuousAt_zero,
    twoXSubXSinReciprocal_differentiableAt_iff, twoXSubXSinReciprocal_hasDerivAt,
    fun _ hx ↦ second_hasDerivAt_off_zero twoXSubXSinReciprocal_hasDerivAt twoXSubXSinReciprocalFirstDeriv_hasDerivAt hx,
    twoXSubXSinReciprocal_extrema_iff, twoXSubXSinReciprocal_convexity_intervals, twoXSubXSinReciprocal_inflection_integer_iff⟩

end calculus.Chapter04.Section04TwoXSubXSinReciprocalFunctionInvestigation
