import calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport
import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Bài 4.4.12(b): khảo sát hàm bình phương dao động

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2734–2746.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04SquareMulCosReciprocalSqFunctionInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03 calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport


def squareMulCosReciprocalSq (x : ℝ) : ℝ := if x = 0 then 0 else x ^ 2 * Real.cos (1 / x) ^ 2


def squareMulCosReciprocalSqFirstDeriv (x : ℝ) : ℝ :=
  2 * Real.cos (1 / x) * (x * Real.cos (1 / x) + Real.sin (1 / x))


def squareMulCosReciprocalSqSecondDeriv (x : ℝ) : ℝ :=
  2 * Real.cos (1 / x) ^ 2 + 4 * (1 / x) * Real.sin (1 / x) * Real.cos (1 / x) +
    2 * (1 / x) ^ 2 * (Real.sin (1 / x) ^ 2 - Real.cos (1 / x) ^ 2)


def squareMulCosReciprocalSqThirdDeriv (x : ℝ) : ℝ :=
  -8 * Real.sin (1 / x) * Real.cos (1 / x) / x ^ 4

theorem squareMulCosReciprocalSq_eq_source (x : ℝ) :
    squareMulCosReciprocalSq x = if x = 0 then 0 else x ^ 2 * Real.cos (1 / x) ^ 2 := rfl

theorem squareMulCosReciprocalSq_zero : squareMulCosReciprocalSq 0 = 0 := by simp [squareMulCosReciprocalSq]

theorem squareMulCosReciprocalSq_nonnegative (x : ℝ) : 0 ≤ squareMulCosReciprocalSq x := by
  by_cases hx : x = 0
  · simp [hx, squareMulCosReciprocalSq_zero]
  · rw [squareMulCosReciprocalSq, if_neg hx]
    exact mul_nonneg (sq_nonneg x) (sq_nonneg _)

theorem squareMulCosReciprocalSq_secant_slope_bound (x : ℝ) :
    |(squareMulCosReciprocalSq x - squareMulCosReciprocalSq 0) / (x - 0)| ≤ |x| := by
  by_cases hx : x = 0
  · simp [hx, squareMulCosReciprocalSq_zero]
  rw [squareMulCosReciprocalSq_zero, squareMulCosReciprocalSq, if_neg hx]
  simp only [sub_zero]
  have he : x ^ 2 * Real.cos (1 / x) ^ 2 / x = x * Real.cos (1 / x) ^ 2 := by
    field_simp [hx]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos (1 / x)))]
  have hc : Real.cos (1 / x) ^ 2 ≤ 1 := by
    have h := abs_le.mp (Real.abs_cos_le_one (1 / x))
    nlinarith [h.1, h.2]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (abs_nonneg x)

theorem squareMulCosReciprocalSq_hasDerivAt_zero : HasDerivAt squareMulCosReciprocalSq 0 0 := by
  have hb : Tendsto (fun x : ℝ ↦ |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using (continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {(0 : ℝ)}ᶜ))
  have ha := squeeze_zero' (Eventually.of_forall fun x : ℝ ↦
    abs_nonneg ((squareMulCosReciprocalSq x - squareMulCosReciprocalSq 0) / (x - 0)))
    (Eventually.of_forall squareMulCosReciprocalSq_secant_slope_bound) hb
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using ha)

theorem squareMulCosReciprocalSq_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt squareMulCosReciprocalSq (squareMulCosReciprocalSqFirstDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have hc := ((Real.hasDerivAt_cos (1 / x)).comp x hi).fun_pow 2
  have h := (hasDerivAt_pow 2 x).mul hc
  have he : squareMulCosReciprocalSq =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ 2 * Real.cos (1 / y) ^ 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact if_neg hy
  apply (h.congr_of_eventuallyEq he).congr_deriv
  dsimp [squareMulCosReciprocalSqFirstDeriv]
  field_simp [hx]

theorem squareMulCosReciprocalSq_differentiable : Differentiable ℝ squareMulCosReciprocalSq := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact squareMulCosReciprocalSq_hasDerivAt_zero.differentiableAt
  · exact (squareMulCosReciprocalSq_hasDerivAt x hx).differentiableAt

theorem squareMulCosReciprocalSqFirstDeriv_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt squareMulCosReciprocalSqFirstDeriv (squareMulCosReciprocalSqSecondDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have hc := (Real.hasDerivAt_cos (1 / x)).comp x hi
  have hs := (Real.hasDerivAt_sin (1 / x)).comp x hi
  have h := (hc.const_mul (2 : ℝ)).mul (((hasDerivAt_id x).mul hc).add hs)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  dsimp [squareMulCosReciprocalSqSecondDeriv]
  field_simp [hx]
  ring

theorem squareMulCosReciprocalSqSecondDeriv_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt squareMulCosReciprocalSqSecondDeriv (squareMulCosReciprocalSqThirdDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have hc := (Real.hasDerivAt_cos (1 / x)).comp x hi
  have hs := (Real.hasDerivAt_sin (1 / x)).comp x hi
  have h1 := (hc.fun_pow 2).const_mul (2 : ℝ)
  have h2 := (((hi.const_mul (4 : ℝ)).mul hs).mul hc)
  have h3 := ((hi.fun_pow 2).const_mul (2 : ℝ)).mul ((hs.fun_pow 2).sub (hc.fun_pow 2))
  apply (((h1.add h2).add h3).congr_of_eventuallyEq
    (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  dsimp [squareMulCosReciprocalSqThirdDeriv]
  field_simp [hx]
  ring


theorem squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero {x : ℝ} (hx : x ≠ 0)
    (hc : Real.cos (1 / x) = 0) : 0 < squareMulCosReciprocalSqSecondDeriv x := by
  have hs : Real.sin (1 / x) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (1 / x)]
  have hp : 0 < (1 / x) ^ 2 := sq_pos_of_ne_zero (one_div_ne_zero hx)
  dsimp [squareMulCosReciprocalSqSecondDeriv]
  rw [hc, hs]
  nlinarith

theorem squareMulCosReciprocalSq_stationary_factor_cos_reciprocal_ne_zero {x : ℝ}
    (hz : x * Real.cos (1 / x) + Real.sin (1 / x) = 0) : Real.cos (1 / x) ≠ 0 := by
  intro hc
  have hs : Real.sin (1 / x) = 0 := by simpa only [hc, mul_zero, zero_add] using hz
  have h := Real.sin_sq_add_cos_sq (1 / x)
  rw [hc, hs] at h
  norm_num at h


theorem squareMulCosReciprocalSq_second_deriv_neg_at_stationary_factor_zero {x : ℝ} (hx : x ≠ 0)
    (hz : x * Real.cos (1 / x) + Real.sin (1 / x) = 0) : squareMulCosReciprocalSqSecondDeriv x < 0 := by
  have hc := squareMulCosReciprocalSq_stationary_factor_cos_reciprocal_ne_zero hz
  have hs : Real.sin (1 / x) = -x * Real.cos (1 / x) := by linarith
  have he : squareMulCosReciprocalSqSecondDeriv x = -2 * Real.cos (1 / x) ^ 2 / x ^ 2 := by
    dsimp [squareMulCosReciprocalSqSecondDeriv]
    rw [hs]
    field_simp [hx]
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero hc))
    (sq_pos_of_ne_zero hx)

theorem squareMulCosReciprocalSq_stationary_second_deriv_ne_zero {x : ℝ} (hx : x ≠ 0)
    (hz : squareMulCosReciprocalSqFirstDeriv x = 0) : squareMulCosReciprocalSqSecondDeriv x ≠ 0 := by
  have hcases : Real.cos (1 / x) = 0 ∨ x * Real.cos (1 / x) + Real.sin (1 / x) = 0 := by
    simpa [squareMulCosReciprocalSqFirstDeriv, mul_eq_zero] using hz
  rcases hcases with hc | he
  · exact (squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero hx hc).ne'
  · exact (squareMulCosReciprocalSq_second_deriv_neg_at_stationary_factor_zero hx he).ne


theorem squareMulCosReciprocalSq_extrema_nonzero_iff {x : ℝ} (hx : x ≠ 0) :
    (IsLocalMinimumOn squareMulCosReciprocalSq univ x ↔ Real.cos (1 / x) = 0) ∧
    (IsLocalMaximumOn squareMulCosReciprocalSq univ x ↔
      x * Real.cos (1 / x) + Real.sin (1 / x) = 0) := by
  have hs := second_hasDerivAt_off_zero squareMulCosReciprocalSq_hasDerivAt squareMulCosReciprocalSqFirstDeriv_hasDerivAt hx
  have hn : deriv squareMulCosReciprocalSq x = 0 → deriv (deriv squareMulCosReciprocalSq) x ≠ 0 := by
    intro hz
    rw [hs.deriv]
    apply squareMulCosReciprocalSq_stationary_second_deriv_ne_zero hx
    rwa [(squareMulCosReciprocalSq_hasDerivAt x hx).deriv] at hz
  have ht := nondegenerate_extrema_iff (squareMulCosReciprocalSq_hasDerivAt x hx).differentiableAt hn
  have hm : IsLocalMinimumOn squareMulCosReciprocalSq univ x ↔
      squareMulCosReciprocalSqFirstDeriv x = 0 ∧ 0 < squareMulCosReciprocalSqSecondDeriv x := by
    simpa only [(squareMulCosReciprocalSq_hasDerivAt x hx).deriv, hs.deriv] using ht.1
  have hM : IsLocalMaximumOn squareMulCosReciprocalSq univ x ↔
      squareMulCosReciprocalSqFirstDeriv x = 0 ∧ squareMulCosReciprocalSqSecondDeriv x < 0 := by
    simpa only [(squareMulCosReciprocalSq_hasDerivAt x hx).deriv, hs.deriv] using ht.2
  constructor
  · constructor
    · intro h
      obtain ⟨hd, hp⟩ := hm.mp h
      have hc : Real.cos (1 / x) = 0 ∨ x * Real.cos (1 / x) + Real.sin (1 / x) = 0 := by
        simpa [squareMulCosReciprocalSqFirstDeriv, mul_eq_zero] using hd
      rcases hc with hc | he
      · exact hc
      · exact ((squareMulCosReciprocalSq_second_deriv_neg_at_stationary_factor_zero hx he).not_ge hp.le).elim
    · intro hc
      exact hm.mpr ⟨by dsimp only [squareMulCosReciprocalSqFirstDeriv]; rw [hc]; simp only [mul_zero, zero_mul], squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero hx hc⟩
  · constructor
    · intro h
      obtain ⟨hd, hp⟩ := hM.mp h
      have hc : Real.cos (1 / x) = 0 ∨ x * Real.cos (1 / x) + Real.sin (1 / x) = 0 := by
        simpa [squareMulCosReciprocalSqFirstDeriv, mul_eq_zero] using hd
      rcases hc with hc | he
      · exact (not_le_of_gt (squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero hx hc) hp.le).elim
      · exact he
    · intro he
      exact hM.mpr ⟨by dsimp only [squareMulCosReciprocalSqFirstDeriv]; rw [he, mul_zero], squareMulCosReciprocalSq_second_deriv_neg_at_stationary_factor_zero hx he⟩

theorem squareMulCosReciprocalSq_minimum_zero : IsLocalMinimumOn squareMulCosReciprocalSq univ 0 := by
  refine ⟨mem_univ _, 1, by norm_num, ?_⟩
  intro y _
  rw [squareMulCosReciprocalSq_zero]
  exact squareMulCosReciprocalSq_nonnegative y

theorem squareMulCosReciprocalSq_phase_value (n : ℕ) :
    squareMulCosReciprocalSq (reciprocalPhase Real.pi n) = reciprocalPhase Real.pi n ^ 2 := by
  have hp := reciprocalPhase_pos Real.pi_pos n
  rw [squareMulCosReciprocalSq, if_neg hp.ne', (reciprocalPhase_trig Real.pi n).2, Real.cos_pi]
  ring

theorem squareMulCosReciprocalSq_no_maximum_zero : ¬ IsLocalMaximumOn squareMulCosReciprocalSq univ 0 := by
  intro hM
  have hh := (source_maximum_univ_iff squareMulCosReciprocalSq 0).mp hM
  change ∀ᶠ x in 𝓝 (0 : ℝ), squareMulCosReciprocalSq x ≤ squareMulCosReciprocalSq 0 at hh
  obtain ⟨n, hn⟩ := ((reciprocalPhase_tendsto_zero Real.pi).eventually hh).exists
  rw [squareMulCosReciprocalSq_phase_value, squareMulCosReciprocalSq_zero] at hn
  exact not_le_of_gt (sq_pos_of_ne_zero (reciprocalPhase_pos Real.pi_pos n).ne') hn


theorem squareMulCosReciprocalSq_extrema_iff (x : ℝ) :
    (IsLocalMinimumOn squareMulCosReciprocalSq univ x ↔ x = 0 ∨ Real.cos (1 / x) = 0) ∧
    (IsLocalMaximumOn squareMulCosReciprocalSq univ x ↔
      x ≠ 0 ∧ x * Real.cos (1 / x) + Real.sin (1 / x) = 0) := by
  by_cases hx : x = 0
  · subst x
    constructor
    · constructor
      · intro _; exact Or.inl rfl
      · intro _; exact squareMulCosReciprocalSq_minimum_zero
    · constructor
      · intro h; exact (squareMulCosReciprocalSq_no_maximum_zero h).elim
      · rintro ⟨h, _⟩; exact (h rfl).elim
  · have h := squareMulCosReciprocalSq_extrema_nonzero_iff hx
    exact ⟨⟨fun hm ↦ Or.inr (h.1.mp hm),
        fun hm ↦ hm.elim (fun he ↦ (hx he).elim) h.1.mpr⟩,
      ⟨fun hM ↦ ⟨hx, h.2.mp hM⟩, fun hM ↦ h.2.mpr hM.2⟩⟩


theorem squareMulCosReciprocalSq_stationary_minima_accumulate :
    (∀ n : ℕ, 0 < reciprocalPhase (Real.pi / 2) n ∧
      squareMulCosReciprocalSq (reciprocalPhase (Real.pi / 2) n) = squareMulCosReciprocalSq 0 ∧
      IsLocalMinimumOn squareMulCosReciprocalSq univ (reciprocalPhase (Real.pi / 2) n) ∧
      HasDerivAt squareMulCosReciprocalSq 0 (reciprocalPhase (Real.pi / 2) n)) ∧
    Tendsto (reciprocalPhase (Real.pi / 2)) atTop (𝓝 0) := by
  refine ⟨?_, reciprocalPhase_tendsto_zero (Real.pi / 2)⟩
  intro n
  have hp := reciprocalPhase_pos (by positivity : 0 < Real.pi / 2) n
  have hc : Real.cos (1 / reciprocalPhase (Real.pi / 2) n) = 0 := by
    rw [(reciprocalPhase_trig (Real.pi / 2) n).2, Real.cos_pi_div_two]
  refine ⟨hp, ?_, (squareMulCosReciprocalSq_extrema_iff _).1.mpr (Or.inr hc), ?_⟩
  · rw [squareMulCosReciprocalSq_zero, squareMulCosReciprocalSq, if_neg hp.ne', hc]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · simpa only [squareMulCosReciprocalSqFirstDeriv, hc, mul_zero, zero_mul] using
      squareMulCosReciprocalSq_hasDerivAt (reciprocalPhase (Real.pi / 2) n) hp.ne'

theorem squareMulCosReciprocalSq_zero_minimum_not_strict (δ : ℝ) (hδ : 0 < δ) :
    ∃ x ∈ Ioo 0 δ, squareMulCosReciprocalSq x = squareMulCosReciprocalSq 0 := by
  obtain ⟨n, hn⟩ := ((reciprocalPhase_tendsto_zero (Real.pi / 2)).eventually
    (eventually_lt_nhds hδ)).exists
  exact ⟨_, ⟨(squareMulCosReciprocalSq_stationary_minima_accumulate.1 n).1, hn⟩,
    (squareMulCosReciprocalSq_stationary_minima_accumulate.1 n).2.1⟩

theorem squareMulCosReciprocalSq_first_deriv_secant_slopes_on_phase_sequences (n : ℕ) :
    (deriv squareMulCosReciprocalSq (reciprocalPhase Real.pi n) - deriv squareMulCosReciprocalSq 0) /
      (reciprocalPhase Real.pi n - 0) = 2 ∧
    (deriv squareMulCosReciprocalSq (reciprocalPhase (Real.pi / 2) n) - deriv squareMulCosReciprocalSq 0) /
      (reciprocalPhase (Real.pi / 2) n - 0) = 0 := by
  have hp := reciprocalPhase_pos Real.pi_pos n
  have hq := reciprocalPhase_pos (by positivity : 0 < Real.pi / 2) n
  constructor
  · rw [(squareMulCosReciprocalSq_hasDerivAt _ hp.ne').deriv, squareMulCosReciprocalSq_hasDerivAt_zero.deriv]
    dsimp [squareMulCosReciprocalSqFirstDeriv]
    rw [(reciprocalPhase_trig Real.pi n).1, (reciprocalPhase_trig Real.pi n).2,
      Real.sin_pi, Real.cos_pi]
    field_simp [hp.ne']
    ring
  · rw [(squareMulCosReciprocalSq_hasDerivAt _ hq.ne').deriv, squareMulCosReciprocalSq_hasDerivAt_zero.deriv]
    dsimp [squareMulCosReciprocalSqFirstDeriv]
    rw [(reciprocalPhase_trig (Real.pi / 2) n).2, Real.cos_pi_div_two]
    simp


theorem squareMulCosReciprocalSq_not_twice_differentiableAt_zero :
    ¬ DifferentiableAt ℝ (deriv squareMulCosReciprocalSq) 0 := by
  intro h
  have hs := h.hasDerivAt.tendsto_slope
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient] at hs
  have hp : Tendsto (reciprocalPhase Real.pi) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨reciprocalPhase_tendsto_zero Real.pi,
      Eventually.of_forall fun n ↦ (reciprocalPhase_pos Real.pi_pos n).ne'⟩
  have hq : Tendsto (reciprocalPhase (Real.pi / 2)) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨reciprocalPhase_tendsto_zero (Real.pi / 2),
      Eventually.of_forall fun n ↦ (reciprocalPhase_pos (by positivity : 0 < Real.pi / 2) n).ne'⟩
  have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 (deriv (deriv squareMulCosReciprocalSq) 0)) :=
    (hs.comp hp).congr' (Eventually.of_forall fun n ↦
      by simpa only [Function.comp_def] using (squareMulCosReciprocalSq_first_deriv_secant_slopes_on_phase_sequences n).1)
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (deriv (deriv squareMulCosReciprocalSq) 0)) :=
    (hs.comp hq).congr' (Eventually.of_forall fun n ↦
      by simpa only [Function.comp_def] using (squareMulCosReciprocalSq_first_deriv_secant_slopes_on_phase_sequences n).2)
  have he2 : deriv (deriv squareMulCosReciprocalSq) 0 = 2 := tendsto_nhds_unique htwo tendsto_const_nhds
  have he0 : deriv (deriv squareMulCosReciprocalSq) 0 = 0 := tendsto_nhds_unique hzero tendsto_const_nhds
  linarith


theorem squareMulCosReciprocalSq_second_deriv_signs_oscillate_near_zero (b : ℝ) (hb : 0 < b) :
    (∃ u ∈ Ioo 0 b, 0 < squareMulCosReciprocalSqSecondDeriv u) ∧
      (∃ v ∈ Ioo 0 b, squareMulCosReciprocalSqSecondDeriv v < 0) := by
  have hp := (reciprocalPhase_tendsto_zero (Real.pi / 2)).eventually (eventually_lt_nhds hb)
  have hm := (reciprocalPhase_tendsto_zero Real.pi).eventually
    (eventually_lt_nhds (lt_min hb (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨n, hn, hn'⟩ := (hp.and hm).exists
  have hu := reciprocalPhase_pos (by positivity : 0 < Real.pi / 2) n
  have hv := reciprocalPhase_pos Real.pi_pos n
  constructor
  · refine ⟨_, ⟨hu, hn⟩, squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero hu.ne' ?_⟩
    rw [(reciprocalPhase_trig (Real.pi / 2) n).2, Real.cos_pi_div_two]
  · refine ⟨_, ⟨hv, hn'.trans_le (min_le_left b 1)⟩, ?_⟩
    have hv1 : reciprocalPhase Real.pi n < 1 := hn'.trans_le (min_le_right b 1)
    have hsq : reciprocalPhase Real.pi n ^ 2 < 1 := by nlinarith
    have hsqpos : 0 < reciprocalPhase Real.pi n ^ 2 := sq_pos_of_ne_zero hv.ne'
    have hinv : 1 < 1 / reciprocalPhase Real.pi n ^ 2 :=
      (lt_div_iff₀ hsqpos).mpr (by simpa using hsq)
    have ht : 1 < (1 / reciprocalPhase Real.pi n) ^ 2 := by
      simpa only [div_pow, one_pow] using hinv
    dsimp [squareMulCosReciprocalSqSecondDeriv]
    rw [(reciprocalPhase_trig Real.pi n).1, (reciprocalPhase_trig Real.pi n).2,
      Real.sin_pi, Real.cos_pi]
    nlinarith

theorem squareMulCosReciprocalSq_convexity_intervals (a b : ℝ) :
    (ConvexOnOpenInterval squareMulCosReciprocalSq a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, 0 ≤ squareMulCosReciprocalSqSecondDeriv x) ∧
    (ConcaveOnOpenInterval squareMulCosReciprocalSq a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, squareMulCosReciprocalSqSecondDeriv x ≤ 0) :=
  convexity_intervals_iff_second_deriv_sign squareMulCosReciprocalSq_hasDerivAt squareMulCosReciprocalSqFirstDeriv_hasDerivAt
    squareMulCosReciprocalSq_second_deriv_signs_oscillate_near_zero a b

theorem squareMulCosReciprocalSq_second_deriv_zero_is_simple {x : ℝ} (hx : x ≠ 0)
    (hz : squareMulCosReciprocalSqSecondDeriv x = 0) : squareMulCosReciprocalSqThirdDeriv x ≠ 0 := by
  have hc : Real.cos (1 / x) ≠ 0 := by
    intro hc
    exact (squareMulCosReciprocalSq_second_deriv_pos_at_cos_reciprocal_zero hx hc).ne' hz
  have hs : Real.sin (1 / x) ≠ 0 := by
    intro hs
    have hcos : Real.cos (1 / x) ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (1 / x)]
    have ht : (1 / x) ^ 2 = 1 := by
      dsimp [squareMulCosReciprocalSqSecondDeriv] at hz
      rw [hs, hcos] at hz
      nlinarith
    have hsin1 : 0 < Real.sin (1 : ℝ) :=
      Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
    have hsq : (1 / x) ^ 2 = (1 : ℝ) ^ 2 := by simpa using ht
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hp
    · rw [hp] at hs
      exact hsin1.ne' hs
    · rw [hp, Real.sin_neg] at hs
      linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-8 : ℝ) ≠ 0) hs) hc)
    (pow_ne_zero 4 hx)

theorem squareMulCosReciprocalSq_inflection_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn squareMulCosReciprocalSq a b x) ↔
      x ≠ 0 ∧ squareMulCosReciprocalSqSecondDeriv x = 0 :=
  complete_inflection_points squareMulCosReciprocalSq_hasDerivAt squareMulCosReciprocalSqFirstDeriv_hasDerivAt
    squareMulCosReciprocalSqSecondDeriv_hasDerivAt squareMulCosReciprocalSq_second_deriv_signs_oscillate_near_zero
    (fun _ hx hz ↦ squareMulCosReciprocalSq_second_deriv_zero_is_simple hx hz) x


theorem squareMulCosReciprocalSqSecondDeriv_explicit (x : ℝ) :
    squareMulCosReciprocalSqSecondDeriv x = 1 + (1 - 2 * (1 / x) ^ 2) * Real.cos (2 * (1 / x)) +
      2 * (1 / x) * Real.sin (2 * (1 / x)) := by
  dsimp [squareMulCosReciprocalSqSecondDeriv]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have hs : Real.sin (1 / x) ^ 2 = 1 - Real.cos (1 / x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (1 / x)]
  rw [hs]
  ring

theorem squareMulCosReciprocalSq_inflection_explicit_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn squareMulCosReciprocalSq a b x) ↔
      x ≠ 0 ∧ 1 + (1 - 2 * (1 / x) ^ 2) * Real.cos (2 * (1 / x)) +
        2 * (1 / x) * Real.sin (2 * (1 / x)) = 0 := by
  rw [squareMulCosReciprocalSq_inflection_iff, squareMulCosReciprocalSqSecondDeriv_explicit]


theorem exercise12_square_mul_cos_reciprocal_sq_function_investigation :
    (∀ x : ℝ, squareMulCosReciprocalSq x = if x = 0 then 0 else x ^ 2 * Real.cos (1 / x) ^ 2) ∧
    Differentiable ℝ squareMulCosReciprocalSq ∧ HasDerivAt squareMulCosReciprocalSq 0 0 ∧
    ¬ DifferentiableAt ℝ (deriv squareMulCosReciprocalSq) 0 ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt squareMulCosReciprocalSq (squareMulCosReciprocalSqFirstDeriv x) x) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt (deriv squareMulCosReciprocalSq) (squareMulCosReciprocalSqSecondDeriv x) x) ∧
    (∀ x : ℝ, (IsLocalMinimumOn squareMulCosReciprocalSq univ x ↔ x = 0 ∨ Real.cos (1 / x) = 0) ∧
      (IsLocalMaximumOn squareMulCosReciprocalSq univ x ↔
        x ≠ 0 ∧ x * Real.cos (1 / x) + Real.sin (1 / x) = 0)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ x ∈ Ioo 0 δ, squareMulCosReciprocalSq x = squareMulCosReciprocalSq 0) ∧
    (∀ a b : ℝ, (ConvexOnOpenInterval squareMulCosReciprocalSq a b ↔
      0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, 0 ≤ squareMulCosReciprocalSqSecondDeriv x) ∧
      (ConcaveOnOpenInterval squareMulCosReciprocalSq a b ↔
      0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, squareMulCosReciprocalSqSecondDeriv x ≤ 0)) ∧
    (∀ x : ℝ, (∃ a b : ℝ, SourceInflectionOn squareMulCosReciprocalSq a b x) ↔
      x ≠ 0 ∧ 1 + (1 - 2 * (1 / x) ^ 2) * Real.cos (2 * (1 / x)) +
        2 * (1 / x) * Real.sin (2 * (1 / x)) = 0) := by
  exact ⟨squareMulCosReciprocalSq_eq_source, squareMulCosReciprocalSq_differentiable, squareMulCosReciprocalSq_hasDerivAt_zero,
    squareMulCosReciprocalSq_not_twice_differentiableAt_zero,
    squareMulCosReciprocalSq_hasDerivAt,
    fun _ hx ↦ second_hasDerivAt_off_zero squareMulCosReciprocalSq_hasDerivAt squareMulCosReciprocalSqFirstDeriv_hasDerivAt hx,
    squareMulCosReciprocalSq_extrema_iff, squareMulCosReciprocalSq_zero_minimum_not_strict,
    squareMulCosReciprocalSq_convexity_intervals, squareMulCosReciprocalSq_inflection_explicit_iff⟩

end calculus.Chapter04.Section04SquareMulCosReciprocalSqFunctionInvestigation
