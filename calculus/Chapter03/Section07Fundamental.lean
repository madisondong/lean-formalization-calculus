import calculus.Chapter03.Section07Examples
import calculus.Chapter03.Section07AlgebraSupplement
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
§3.7 — các tương đương cơ bản

Nguồn: dòng 3309–3340.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07AlgebraSupplement
open calculus.Chapter03.Section02


theorem derivative_quotient_zero {f : ℝ → ℝ} {A : ℝ} (hf : HasDerivAt f A 0) :
    Tendsto (fun x ↦ (f x - f 0) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 A) := by
  simpa only [domainApproachFilter, ← compl_eq_univ_sdiff, smul_eq_mul,
    zero_add, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero

theorem exponential_sub_one_equivalent_identity_zero :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) (fun x : ℝ ↦ Real.exp x - 1) (fun x ↦ x) := by
  refine ⟨sine_equivalent_identity_zero.1, punctured_zero_eventually_ne, ?_⟩
  simpa only [Real.exp_zero] using derivative_quotient_zero (Real.hasDerivAt_exp 0)


theorem log_one_add_eventually_defined :
    ∀ᶠ x in domainApproachFilter univ (.point 0), 0 < 1 + x := by
  have hh : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), -1 < x := Ioi_mem_nhds (by norm_num)
  filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with x hx
  linarith

theorem logarithm_one_add_equivalent_identity_zero :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) (fun x : ℝ ↦ Real.log (1 + x)) (fun x ↦ x) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x)) 1 0 := by
    have ha : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 0 :=
      (hasDerivAt_id (0 : ℝ)).const_add 1
    simpa only [add_zero, div_one] using
      ha.log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  refine ⟨sine_equivalent_identity_zero.1, punctured_zero_eventually_ne, ?_⟩
  simpa only [add_zero, Real.log_one, sub_zero] using derivative_quotient_zero hf


theorem one_sub_cosine_over_square_zero :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
  have hc : Tendsto (fun x : ℝ ↦ 1 + Real.cos x)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    have hc0 : ContinuousAt (fun x : ℝ ↦ 1 + Real.cos x) (0 : ℝ) :=
      continuous_const.continuousAt.add Real.continuous_cos.continuousAt
    simpa only [domainApproachFilter, Real.cos_zero, one_add_one_eq_two] using
      hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  have ht : Tendsto (fun x : ℝ ↦ (Real.sin x / x) * (Real.sin x / x) / (1 + Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_def, one_mul] using (sine_equivalent_identity_zero.2.2.mul
      sine_equivalent_identity_zero.2.2).div hc (by norm_num)
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne, hc.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)] with x hx hcx
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem one_sub_cosine_same_order_square_zero :
    NonzeroRatioLimitAlong univ (.point 0) (fun x : ℝ ↦ 1 - Real.cos x) (fun x ↦ x ^ 2) :=
  ⟨sine_equivalent_identity_zero.1, punctured_zero_eventually_ne.mono (fun x hx ↦ pow_ne_zero 2 hx),
    1 / 2, by norm_num, one_sub_cosine_over_square_zero⟩

theorem one_sub_cosine_equivalent_half_square_zero :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) (fun x : ℝ ↦ 1 - Real.cos x) (fun x ↦ x ^ 2 / 2) := by
  refine ⟨sine_equivalent_identity_zero.1, ?_, ?_⟩
  · exact punctured_zero_eventually_ne.mono fun x hx ↦ div_ne_zero (pow_ne_zero 2 hx) (by norm_num)
  · have ht : Tendsto (fun x : ℝ ↦ 2 * ((1 - Real.cos x) / x ^ 2))
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa using one_sub_cosine_over_square_zero.const_mul 2
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp

/-- Ví dụ 3.7.13(c): 1−cos x cùng bậc với x² và tương đương x²/2 khi x→0. -/
theorem cosine_quadratic_infinitesimal_example :
    InfinitesimalsWithNonzeroRatioLimitAlong univ (.point 0) (fun x : ℝ ↦ 1 - Real.cos x) (fun x ↦ x ^ 2) ∧
    EquivalentInfinitesimalsAlong univ (.point 0) (fun x : ℝ ↦ 1 - Real.cos x) (fun x ↦ x ^ 2 / 2) := by
  have hc : InfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ 1 - Real.cos x) :=
    ⟨sine_equivalent_identity_zero.1, by
      have hc0 : ContinuousAt (fun x : ℝ ↦ 1 - Real.cos x) (0 : ℝ) :=
        continuous_const.continuousAt.sub Real.continuous_cos.continuousAt
      simpa only [domainApproachFilter, Real.cos_zero, sub_self] using
        hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))⟩
  have hs : InfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ x ^ 2) :=
    ⟨hc.1, by
      have hs0 : ContinuousAt (fun x : ℝ ↦ x ^ 2) (0 : ℝ) := by
        simpa only [Pi.pow_def, id_eq] using
          (continuous_id.continuousAt (x := (0 : ℝ))).pow 2
      simpa only [domainApproachFilter, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        hs0.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))⟩
  have hh : InfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ x ^ 2 / 2) :=
    ⟨hc.1, by simpa only [zero_div] using hs.2.div_const 2⟩
  exact ⟨⟨hc, hs, one_sub_cosine_same_order_square_zero⟩,
    ⟨hc, hh, one_sub_cosine_equivalent_half_square_zero⟩⟩


theorem one_add_power_sub_one_equivalent (n : ℕ) (hn : 1 ≤ n) :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) (fun x : ℝ ↦ (1 + x) ^ n - 1) (fun x ↦ (n : ℝ) * x) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hf : HasDerivAt (fun x : ℝ ↦ (1 + x) ^ n) (n : ℝ) 0 := by
    simpa only [Pi.pow_def, id_eq, add_zero, one_pow, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_add 1).pow n
  refine ⟨sine_equivalent_identity_zero.1,
    punctured_zero_eventually_ne.mono (fun x hx ↦ mul_ne_zero hn0 hx), ?_⟩
  have ht : Tendsto (fun x : ℝ ↦ (((1 + x) ^ n - 1) / x) / (n : ℝ))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero, one_pow, div_self hn0] using (derivative_quotient_zero hf).div_const (n : ℝ)
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  field_simp


theorem nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero {D : Set ℝ} {p : LimitApproach}
    {f g : ℝ → ℝ} (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) (hg : InfinitesimalAlong D p g) :
    EquivalentInfinitesimalsAlong D p f g :=
  ⟨⟨hg.1, (nonvanishingAsymptoticEquivalenceAlong_mathlib hf).tendsto_nhds_iff.mpr hg.2⟩, hg, hf⟩


theorem identity_infinitesimal_zero :
    InfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ x) := by
  refine ⟨sine_equivalent_identity_zero.1, ?_⟩
  exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- Ví dụ 3.7.13(a): x² và x là vô cùng bé, với x²=o(x). -/
theorem square_higher_infinitesimal_identity_zero :
    HigherOrderInfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ x ^ 2) (fun x ↦ x) := by
  refine ⟨⟨identity_infinitesimal_zero.1, ?_⟩, identity_infinitesimal_zero,
    square_littleO_identity_zero⟩
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using identity_infinitesimal_zero.2.pow 2

/-- Ví dụ 3.7.13(b): sin(x²)=o(x) khi x→0. -/
theorem sine_of_square_higher_infinitesimal_identity_zero :
    HigherOrderInfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ Real.sin (x ^ 2)) (fun x ↦ x) := by
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using identity_infinitesimal_zero.2.pow 2
  have hf : InfinitesimalAlong univ (.point 0) (fun x : ℝ ↦ Real.sin (x ^ 2)) := by
    refine ⟨identity_infinitesimal_zero.1, ?_⟩
    simpa only [Real.sin_zero, Function.comp_def] using
      (show ContinuousAt Real.sin (0 : ℝ) from Real.continuous_sin.continuousAt).tendsto.comp hsq
  refine ⟨hf, identity_infinitesimal_zero, identity_infinitesimal_zero.1,
    punctured_zero_eventually_ne, ?_⟩
  have hs : Tendsto (fun x : ℝ ↦ Real.sinc (x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.sinc_zero, Function.comp_def] using
      (show ContinuousAt Real.sinc (0 : ℝ) from Real.continuous_sinc.continuousAt).tendsto.comp hsq
  have ht : Tendsto (fun x : ℝ ↦ Real.sinc (x ^ 2) * x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [one_mul] using hs.mul identity_infinitesimal_zero.2
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  rw [Real.sinc_of_ne_zero (pow_ne_zero 2 hx)]
  field_simp [hx]

/-- Mệnh đề 3.7.14: exp(x)−1 và x là hai vô cùng bé tương đương. -/
theorem exponential_equivalent_infinitesimals_zero :
    EquivalentInfinitesimalsAlong univ (.point 0) (fun x : ℝ ↦ Real.exp x - 1) (fun x ↦ x) :=
  nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero exponential_sub_one_equivalent_identity_zero
    identity_infinitesimal_zero


theorem sine_equivalent_infinitesimals_zero :
    EquivalentInfinitesimalsAlong univ (.point 0) Real.sin (fun x ↦ x) :=
  nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero sine_equivalent_identity_zero identity_infinitesimal_zero


theorem logarithm_equivalent_infinitesimals_zero :
    EquivalentInfinitesimalsAlong univ (.point 0) (fun x : ℝ ↦ Real.log (1 + x)) (fun x ↦ x) :=
  nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero logarithm_one_add_equivalent_identity_zero
    identity_infinitesimal_zero


theorem tangent_equivalent_infinitesimals_zero :
    EquivalentInfinitesimalsAlong univ (.point 0) Real.tan (fun x ↦ x) :=
  nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero tangent_equivalent_identity_zero identity_infinitesimal_zero


theorem natural_power_equivalent_infinitesimals_zero (n : ℕ) (hn : 1 ≤ n) :
    EquivalentInfinitesimalsAlong univ (.point 0)
      (fun x : ℝ ↦ (1 + x) ^ n - 1) (fun x ↦ (n : ℝ) * x) := by
  apply nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero (one_add_power_sub_one_equivalent n hn)
  refine ⟨identity_infinitesimal_zero.1, ?_⟩
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := (n : ℝ))).mul identity_infinitesimal_zero.2

end calculus.Chapter03.Section07Fundamental
