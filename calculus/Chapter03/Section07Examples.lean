import calculus.Chapter03.Section07
import calculus.Chapter03.Section03Supplement
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
§3.7 — các ví dụ mở đầu về giới hạn thương

Nguồn: dòng 3211–3232.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07 calculus.Chapter03.Section02

theorem punctured_zero_eventually_ne :
    ∀ᶠ x in domainApproachFilter univ (.point 0), x ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hx.2

/-- Dòng 3213: xᵐ=o(xⁿ) tại 0 khi n<m. -/
theorem powers_littleO_zero (m n : ℕ) (hmn : n < m) :
    NonvanishingDenominatorLittleOAlong univ (.point 0) (fun x ↦ x ^ m) (fun x ↦ x ^ n) := by
  apply nonvanishingDenominatorLittleOAlong_iff_mathlib.mpr
  refine ⟨(properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0), ?_, ?_⟩
  · exact punctured_zero_eventually_ne.mono fun x hx ↦ pow_ne_zero n hx
  · exact (Asymptotics.isLittleO_pow_pow hmn).mono nhdsWithin_le_nhds

theorem square_littleO_identity_zero :
    NonvanishingDenominatorLittleOAlong univ (.point 0) (fun x ↦ x ^ 2) (fun x ↦ x) := by
  simpa only [pow_one] using powers_littleO_zero 2 1 (by decide)

/-- Dòng 3215: x=o(x²) tại +∞. -/
theorem identity_littleO_square_atTop :
    NonvanishingDenominatorLittleOAlong univ .positiveInfinity (fun x ↦ x) (fun x ↦ x ^ 2) := by
  refine ⟨(properLimitApproach_positiveInfinity_iff univ).mpr not_bddAbove_univ, ?_, ?_⟩
  · have hn : ∀ᶠ x : ℝ in atTop, x ^ 2 ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact pow_ne_zero 2 (by linarith)
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using hn
  · simpa only [domainApproachFilter, principal_univ, inf_top_eq, pow_one] using
      (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (p := 1) (q := 2) (by decide))

/-- Dòng 3230: sin x∼x khi x→0. -/
theorem sine_equivalent_identity_zero :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) Real.sin (fun x ↦ x) := by
  refine ⟨(properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0),
    punctured_zero_eventually_ne, ?_⟩
  have ht : Tendsto Real.sinc (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact Real.sinc_of_ne_zero hx

/-- dòng 3217: sin³ x là vô cùng bé bậc cao hơn x. -/
theorem sine_cube_littleO_identity_zero :
    NonvanishingDenominatorLittleOAlong univ (.point 0) (fun x ↦ Real.sin x ^ 3) (fun x ↦ x) := by
  refine ⟨(properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0),
    punctured_zero_eventually_ne, ?_⟩
  have hs : Tendsto (fun x : ℝ ↦ Real.sin x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    have hc2 : ContinuousAt (fun x : ℝ ↦ Real.sin x ^ 2) 0 := by
      simpa only [Pi.pow_def] using
        (Real.continuous_sin.continuousAt (x := (0 : ℝ))).pow 2
    simpa only [domainApproachFilter, Real.sin_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      hc2.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  apply (show Tendsto (fun x : ℝ ↦ (Real.sin x / x) * Real.sin x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 0) from by
        simpa using sine_equivalent_identity_zero.2.2.mul hs).congr'
  exact Eventually.of_forall fun x ↦ by ring

/-- Dòng 3225: thương có giới hạn 5 nên hai hàm cùng bậc. -/
theorem five_square_same_order_square_zero :
    NonzeroRatioLimitAlong univ (.point 0) (fun x ↦ 5 * x ^ 2) (fun x ↦ x ^ 2) := by
  refine ⟨(properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0),
    punctured_zero_eventually_ne.mono (fun x hx ↦ pow_ne_zero 2 hx), 5, by norm_num, ?_⟩
  apply (tendsto_const_nhds (x := (5 : ℝ))).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  field_simp


theorem sine_same_order_identity_zero :
    NonzeroRatioLimitAlong univ (.point 0) Real.sin (fun x ↦ x) :=
  ⟨sine_equivalent_identity_zero.1, sine_equivalent_identity_zero.2.1,
    1, by norm_num, sine_equivalent_identity_zero.2.2⟩

/-- Dòng 3227: hai đa thức bậc hai cùng bậc. -/
theorem quadratic_polynomials_same_order_atTop :
    NonzeroRatioLimitAlong univ .positiveInfinity
      (fun x ↦ 2 * x ^ 2 + x + 1) (fun x ↦ 4 * x ^ 2 + 7 * x + 1) := by
  refine ⟨(properLimitApproach_positiveInfinity_iff univ).mpr not_bddAbove_univ, ?_,
    1 / 2, by norm_num, ?_⟩
  · have he : ∀ᶠ x : ℝ in atTop, 4 * x ^ 2 + 7 * x + 1 ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hp : 0 < 4 * x ^ 2 + 7 * x + 1 := by nlinarith [sq_nonneg x]
      exact hp.ne'
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using he
  · have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hn : Tendsto (fun x : ℝ ↦ 2 + x⁻¹ + x⁻¹ ^ 2) atTop (𝓝 2) := by
      simpa using ((tendsto_const_nhds (x := (2 : ℝ))).add hi).add (hi.pow 2)
    have hd : Tendsto (fun x : ℝ ↦ 4 + 7 * x⁻¹ + x⁻¹ ^ 2) atTop (𝓝 4) := by
      simpa using ((tendsto_const_nhds (x := (4 : ℝ))).add
        ((tendsto_const_nhds (x := (7 : ℝ))).mul hi)).add (hi.pow 2)
    have hq : Tendsto (fun x : ℝ ↦ (2 + x⁻¹ + x⁻¹ ^ 2) / (4 + 7 * x⁻¹ + x⁻¹ ^ 2))
        atTop (𝓝 (1 / 2 : ℝ)) := by
      (convert! hn.div hd (by norm_num : (4 : ℝ) ≠ 0) using 1; norm_num)
    have ht : Tendsto (fun x : ℝ ↦ (2 * x ^ 2 + x + 1) / (4 * x ^ 2 + 7 * x + 1))
        atTop (𝓝 (1 / 2 : ℝ)) := by
      apply hq.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      field_simp [hx0]
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using ht


theorem tangent_eventually_defined_zero :
    ∀ᶠ x in domainApproachFilter univ (.point 0), Real.cos x ≠ 0 := by
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  exact hc.eventually_ne (by norm_num)

theorem tangent_equivalent_identity_zero :
    NonvanishingAsymptoticEquivalenceAlong univ (.point 0) Real.tan (fun x ↦ x) := by
  refine ⟨sine_equivalent_identity_zero.1, punctured_zero_eventually_ne, ?_⟩
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  have ht : Tendsto (fun x ↦ (Real.sin x / x) / Real.cos x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, div_one] using
      sine_equivalent_identity_zero.2.2.div hc (by norm_num : (1 : ℝ) ≠ 0)
  apply ht.congr'
  exact Eventually.of_forall fun x ↦ by
    change (Real.sin x / x) / Real.cos x = Real.tan x / x
    rw [Real.tan_eq_sin_div_cos]
    ring

/-- Dòng 3280: tính bắc cầu và tương đương sin x với tan x. -/
theorem equivalence_transitivity_with_sine_tangent :
    (∀ (D : Set ℝ) (p : LimitApproach) (f g h : ℝ → ℝ),
      NonvanishingAsymptoticEquivalenceAlong D p f g → NonvanishingAsymptoticEquivalenceAlong D p g h → NonvanishingAsymptoticEquivalenceAlong D p f h) ∧
      NonvanishingAsymptoticEquivalenceAlong univ (.point 0) Real.sin (fun x ↦ x) ∧
      NonvanishingAsymptoticEquivalenceAlong univ (.point 0) (fun x ↦ x) Real.tan ∧
      NonvanishingAsymptoticEquivalenceAlong univ (.point 0) Real.sin Real.tan := by
  have ht := nonvanishingAsymptoticEquivalenceAlong_symm tangent_equivalent_identity_zero
  exact ⟨fun _ _ _ _ _ hf hg ↦ nonvanishingAsymptoticEquivalenceAlong_trans hf hg,
    sine_equivalent_identity_zero, ht, nonvanishingAsymptoticEquivalenceAlong_trans sine_equivalent_identity_zero ht⟩

end calculus.Chapter03.Section07Examples
