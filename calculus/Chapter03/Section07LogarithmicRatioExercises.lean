import calculus.Chapter03.Section07Examples
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
§3.7 — Bài tập 3.7.11(e,g)

Nguồn: dòng 3687, 3689.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07LogarithmicRatioExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section07
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07Examples


def logarithmicTangentRatioDomain : Set ℝ :=
  {x | Real.cos x ≠ 0 ∧ 0 < 1 + x * Real.tan x ∧ x ^ 2 + Real.sin x ^ 3 ≠ 0}


def logarithmicPolynomialRatioDomain : Set ℝ :=
  {x | 0 < 1 + 4 * x ^ 2 - 5 * x ^ 3 ∧ 0 < 1 + 2 * x ^ 2 + 3 * x ^ 3 ∧
    Real.log (1 + 2 * x ^ 2 + 3 * x ^ 3) ≠ 0}


theorem normalized_log_of_quadratic {u : ℝ → ℝ} {A : ℝ}
    (hu : Tendsto u (domainApproachFilter univ (.point 0)) (𝓝 0))
    (hn : Tendsto (fun x ↦ u x / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 A)) (hA : A ≠ 0) :
    Tendsto (fun x ↦ Real.log (1 + u x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 A) := by
  have hune : ∀ᶠ x in domainApproachFilter univ (.point 0), u x ≠ 0 :=
    (hn.eventually_ne hA).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hv : Tendsto (fun x ↦ 1 + u x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using hu.const_add 1
  have hvn : Tendsto (fun x ↦ 1 + u x)
      (domainApproachFilter univ (.point 0)) (𝓝[univ \ {(1 : ℝ)}] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hv, ?_⟩
    filter_upwards [hune] with x hx
    exact ⟨mem_univ _, by simpa using hx⟩
  have hs : Tendsto (fun x ↦ slope Real.log 1 (1 + u x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hd : HasDerivAt Real.log 1 1 := by
      simpa only [inv_one] using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    exact ((domainLimit_iff_tendsto (univ_accumulation 1)).mp
      (hasDerivAt_domainLimit_slope hd)).comp hvn
  apply (show Tendsto (fun x ↦ slope Real.log 1 (1 + u x) * (u x / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 A) from by
        simpa only [one_mul] using hs.mul hn).congr'
  filter_upwards [hune] with x hu0
  rw [slope_def_field, Real.log_one]
  field_simp [hu0]
  ring


theorem domainLimit_of_eventually_domain {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ D)
    (hf : Tendsto f (domainApproachFilter univ (.point 0)) (𝓝 L)) :
    DomainLimit D f 0 L := by
  have he := domainApproachFilter_eq_univ_of_eventually_mem hD
  have hp : NontrivialDomainApproach D (.point 0) := by
    change (domainApproachFilter D (.point 0)).NeBot
    rw [he]
    exact (properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0)
  apply (domainLimit_iff_tendsto ((properLimitApproach_point_iff D 0).mp hp)).mpr
  change Tendsto f (domainApproachFilter D (.point 0)) (𝓝 L)
  rwa [he]

/-- Bài tập 3.7.11(e): giới hạn bằng 1. -/
theorem logarithmic_tangent_ratio_at_zero :
    DomainLimit logarithmicTangentRatioDomain
      (fun x ↦ Real.log (1 + x * Real.tan x) / (x ^ 2 + Real.sin x ^ 3)) 0 1 := by
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have htan : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.tan_zero] using
      (Real.continuousAt_tan.mpr (by norm_num : Real.cos (0 : ℝ) ≠ 0)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hu : Tendsto (fun x ↦ x * Real.tan x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hi.mul htan
  have hun : Tendsto (fun x : ℝ ↦ (x * Real.tan x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply tangent_equivalent_identity_zero.2.2.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hf := normalized_log_of_quadratic hu hun one_ne_zero
  have hn : Tendsto (fun x : ℝ ↦ 1 + x * (Real.sin x / x) ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, zero_mul, add_zero] using
      (hi.mul (sine_equivalent_identity_zero.2.2.pow 3)).const_add 1
  have hg : Tendsto (fun x : ℝ ↦ (x ^ 2 + Real.sin x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply hn.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hden : ∀ᶠ x in domainApproachFilter univ (.point 0), x ^ 2 + Real.sin x ^ 3 ≠ 0 :=
    (hg.eventually_ne one_ne_zero).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hpos : ∀ᶠ x in domainApproachFilter univ (.point 0), 0 < 1 + x * Real.tan x := by
    have hp : Tendsto (fun x ↦ 1 + x * Real.tan x)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using hu.const_add 1
    exact hp.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ logarithmicTangentRatioDomain := by
    filter_upwards [tangent_eventually_defined_zero, hpos, hden] with x hc hp hd
    exact ⟨hc, hp, hd⟩
  apply domainLimit_of_eventually_domain hD
  apply (show Tendsto (fun x : ℝ ↦ (Real.log (1 + x * Real.tan x) / x ^ 2) /
      ((x ^ 2 + Real.sin x ^ 3) / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) from by
        simpa only [Pi.div_apply, div_one] using! hf.div hg one_ne_zero).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 hx) _ _

/-- Bài tập 3.7.11(g): giới hạn bằng 2. -/
theorem logarithmic_polynomial_ratio_at_zero :
    DomainLimit logarithmicPolynomialRatioDomain
      (fun x ↦ Real.log (1 + 4 * x ^ 2 - 5 * x ^ 3) /
        Real.log (1 + 2 * x ^ 2 + 3 * x ^ 3)) 0 2 := by
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ 4 * x ^ 2 - 5 * x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa using ((hi.pow 2).const_mul 4).sub ((hi.pow 3).const_mul 5)
  have hv : Tendsto (fun x : ℝ ↦ 2 * x ^ 2 + 3 * x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa using ((hi.pow 2).const_mul 2).add ((hi.pow 3).const_mul 3)
  have hun : Tendsto (fun x : ℝ ↦ (4 * x ^ 2 - 5 * x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ 4 - 5 * x)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) from by
        simpa using (hi.const_mul 5).const_sub 4).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hvn : Tendsto (fun x : ℝ ↦ (2 * x ^ 2 + 3 * x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    apply (show Tendsto (fun x : ℝ ↦ 2 + 3 * x)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) from by
        simpa using (hi.const_mul 3).const_add 2).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have hf : Tendsto (fun x : ℝ ↦ Real.log (1 + 4 * x ^ 2 - 5 * x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (4 : ℝ)) := by
    convert! normalized_log_of_quadratic hu hun (by norm_num : (4 : ℝ) ≠ 0) using 1
    ext x
    congr 2
    ring
  have hg : Tendsto (fun x : ℝ ↦ Real.log (1 + 2 * x ^ 2 + 3 * x ^ 3) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    convert! normalized_log_of_quadratic hv hvn (by norm_num : (2 : ℝ) ≠ 0) using 1
    ext x
    congr 2
    ring
  have hpos1 : ∀ᶠ x in domainApproachFilter univ (.point 0), 0 < 1 + 4 * x ^ 2 - 5 * x ^ 3 := by
    have hp : Tendsto (fun x : ℝ ↦ 1 + 4 * x ^ 2 - 5 * x ^ 3)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      convert! hu.const_add 1 using 1
      · ext x; ring
      · norm_num
    exact hp.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpos2 : ∀ᶠ x in domainApproachFilter univ (.point 0), 0 < 1 + 2 * x ^ 2 + 3 * x ^ 3 := by
    have hp : Tendsto (fun x : ℝ ↦ 1 + 2 * x ^ 2 + 3 * x ^ 3)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [add_assoc, add_zero] using hv.const_add 1
    exact hp.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hden : ∀ᶠ x in domainApproachFilter univ (.point 0),
      Real.log (1 + 2 * x ^ 2 + 3 * x ^ 3) ≠ 0 :=
    (hg.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ logarithmicPolynomialRatioDomain := by
    filter_upwards [hpos1, hpos2, hden] with x hp1 hp2 hd
    exact ⟨hp1, hp2, hd⟩
  apply domainLimit_of_eventually_domain hD
  apply (show Tendsto (fun x : ℝ ↦ (Real.log (1 + 4 * x ^ 2 - 5 * x ^ 3) / x ^ 2) /
      (Real.log (1 + 2 * x ^ 2 + 3 * x ^ 3) / x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) from by
        simpa only [Pi.div_apply, show (4 : ℝ) / 2 = 2 by norm_num] using!
          hf.div hg (by norm_num : (2 : ℝ) ≠ 0)).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 hx) _ _

end calculus.Chapter03.Section07LogarithmicRatioExercises
