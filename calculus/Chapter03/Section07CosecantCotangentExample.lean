import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts

/-!
# §3.7 — hiệu hai nghịch đảo lượng giác

Nguồn: Ví dụ 3.7.25, `Ch3_gioihanhamso.tex`, dòng 3451–3457.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07CosecantCotangentExample

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts


def cosecantCotangentDomain : Set ℝ := {x | Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}


theorem tangent_ne_zero_on_domain {x : ℝ} (hx : x ∈ cosecantCotangentDomain) :
    Real.tan x ≠ 0 := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_ne_zero hx.1 hx.2


theorem cosecant_cotangent_domain_accumulation :
    AccumulationPointOf cosecantCotangentDomain 0 := by
  have hsin : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin (0 : ℝ)
  have ha := derivative_quotient_domain_accumulation hsin (by simp) (by norm_num)
  exact accumulationPointOf_inter_nhds ha tangent_domain_nhds


theorem cosecant_sub_reciprocal_tangent_eq {x : ℝ} (hx : x ∈ cosecantCotangentDomain) :
    1 / Real.sin x - 1 / Real.tan x = (1 - Real.cos x) / Real.sin x := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2]

/-- Ví dụ 3.7.25: 1/sin x−1/tan x→0 khi x→0. -/
theorem cosecant_sub_reciprocal_tangent_domainLimit :
    DomainLimit cosecantCotangentDomain
      (fun x ↦ 1 / Real.sin x - 1 / Real.tan x) 0 0 := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ x in domainApproachFilter univ (.point 0), Real.sin x ≠ 0 := by
    filter_upwards [sine_equivalent_identity_zero.2.2.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)]
      with x hx
    exact (div_ne_zero_iff.mp hx).1
  have ht : Tendsto (fun x : ℝ ↦ ((1 - Real.cos x) / x ^ 2) * x / (Real.sin x / x))
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [Pi.div_apply, mul_zero, zero_div] using!
      (one_sub_cos_div_square_tendsto.mul hi).div sine_equivalent_identity_zero.2.2
        (by norm_num : (1 : ℝ) ≠ 0)
  have hfull : Tendsto (fun x : ℝ ↦ 1 / Real.sin x - 1 / Real.tan x)
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne, tangent_eventually_defined_zero, hs]
      with x hx hc hsin
    rw [cosecant_sub_reciprocal_tangent_eq (show x ∈ cosecantCotangentDomain from ⟨hsin, hc⟩)]
    field_simp [hx, hsin]
  apply (domainLimit_iff_tendsto cosecant_cotangent_domain_accumulation).mpr
  exact hfull.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ cosecantCotangentDomain)))

end calculus.Chapter03.Section07CosecantCotangentExample
