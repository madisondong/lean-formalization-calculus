import calculus.Chapter03.Section07Examples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
§3.7 — Bài tập 3.7.11(c,f,q)

Nguồn: dòng 3685, dòng 3688, dòng 3699.
-/

set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07CosineRatioExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples


def halfAngleCosineRatioDomain : Set ℝ := {x | 1 - Real.cos (x / 2) ≠ 0}


def cosinePolynomialRatioDomain : Set ℝ := {x | 2 * x ^ 2 + 3 * x ^ 3 - x ^ 4 ≠ 0}


def cosineSquareRatioDomain : Set ℝ := {x | x ^ 2 ≠ 0}


theorem normalized_scaled_cosine (c : ℝ) :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos (c * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (c ^ 2 / 2)) := by
  by_cases hc : c = 0
  · subst c
    simpa using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (domainApproachFilter univ (.point 0)) (𝓝 0))
  have hs : Tendsto (fun x : ℝ ↦ Real.sinc (c * x / 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.sinc (c * x / 2)) 0 :=
      Real.continuous_sinc.continuousAt.comp
        ((continuous_const.mul continuous_id).div_const 2).continuousAt
    simpa only [domainApproachFilter, mul_zero, zero_div, Real.sinc_zero] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ (c ^ 2 / 2) * Real.sinc (c * x / 2) ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (c ^ 2 / 2)) := by
    simpa only [one_pow, mul_one] using (hs.pow 2).const_mul (c ^ 2 / 2)
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  have hphase : c * x / 2 ≠ 0 := div_ne_zero (mul_ne_zero hc hx) (by norm_num)
  have hhalf : 1 - Real.cos (c * x) = 2 * Real.sin (c * x / 2) ^ 2 := by
    have h := Real.cos_two_mul (c * x / 2)
    rw [show 2 * (c * x / 2) = c * x by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (c * x / 2)]
  rw [Real.sinc_of_ne_zero hphase, hhalf]
  field_simp [hc, hx]


theorem ratio_of_quadratic_normalizations {f g : ℝ → ℝ} {A B : ℝ}
    (hf : Tendsto (fun x ↦ f x / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 A))
    (hg : Tendsto (fun x ↦ g x / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 B)) (hB : B ≠ 0) :
    DomainLimit {x | g x ≠ 0} (fun x ↦ f x / g x) 0 (A / B) := by
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ {x | g x ≠ 0} :=
    (hg.eventually_ne hB).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hfilter := domainApproachFilter_eq_univ_of_eventually_mem hD
  have hp : NontrivialDomainApproach {x | g x ≠ 0} (.point 0) := by
    change (domainApproachFilter {x | g x ≠ 0} (.point 0)).NeBot
    rw [hfilter]
    exact (properLimitApproach_point_iff univ 0).mpr (univ_accumulation 0)
  have ha := (properLimitApproach_point_iff {x | g x ≠ 0} 0).mp hp
  apply (domainLimit_iff_tendsto ha).mpr
  change Tendsto (fun x ↦ f x / g x)
    (domainApproachFilter {x | g x ≠ 0} (.point 0)) (𝓝 (A / B))
  rw [hfilter]
  apply (hf.div hg hB).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  simp only [Pi.div_apply]
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 hx) _ _

/-- Bài tập 3.7.11(c): giới hạn bằng 4. -/
theorem half_angle_cosine_ratio_at_zero :
    DomainLimit halfAngleCosineRatioDomain
      (fun x ↦ (1 - Real.cos x) / (1 - Real.cos (x / 2))) 0 4 := by
  have hf : Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [one_mul, one_pow] using normalized_scaled_cosine 1
  have hg : Tendsto (fun x : ℝ ↦ (1 - Real.cos (x / 2)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 8 : ℝ)) := by
    convert! normalized_scaled_cosine (1 / 2) using 1
    · ext x
      congr 2
      ring
    · norm_num
  have ht := ratio_of_quadratic_normalizations hf hg (by norm_num : (1 / 8 : ℝ) ≠ 0)
  norm_num at ht
  exact ht

/-- Bài tập 3.7.11(f): giới hạn bằng 9/4. -/
theorem cosine_polynomial_ratio_at_zero :
    DomainLimit cosinePolynomialRatioDomain
      (fun x ↦ (1 - Real.cos (3 * x)) / (2 * x ^ 2 + 3 * x ^ 3 - x ^ 4))
      0 (9 / 4) := by
  have hf : Tendsto (fun x : ℝ ↦ (1 - Real.cos (3 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (9 / 2 : ℝ)) := by
    convert! normalized_scaled_cosine 3 using 1; norm_num
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ ↦ 2 + 3 * x - x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
      ((tendsto_const_nhds (x := (2 : ℝ))).add (hi.const_mul 3)).sub (hi.pow 2)
  have hg : Tendsto (fun x : ℝ ↦ (2 * x ^ 2 + 3 * x ^ 3 - x ^ 4) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    apply hn.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have ht := ratio_of_quadratic_normalizations hf hg (by norm_num : (2 : ℝ) ≠ 0)
  norm_num at ht
  exact ht

/-- Bài tập 3.7.11(q): (cos 3x−cos 7x)/x²→20. -/
theorem cosine_frequency_difference_at_zero :
    DomainLimit cosineSquareRatioDomain
      (fun x ↦ (Real.cos (3 * x) - Real.cos (7 * x)) / x ^ 2) 0 20 := by
  have h7 := normalized_scaled_cosine 7
  have h3 := normalized_scaled_cosine 3
  have hf : Tendsto (fun x : ℝ ↦ (Real.cos (3 * x) - Real.cos (7 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (20 : ℝ)) := by
    convert! h7.sub h3 using 1
    · ext x
      ring
    · norm_num
  have hg : Tendsto (fun x : ℝ ↦ x ^ 2 / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    exact (div_self (pow_ne_zero 2 hx)).symm
  simpa only [cosineSquareRatioDomain, div_one] using ratio_of_quadratic_normalizations hf hg one_ne_zero

end calculus.Chapter03.Section07CosineRatioExercises
