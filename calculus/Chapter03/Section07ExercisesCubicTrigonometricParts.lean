import calculus.Chapter03.Section07Examples
import calculus.Chapter03.Section07Orders
import calculus.Chapter03.Section03Exercises

/-!
# §3.7 — phần chính bậc ba của sin và tang

Nguồn: Ví dụ 3.7.21(a), dòng 3385–3386; Bài tập 3.7.3(c), dòng 3489; Bài tập 3.7.11(k,l), dòng 3693–3694.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesCubicTrigonometricParts

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07Orders


def tangentDomain : Set ℝ := {x | Real.cos x ≠ 0}


def cubicTangentQuotientDomain : Set ℝ := {x | Real.cos x ≠ 0 ∧ x ≠ 0}


theorem tangent_domain_nhds : tangentDomain ∈ 𝓝 (0 : ℝ) := by
  exact (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.eventually_ne
    (by norm_num : Real.cos (0 : ℝ) ≠ 0)


theorem tangent_domain_accumulation : AccumulationPointOf tangentDomain 0 := by
  simpa only [univ_inter] using
    accumulationPointOf_inter_nhds (univ_accumulation 0) tangent_domain_nhds


theorem cubic_tangent_quotient_accumulation :
    AccumulationPointOf cubicTangentQuotientDomain 0 := by
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hu⟩ := tangent_domain_accumulation δ hδ
  exact ⟨x, ⟨hx, hn⟩, hn, hl, hu⟩


theorem one_sub_cos_half_square (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]


theorem one_sub_cos_div_square_tendsto :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ Real.sinc (x / 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.sinc (x / 2)) 0 :=
      Real.continuous_sinc.continuousAt.comp (continuous_id.div_const 2).continuousAt
    simpa only [domainApproachFilter, zero_div, Real.sinc_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ ↦ (1 / 2 : ℝ) * Real.sinc (x / 2) ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [one_pow, mul_one] using (hs.pow 2).const_mul (1 / 2 : ℝ)
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num)), one_sub_cos_half_square]
  field_simp [hx]


theorem sine_sub_tangent_div_cube_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.sin x - Real.tan x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  have ht : Tendsto (fun x : ℝ ↦
      -((Real.sin x / x) * ((1 - Real.cos x) / x ^ 2) / Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply, one_mul, div_one, neg_div] using
      ((sine_equivalent_identity_zero.2.2.mul one_sub_cos_div_square_tendsto).div hc
        (by norm_num : (1 : ℝ) ≠ 0)).neg
  apply ht.congr'
  filter_upwards [punctured_zero_eventually_ne, tangent_eventually_defined_zero] with x hx hcos
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx, hcos]
  ring


theorem hasPowerPrincipalPartAlong_nat_of_tendsto
    {D : Set ℝ} {f : ℝ → ℝ} {n : ℕ} {C : ℝ}
    (ha : AccumulationPointOf D 0) (hn : 0 < n) (hC : C ≠ 0)
    (hf : Tendsto f (domainApproachFilter D (.point 0)) (𝓝 0))
    (ht : Tendsto (fun x ↦ f x / x ^ n) (domainApproachFilter D (.point 0)) (𝓝 C)) :
    HasPowerPrincipalPartAlong D (.point 0) f (fun x ↦ x) (n : ℝ) C := by
  have hp := (properLimitApproach_point_iff D 0).mpr ha
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter D (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ x in domainApproachFilter D (.point 0), x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx.2
  have hpn : ∀ᶠ x in domainApproachFilter D (.point 0), x ^ n ≠ 0 :=
    hne.mono fun x hx ↦ pow_ne_zero n hx
  have had : EventuallyRealPowerDefinedAlong D (.point 0) (fun x ↦ x) (n : ℝ) := by
    have hz : 0 < (n : ℤ) := by exact_mod_cast hn
    have hd : realPowerDomain (n : ℝ) = (univ : Set ℝ) := by
      simpa only [Int.cast_natCast] using positive_integer_power_domain n hz
    exact Filter.Eventually.of_forall fun x ↦ by simp [hd]
  have ho : InfinitesimalPowerOrderAlong D (.point 0) f (fun x ↦ x) (n : ℝ) := by
    refine ⟨by exact_mod_cast hn, ⟨hp, hf⟩, ⟨hp, hi⟩, had, hp, ?_, C, hC, ?_⟩
    · simpa only [Real.rpow_natCast] using hpn
    · simpa only [Real.rpow_natCast] using ht
  refine ⟨Or.inl ho, hC, hp, ?_, ?_⟩
  · simpa only [powerPrincipalPart, Real.rpow_natCast] using
      hpn.mono (fun x hx ↦ mul_ne_zero hC hx)
  · have hscaled : Tendsto (fun x ↦ (f x / x ^ n) / C)
        (domainApproachFilter D (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [div_self hC] using ht.div_const C
    apply hscaled.congr'
    exact Eventually.of_forall fun x ↦ by
      simp only [powerPrincipalPart, Real.rpow_natCast]
      rw [div_div, mul_comm (x ^ n) C]


theorem sine_sub_tangent_infinitesimal :
    Tendsto (fun x : ℝ ↦ Real.sin x - Real.tan x)
      (domainApproachFilter tangentDomain (.point 0)) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto Real.tan (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    apply (show Tendsto (fun x : ℝ ↦ (Real.tan x / x) * x)
      (domainApproachFilter univ (.point 0)) (𝓝 0) from by
        simpa only [mul_zero] using tangent_equivalent_identity_zero.2.2.mul hi).congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    exact div_mul_cancel₀ (Real.tan x) hx
  have hs : Tendsto Real.sin (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [domainApproachFilter, Real.sin_zero] using
      (Real.continuous_sin.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  have hsub : Tendsto (fun x : ℝ ↦ Real.sin x - Real.tan x)
      (domainApproachFilter univ (.point 0)) (𝓝 0) := by
    simpa only [sub_zero] using hs.sub ht
  exact hsub.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ tangentDomain)))

/-- Ví dụ 3.7.21(a): phần chính −x³/2, bậc 3. -/
theorem sine_sub_tangent_principal_part :
    HasPowerPrincipalPartAlong tangentDomain (.point 0)
      (fun x ↦ Real.sin x - Real.tan x) (fun x ↦ x) 3 (-1 / 2) := by
  apply hasPowerPrincipalPartAlong_nat_of_tendsto
    tangent_domain_accumulation (by norm_num : 0 < (3 : ℕ)) (by norm_num)
    sine_sub_tangent_infinitesimal
  exact sine_sub_tangent_div_cube_tendsto.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ tangentDomain)))

/-- Bài tập 3.7.3(c): phần chính x³/2, bậc 3. -/
theorem tangent_sub_sine_principal_part :
    HasPowerPrincipalPartAlong tangentDomain (.point 0)
      (fun x ↦ Real.tan x - Real.sin x) (fun x ↦ x) 3 (1 / 2) := by
  have hf : Tendsto (fun x : ℝ ↦ Real.tan x - Real.sin x)
      (domainApproachFilter tangentDomain (.point 0)) (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using sine_sub_tangent_infinitesimal.neg
  apply hasPowerPrincipalPartAlong_nat_of_tendsto
    tangent_domain_accumulation (by norm_num : 0 < (3 : ℕ)) (by norm_num) hf
  have ht := sine_sub_tangent_div_cube_tendsto.neg
  have hnorm : Tendsto (fun x : ℝ ↦ (Real.tan x - Real.sin x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.neg_apply, ← neg_div, neg_sub, neg_neg] using! ht
  exact hnorm.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ tangentDomain)))

/-- Bài tập 3.7.11(l): giới hạn thương trên miền x≠0. -/
theorem sine_sub_tangent_div_cube_domainLimit :
    DomainLimit cubicTangentQuotientDomain
      (fun x ↦ (Real.sin x - Real.tan x) / x ^ 3) 0 (-1 / 2) := by
  apply (domainLimit_iff_tendsto cubic_tangent_quotient_accumulation).mpr
  exact sine_sub_tangent_div_cube_tendsto.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ cubicTangentQuotientDomain)))

/-- Bài tập 3.7.11(k): (tan x−sin x cos x)/x³→1. -/
theorem tangent_sub_sine_cos_div_cube_domainLimit :
    DomainLimit cubicTangentQuotientDomain
      (fun x ↦ (Real.tan x - Real.sin x * Real.cos x) / x ^ 3) 0 1 := by
  have hc : Tendsto Real.cos (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [domainApproachFilter, Real.cos_zero] using
      (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := univ \ {(0 : ℝ)}))
  have ht : Tendsto (fun x : ℝ ↦ (Real.sin x / x) ^ 3 / Real.cos x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, one_pow, div_one] using!
      (sine_equivalent_identity_zero.2.2.pow 3).div hc (by norm_num : (1 : ℝ) ≠ 0)
  have hnorm : Tendsto (fun x : ℝ ↦ (Real.tan x - Real.sin x * Real.cos x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne, tangent_eventually_defined_zero] with x hx hcos
    have hid : Real.sin x * (Real.sin x ^ 2 + Real.cos x ^ 2) = Real.sin x := by
      rw [Real.sin_sq_add_cos_sq]
      ring
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hx, hcos]
    nlinarith [hid]
  apply (domainLimit_iff_tendsto cubic_tangent_quotient_accumulation).mpr
  exact hnorm.mono_left
    (nhdsWithin_mono 0 (sdiff_subset_sdiff_left (subset_univ cubicTangentQuotientDomain)))

end calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
