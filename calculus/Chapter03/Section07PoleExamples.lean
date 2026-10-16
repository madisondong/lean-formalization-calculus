import calculus.Chapter03.Section07

/-! §3.7 — Ví dụ 3.7.16(a): so sánh hai vô cùng lớn tại 1; xét trị tuyệt đối vì 1/(1−x) đổi dấu. -/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07PoleExamples
open calculus.Chapter03.Section07 calculus.Chapter03.Section02


theorem punctured_one_nontrivial_and_eventually_ne :
    NontrivialDomainApproach univ (.point 1) ∧
      (∀ᶠ x in domainApproachFilter univ (.point 1), x ≠ 1) := by
  refine ⟨(properLimitApproach_point_iff univ 1).mpr (univ_accumulation 1), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hx.2


theorem pole_coordinates_infinite_magnitude :
    InfiniteMagnitudeAlong univ (.point 1) (fun x ↦ 1 / (x - 1) ^ 2) ∧
      InfiniteMagnitudeAlong univ (.point 1) (fun x ↦ 1 / (1 - x)) := by
  have hp := punctured_one_nontrivial_and_eventually_ne.1
  have hn := punctured_one_nontrivial_and_eventually_ne.2
  have hx : InfinitesimalAlong univ (.point 1) (fun x : ℝ ↦ x - 1) := by
    refine ⟨hp, ?_⟩
    have hc : ContinuousAt (fun x : ℝ ↦ x - 1) (1 : ℝ) :=
      continuous_id.continuousAt.sub continuous_const.continuousAt
    simpa only [domainApproachFilter, sub_self] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(1 : ℝ)}))
  have hs : InfinitesimalAlong univ (.point 1) (fun x : ℝ ↦ (x - 1) ^ 2) :=
    ⟨hp, by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hx.2.pow 2⟩
  have hy : InfinitesimalAlong univ (.point 1) (fun x : ℝ ↦ 1 - x) := by
    refine ⟨hp, ?_⟩
    have hc : ContinuousAt (fun x : ℝ ↦ 1 - x) (1 : ℝ) :=
      continuous_const.continuousAt.sub continuous_id.continuousAt
    simpa only [domainApproachFilter, sub_self] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(1 : ℝ)}))
  exact ⟨infinitesimalAlong_reciprocal_infinite hs
      (hn.mono fun x hx ↦ pow_ne_zero 2 (sub_ne_zero.mpr hx)),
    infinitesimalAlong_reciprocal_infinite hy
      (hn.mono fun x hx ↦ sub_ne_zero.mpr (Ne.symm hx))⟩

/-- Dòng 3354: 1/(x−1)² là vô cùng lớn bậc cao hơn 1/(1−x). -/
theorem square_pole_higher_than_simple_pole :
    LowerOrderInfiniteMagnitudeAlong univ (.point 1)
      (fun x ↦ 1 / (1 - x)) (fun x ↦ 1 / (x - 1) ^ 2) := by
  refine ⟨pole_coordinates_infinite_magnitude.2, pole_coordinates_infinite_magnitude.1,
    punctured_one_nontrivial_and_eventually_ne.1, ?_, ?_⟩
  · exact punctured_one_nontrivial_and_eventually_ne.2.mono fun x hx ↦
      one_div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx))
  · have ht : Tendsto (fun x : ℝ ↦ -(x - 1))
        (domainApproachFilter univ (.point 1)) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ ↦ x - 1) (1 : ℝ) :=
        continuous_id.continuousAt.sub continuous_const.continuousAt
      simpa only [domainApproachFilter, Pi.neg_def, sub_self, neg_zero] using
        hc.neg.tendsto.mono_left (nhdsWithin_le_nhds (s := univ \ {(1 : ℝ)}))
    apply ht.congr'
    filter_upwards [punctured_one_nontrivial_and_eventually_ne.2] with x hx
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have h2 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    field_simp [h1, h2]
    ring

end calculus.Chapter03.Section07PoleExamples
