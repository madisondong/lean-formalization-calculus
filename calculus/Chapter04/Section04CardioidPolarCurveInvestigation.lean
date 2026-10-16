import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

/-!
# Bài 4.4.16(a): cardioid r=1+cosφ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2793.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04CardioidPolarCurveInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

theorem cardioid_source_formula (θ : ℝ) : cosineRadius 1 θ = 1 + Real.cos θ := by
  simp only [cosineRadius, one_mul]

theorem cardioid_radius_bounds (θ : ℝ) : 0 ≤ cosineRadius 1 θ ∧ cosineRadius 1 θ ≤ 2 := by
  rw [cardioid_source_formula]
  constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

theorem cardioid_pole_iff (θ : ℝ) :
    signedPolarPoint (cosineRadius 1 θ) θ = 0 ↔ Real.cos θ = -1 := by
  rw [signedPolarPoint_eq_zero_iff, cardioid_source_formula]
  constructor <;> intro h <;> linarith

theorem cardioid_mem_curve_image_iff (z : ℂ) :
    z ∈ polarCurveImage (cosineRadius 1) ↔
      (z.re ^ 2 + z.im ^ 2 - z.re) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have hzero : ∃ θ : ℝ, cosineRadius 1 θ = 0 := by
    refine ⟨Real.pi, ?_⟩
    rw [cardioid_source_formula, Real.cos_pi]
    norm_num
  simpa only [cosineCartesian, one_mul] using! cosine_mem_curve_image_iff 1 hzero z


theorem cardioid_x_bounds (θ : ℝ) :
    -1 / 4 ≤ polarX (cosineRadius 1) θ ∧ polarX (cosineRadius 1) θ ≤ 2 ∧
      (polarX (cosineRadius 1) θ = -1 / 4 ↔ Real.cos θ = -1 / 2) ∧
      (polarX (cosineRadius 1) θ = 2 ↔ Real.cos θ = 1) := by
  have he : polarX (cosineRadius 1) θ = Real.cos θ + Real.cos θ ^ 2 := by
    dsimp only [polarX, cosineRadius]
    ring
  rw [he]
  have hc := Real.cos_le_one θ
  have hn := Real.neg_one_le_cos θ
  have hs := Real.sin_sq_add_cos_sq θ
  refine ⟨by nlinarith [sq_nonneg (Real.cos θ + 1 / 2)], by nlinarith [sq_nonneg (Real.sin θ)], ?_, ?_⟩
  · constructor
    · intro h
      have hz : (Real.cos θ + 1 / 2) ^ 2 = 0 := by nlinarith
      have hh := sq_eq_zero_iff.mp hz
      linarith
    · intro h
      rw [h]
      norm_num
  · constructor
    · intro h
      have hp : (Real.cos θ - 1) * (Real.cos θ + 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with h | h
      · linarith
      · linarith
    · intro h
      rw [h]
      norm_num

theorem cardioid_x_axis (x : ℝ) :
    (⟨x, 0⟩ : ℂ) ∈ polarCurveImage (cosineRadius 1) ↔ x = 0 ∨ x = 2 := by
  rw [cardioid_mem_curve_image_iff]
  change (x ^ 2 + 0 ^ 2 - x) ^ 2 = x ^ 2 + 0 ^ 2 ↔ _
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · have hh : x * (x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by linarith)
    · exact Or.inl (sq_eq_zero_iff.mp (by nlinarith : x ^ 2 = 0))
  · rintro (rfl | rfl) <;> norm_num

theorem cardioid_y_axis (y : ℝ) :
    (⟨0, y⟩ : ℂ) ∈ polarCurveImage (cosineRadius 1) ↔ y = 0 ∨ y = 1 ∨ y = -1 := by
  rw [cardioid_mem_curve_image_iff]
  change (0 ^ 2 + y ^ 2 - 0) ^ 2 = 0 ^ 2 + y ^ 2 ↔ _
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, sub_zero]
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · have hh : y * (y - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (by linarith))
    · have hh : y * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num


theorem cardioid_velocity_zero_iff (θ : ℝ) :
    (cosineXFirst 1 θ = 0 ∧ cosineYFirst 1 θ = 0) ↔ Real.cos θ = -1 := by
  have hs := cosine_speed_square 1 θ
  constructor
  · rintro ⟨hx, hy⟩
    rw [hx, hy] at hs
    nlinarith
  · intro hc
    have ht : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
    dsimp only [cosineXFirst, cosineYFirst]
    rw [hc, ht]
    norm_num


theorem cardioid_cusp_jets {θ : ℝ} (hc : Real.cos θ = -1) :
    polarX (cosineRadius 1) θ = 0 ∧ polarY (cosineRadius 1) θ = 0 ∧
      cosineXFirst 1 θ = 0 ∧ cosineYFirst 1 θ = 0 ∧
      cosineXSecond 1 θ = -1 ∧ cosineYSecond 1 θ = 0 ∧
      cosineXThird 1 θ = 0 ∧ cosineYThird 1 θ = -3 := by
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
  dsimp only [polarX, polarY, cosineRadius, cosineXFirst, cosineYFirst,
    cosineXSecond, cosineYSecond, cosineXThird, cosineYThird]
  rw [hc, hs]
  norm_num


theorem cardioid_cusp_x_secants_accumulate {θ : ℝ} (hc : Real.cos θ = -1) :
    AccumulationPointOf (xSecantDomain univ (cosineRadius 1) θ) θ := by
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
  have hx0 := (cardioid_cusp_jets hc).1
  intro δ hδ
  let u : ℝ := min (δ / 2) (Real.pi / 4)
  have hu : 0 < u := lt_min (by linarith) (by positivity)
  have hud : u < δ := (min_le_left _ _).trans_lt (by linarith)
  have hup : u < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hco : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hup⟩
  have hcu : Real.cos u < 1 := lt_of_le_of_ne (Real.cos_le_one u) (by
    intro h
    exact hu.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp h))
  have hcadd : Real.cos (θ + u) = -Real.cos u := by
    rw [Real.cos_add, hc, hs]
    ring
  refine ⟨θ + u, ⟨mem_univ _, ?_⟩, by linarith, by linarith, by linarith⟩
  rw [hx0, sub_zero]
  change cosineRadius 1 (θ + u) * Real.cos (θ + u) ≠ 0
  rw [cardioid_source_formula, hcadd]
  exact mul_ne_zero (by linarith) (neg_ne_zero.mpr hco.ne')


theorem cardioid_cusp_horizontal {θ : ℝ} (hc : Real.cos θ = -1) :
    HasHorizontalPolarTangent univ (cosineRadius 1) θ := by
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
  have hj := cardioid_cusp_jets hc
  have ha := cardioid_cusp_x_secants_accumulate hc
  apply (domainLimit_iff_tendsto ha).mpr
  have ht : Tendsto (fun t : ℝ ↦ Real.sin t / Real.cos t) (𝓝 θ) (𝓝 0) := by
    simpa only [hs, hc, zero_div] using!
      (Real.continuous_sin.continuousAt.tendsto.div Real.continuous_cos.continuousAt.tendsto
        (by rw [hc]; norm_num : Real.cos θ ≠ 0))
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hx : polarX (cosineRadius 1) t ≠ 0 := by
    simpa only [hj.1, sub_zero] using ht.1.2
  change cosineRadius 1 t * Real.cos t ≠ 0 at hx
  have hn : cosineRadius 1 t ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hcn : Real.cos t ≠ 0 := (mul_ne_zero_iff.mp hx).2
  rw [hj.1, hj.2.1]
  dsimp only [polarX, polarY]
  simp only [sub_zero]
  field_simp [hn, hcn]


theorem cardioid_cusp_not_vertical {θ : ℝ} (hc : Real.cos θ = -1) :
    ¬ HasVerticalPolarTangent univ (cosineRadius 1) θ := by
  intro hv
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
  have hj := cardioid_cusp_jets hc
  let F := 𝓝[ySecantDomain univ (cosineRadius 1) θ \ {θ}] θ
  let : NeBot F := accumulationPointOf_iff_neBot.mp hv.1
  have hl : Tendsto (fun t : ℝ ↦
      (polarX (cosineRadius 1) t - polarX (cosineRadius 1) θ) /
        (polarY (cosineRadius 1) t - polarY (cosineRadius 1) θ)) F (𝓝 0) :=
    (domainLimit_iff_tendsto hv.1).mp hv
  have hr : Tendsto (fun t : ℝ ↦ Real.sin t / Real.cos t) F (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ Real.sin t / Real.cos t) (𝓝 θ) (𝓝 0) := by
      simpa only [hs, hc, zero_div] using!
        (Real.continuous_sin.continuousAt.tendsto.div Real.continuous_cos.continuousAt.tendsto
          (by rw [hc]; norm_num : Real.cos θ ≠ 0))
    exact ht.mono_left nhdsWithin_le_nhds
  have hh := hl.mul hr
  simp only [mul_zero] at hh
  have hco : ∀ᶠ t : ℝ in F, Real.cos t ≠ 0 :=
    (Real.continuous_cos.continuousAt.tendsto.eventually_ne
      (by rw [hc]; norm_num : Real.cos θ ≠ 0)).filter_mono nhdsWithin_le_nhds
  have hunit : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) F (𝓝 0) := by
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin, hco] with t ht hct
    have hy : polarY (cosineRadius 1) t ≠ 0 := by
      simpa only [hj.2.1, sub_zero] using ht.1.2
    change cosineRadius 1 t * Real.sin t ≠ 0 at hy
    have hn : cosineRadius 1 t ≠ 0 := (mul_ne_zero_iff.mp hy).1
    have hsn : Real.sin t ≠ 0 := (mul_ne_zero_iff.mp hy).2
    rw [hj.1, hj.2.1]
    dsimp only [polarX, polarY]
    simp only [sub_zero]
    field_simp [hn, hsn, hct]
  exact zero_ne_one (tendsto_nhds_unique hunit tendsto_const_nhds)


theorem cardioid_horizontal_iff (θ : ℝ) :
    HasHorizontalPolarTangent univ (cosineRadius 1) θ ↔
      Real.cos θ = 1 / 2 ∨ Real.cos θ = -1 := by
  constructor
  · intro h
    have hy := cosine_horizontal_necessary h
    dsimp only [cosineYFirst] at hy
    have hp : (2 * Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hc | hc)
    · apply cosine_horizontal_of
      · dsimp only [cosineYFirst]
        nlinarith [Real.sin_sq_add_cos_sq θ]
      · have hs : Real.sin θ ≠ 0 := by
          intro hs
          have ht := Real.sin_sq_add_cos_sq θ
          rw [hs, hc] at ht
          norm_num at ht
        dsimp only [cosineXFirst]
        rw [hc]
        exact mul_ne_zero (neg_ne_zero.mpr hs) (by norm_num)
    · exact cardioid_cusp_horizontal hc


theorem cardioid_vertical_iff (θ : ℝ) :
    HasVerticalPolarTangent univ (cosineRadius 1) θ ↔
      Real.cos θ = 1 ∨ Real.cos θ = -1 / 2 := by
  constructor
  · intro h
    have hx := cosine_vertical_necessary h
    dsimp only [cosineXFirst] at hx
    rcases mul_eq_zero.mp hx with hs | hc
    · have hs0 : Real.sin θ = 0 := neg_eq_zero.mp hs
      rcases Real.sin_eq_zero_iff_cos_eq.mp hs0 with hc | hc
      · exact Or.inl hc
      · exact (cardioid_cusp_not_vertical hc h).elim
    · exact Or.inr (by linarith)
  · rintro (hc | hc)
    all_goals apply cosine_vertical_of
    · have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hc)
      dsimp only [cosineXFirst]
      rw [hs]
      simp only [neg_zero, zero_mul]
    · dsimp only [cosineYFirst]
      have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hc)
      rw [hc, hs]
      norm_num
    · dsimp only [cosineXFirst]
      rw [hc]
      norm_num
    · dsimp only [cosineYFirst]
      have ht := Real.sin_sq_add_cos_sq θ
      intro h
      nlinarith


theorem cardioid_speed_sq_and_curvature_numerator_positive (θ : ℝ) (hc : Real.cos θ ≠ -1) :
    0 < cosineXFirst 1 θ ^ 2 + cosineYFirst 1 θ ^ 2 ∧
      0 < cosineXFirst 1 θ * cosineYSecond 1 θ - cosineYFirst 1 θ * cosineXSecond 1 θ := by
  rw [cosine_speed_square, cosine_curvature_numerator]
  have hp : -1 < Real.cos θ := lt_of_le_of_ne (Real.neg_one_le_cos θ) hc.symm
  constructor <;> nlinarith


theorem cardioid_cusp_y_signs {θ : ℝ} (hc : Real.cos θ = -1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ u : ℝ, 0 < u ∧ u < δ ∧
      0 < polarY (cosineRadius 1) (θ - u) ∧ polarY (cosineRadius 1) (θ + u) < 0 := by
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
  let u : ℝ := min (δ / 2) (Real.pi / 4)
  have hu : 0 < u := lt_min (by linarith) (by positivity)
  have hud : u < δ := (min_le_left _ _).trans_lt (by linarith)
  have hup : u < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hcu : Real.cos u < 1 := lt_of_le_of_ne (Real.cos_le_one u) (by
    intro h
    exact hu.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp h))
  have hminus : polarY (cosineRadius 1) (θ - u) = (1 - Real.cos u) * Real.sin u := by
    dsimp only [polarY, cosineRadius]
    rw [Real.cos_sub, Real.sin_sub, hc, hs]
    ring
  have hplus : polarY (cosineRadius 1) (θ + u) = -(1 - Real.cos u) * Real.sin u := by
    dsimp only [polarY, cosineRadius]
    rw [Real.cos_add, Real.sin_add, hc, hs]
    ring
  refine ⟨u, hu, hud, ?_, ?_⟩
  · rw [hminus]
    exact mul_pos (sub_pos.mpr hcu) hsu
  · rw [hplus]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hcu)) hsu

theorem cardioid_cusp_coordinate_extrema {θ : ℝ} (hc : Real.cos θ = -1) :
    IsLocalMaximumOn (polarX (cosineRadius 1)) univ θ ∧
      ¬ IsLocalMinimumOn (polarX (cosineRadius 1)) univ θ ∧
      ¬ IsLocalMinimumOn (polarY (cosineRadius 1)) univ θ ∧
      ¬ IsLocalMaximumOn (polarY (cosineRadius 1)) univ θ := by
  have hj := cardioid_cusp_jets hc
  have hx0 : deriv (polarX (cosineRadius 1)) θ = 0 := by
    rw [(cosineX_hasDerivAt 1 θ).deriv]
    exact hj.2.2.1
  have hx2 : deriv (deriv (polarX (cosineRadius 1))) θ = -1 := by
    rw [(cosineX_second_hasDerivAt 1 θ).deriv]
    exact hj.2.2.2.2.1
  have hmax : IsLocalMaximumOn (polarX (cosineRadius 1)) univ θ :=
    (source_maximum_univ_iff _ θ).mpr
      (isLocalMax_of_deriv_deriv_neg (by rw [hx2]; norm_num) hx0
        (cosineX_hasDerivAt 1 θ).continuousAt)
  refine ⟨hmax, ?_, ?_, ?_⟩
  · intro hmin
    have h := second_zero_of_both_extrema hmin hmax
    rw [hx2] at h
    norm_num at h
  · intro hmin
    obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp ((source_minimum_univ_iff _ θ).mp hmin)
    obtain ⟨u, hu, hud, _, hneg⟩ := cardioid_cusp_y_signs hc δ hδ
    have h := hd (y := θ + u) (by
      rw [Real.dist_eq, show θ + u - θ = u by ring, abs_of_pos hu]
      exact hud)
    rw [hj.2.1] at h
    exact (not_le_of_gt hneg) h
  · intro hmaxY
    obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp ((source_maximum_univ_iff _ θ).mp hmaxY)
    obtain ⟨u, hu, hud, hpos, _⟩ := cardioid_cusp_y_signs hc δ hδ
    have h := hd (y := θ - u) (by
      rw [Real.dist_eq, show θ - u - θ = -u by ring, abs_neg, abs_of_pos hu]
      exact hud)
    rw [hj.2.1] at h
    exact (not_le_of_gt hpos) h


theorem cardioid_coordinate_extrema_regular (θ : ℝ) (hc : Real.cos θ ≠ -1) :
    ((IsLocalMinimumOn (polarX (cosineRadius 1)) univ θ ↔
      cosineXFirst 1 θ = 0 ∧ 0 < cosineXSecond 1 θ) ∧
    (IsLocalMaximumOn (polarX (cosineRadius 1)) univ θ ↔
      cosineXFirst 1 θ = 0 ∧ cosineXSecond 1 θ < 0)) ∧
    ((IsLocalMinimumOn (polarY (cosineRadius 1)) univ θ ↔
      cosineYFirst 1 θ = 0 ∧ 0 < cosineYSecond 1 θ) ∧
    (IsLocalMaximumOn (polarY (cosineRadius 1)) univ θ ↔
      cosineYFirst 1 θ = 0 ∧ cosineYSecond 1 θ < 0)) :=
  cosine_coordinate_extrema (cardioid_speed_sq_and_curvature_numerator_positive θ hc).2


theorem source_cardioid_complete_polar_curve_investigation :
    (∀ θ : ℝ, cosineRadius 1 θ = 1 + Real.cos θ ∧
      0 ≤ cosineRadius 1 θ ∧ cosineRadius 1 θ ≤ 2) ∧
    (∀ z : ℂ, z ∈ polarCurveImage (cosineRadius 1) ↔
      (z.re ^ 2 + z.im ^ 2 - z.re) ^ 2 = z.re ^ 2 + z.im ^ 2) ∧
    (∀ θ : ℝ, signedPolarPoint (cosineRadius 1 θ) θ = 0 ↔ Real.cos θ = -1) ∧
    (∀ θ : ℝ, HasDerivAt (cosineRadius 1) (-Real.sin θ) θ ∧
      HasDerivAt (polarX (cosineRadius 1)) (cosineXFirst 1 θ) θ ∧
      HasDerivAt (polarY (cosineRadius 1)) (cosineYFirst 1 θ) θ ∧
      HasDerivAt (deriv (polarX (cosineRadius 1))) (cosineXSecond 1 θ) θ ∧
      HasDerivAt (deriv (polarY (cosineRadius 1))) (cosineYSecond 1 θ) θ ∧
      HasDerivAt (deriv (deriv (polarX (cosineRadius 1)))) (cosineXThird 1 θ) θ ∧
      HasDerivAt (deriv (deriv (polarY (cosineRadius 1)))) (cosineYThird 1 θ) θ) ∧
    (∀ θ : ℝ, (IsLocalMinimumOn (cosineRadius 1) univ θ ↔ Real.cos θ = -1) ∧
      (IsLocalMaximumOn (cosineRadius 1) univ θ ↔ Real.cos θ = 1)) ∧
    (∀ θ : ℝ, -1 / 4 ≤ polarX (cosineRadius 1) θ ∧ polarX (cosineRadius 1) θ ≤ 2 ∧
      (polarX (cosineRadius 1) θ = -1 / 4 ↔ Real.cos θ = -1 / 2) ∧
      (polarX (cosineRadius 1) θ = 2 ↔ Real.cos θ = 1)) ∧
    (∀ x : ℝ, (⟨x, 0⟩ : ℂ) ∈ polarCurveImage (cosineRadius 1) ↔ x = 0 ∨ x = 2) ∧
    (∀ y : ℝ, (⟨0, y⟩ : ℂ) ∈ polarCurveImage (cosineRadius 1) ↔ y = 0 ∨ y = 1 ∨ y = -1) ∧
    (∀ z : ℂ, z ∈ polarCurveImage (cosineRadius 1) ↔
      polarAxisReflection z ∈ polarCurveImage (cosineRadius 1)) ∧
    (∀ θ : ℝ, signedPolarPoint (cosineRadius 1 (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
      signedPolarPoint (cosineRadius 1 θ) θ) ∧
    (∀ θ : ℝ, HasHorizontalPolarTangent univ (cosineRadius 1) θ ↔
      Real.cos θ = 1 / 2 ∨ Real.cos θ = -1) ∧
    (∀ θ : ℝ, HasVerticalPolarTangent univ (cosineRadius 1) θ ↔
      Real.cos θ = 1 ∨ Real.cos θ = -1 / 2) ∧
    (∀ θ : ℝ, Real.cos θ = -1 →
      polarX (cosineRadius 1) θ = 0 ∧ polarY (cosineRadius 1) θ = 0 ∧
      cosineXFirst 1 θ = 0 ∧ cosineYFirst 1 θ = 0 ∧
      cosineXSecond 1 θ = -1 ∧ cosineYSecond 1 θ = 0 ∧
      cosineXThird 1 θ = 0 ∧ cosineYThird 1 θ = -3) ∧
    (∀ θ : ℝ, Real.cos θ ≠ -1 →
      0 < cosineXFirst 1 θ ^ 2 + cosineYFirst 1 θ ^ 2 ∧
      0 < cosineXFirst 1 θ * cosineYSecond 1 θ - cosineYFirst 1 θ * cosineXSecond 1 θ) ∧
    (∀ θ ψ : ℝ, θ ∈ Ico 0 (2 * Real.pi) → ψ ∈ Ico 0 (2 * Real.pi) →
      cosineRadius 1 θ ≠ 0 →
      signedPolarPoint (cosineRadius 1 θ) θ = signedPolarPoint (cosineRadius 1 ψ) ψ → θ = ψ) := by
  refine ⟨fun θ ↦ ⟨cardioid_source_formula θ, cardioid_radius_bounds θ⟩,
    cardioid_mem_curve_image_iff, cardioid_pole_iff, ?_, fun θ ↦ cosine_radius_extrema 1 θ (by norm_num),
    cardioid_x_bounds, cardioid_x_axis, cardioid_y_axis, cosine_axis_symmetry 1,
    cosine_point_periodic 1, cardioid_horizontal_iff, cardioid_vertical_iff,
    fun _ hc ↦ cardioid_cusp_jets hc, cardioid_speed_sq_and_curvature_numerator_positive,
    fun _ _ hθ hψ hn he ↦ cosine_point_injective_off_pole hθ hψ hn he⟩
  intro θ
  exact ⟨by simpa only [neg_one_mul] using cosineRadius_hasDerivAt 1 θ,
    cosineX_hasDerivAt 1 θ, cosineY_hasDerivAt 1 θ,
    cosineX_second_hasDerivAt 1 θ, cosineY_second_hasDerivAt 1 θ,
    cosineX_third_hasDerivAt 1 θ, cosineY_third_hasDerivAt 1 θ⟩

end calculus.Chapter04.Section04CardioidPolarCurveInvestigation
