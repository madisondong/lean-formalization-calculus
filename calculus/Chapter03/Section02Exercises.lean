import calculus.Chapter03.Section02Infinite

/-!
§3.2 — bài tập giới hạn hàm số

Nguồn: dòng 1976–2043.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section02Exercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite calculus.Chapter02.Section03


theorem domainLimit_of_continuousAt {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) (hf : ContinuousAt f a) : DomainLimit D f a (f a) :=
  (domainLimit_iff_tendsto ha).mpr (hf.tendsto.mono_left nhdsWithin_le_nhds)


theorem punctured_univ_accumulation (a b : ℝ) : AccumulationPointOf (univ \ {b}) a := by
  intro δ hδ
  by_cases hb : a + δ / 2 = b
  · refine ⟨a - δ / 2, ?_, by linarith, by linarith, by linarith⟩
    simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
    linarith
  · exact ⟨a + δ / 2, by simpa using hb, by linarith, by linarith, by linarith⟩

theorem accumulationPointOf_mono {D E : Set ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) (hDE : D ⊆ E) : AccumulationPointOf E a := by
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hr⟩ := ha δ hδ
  exact ⟨x, hDE hx, hn, hl, hr⟩

theorem nonnegative_halfline_accumulation {a : ℝ} (ha : 0 ≤ a) :
    AccumulationPointOf (Ici (0 : ℝ)) a := by
  intro δ hδ
  exact ⟨a + δ / 2, (show 0 ≤ a + δ / 2 by linarith), by linarith, by linarith, by linarith⟩

/-- Bài tập 3.2.1: năm giới hạn trên các miền tự nhiên. -/
theorem affine_limit_at_two : DomainLimit univ (fun x ↦ 3 * x - 7) 2 (-1) := by
  have hf : Continuous (fun x : ℝ ↦ 3 * x - 7) :=
    (continuous_const.mul continuous_id).sub continuous_const
  convert domainLimit_of_continuousAt (univ_accumulation 2) hf.continuousAt using 1; norm_num

theorem quadratic_limit_at_three : DomainLimit univ (fun x ↦ x ^ 2 + 1) 3 10 := by
  have hf : Continuous (fun x : ℝ ↦ x ^ 2 + 1) := (continuous_id.pow 2).add continuous_const
  convert domainLimit_of_continuousAt (univ_accumulation 3) hf.continuousAt using 1; norm_num

theorem rational_limit_at_one :
    DomainLimit (univ \ {(-1 : ℝ)}) (fun x ↦ (x + 3) / (x + 1)) 1 2 := by
  have hf : ContinuousAt (fun x : ℝ ↦ (x + 3) / (x + 1)) 1 :=
    (continuous_id.add continuous_const).continuousAt.div
      (continuous_id.add continuous_const).continuousAt (by norm_num)
  convert domainLimit_of_continuousAt (punctured_univ_accumulation 1 (-1)) hf using 1; norm_num

theorem sqrt_limit_at_four : DomainLimit (Ici (0 : ℝ)) Real.sqrt 4 2 := by
  have hs : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  simpa only [hs] using domainLimit_of_continuousAt (nonnegative_halfline_accumulation (by norm_num : (0 : ℝ) ≤ 4))
    (show ContinuousAt Real.sqrt 4 from Real.continuous_sqrt.continuousAt)

theorem cubic_limit_at_negative_two : DomainLimit univ (fun x ↦ x ^ 3) (-2) (-8) := by
  convert domainLimit_of_continuousAt (univ_accumulation (-2))
    (show ContinuousAt (fun x : ℝ ↦ x ^ 3) (-2) from (continuous_id.pow 3).continuousAt) using 1; norm_num

/-- Bài tập 3.2.2(a): x/|x| không có giới hạn tại 0. -/
theorem div_abs_no_domainLimit :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ x / |x|) 0 := by
  have heq : ∀ x : ℝ, x ≠ 0 → x / |x| = |x| / x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · rw [abs_of_neg hn, div_neg, div_self hx, neg_div, div_self hx]
    · rw [abs_of_pos hp]
  intro h
  obtain ⟨L, hL⟩ := h
  exact absolute_div_self_no_domainLimit ⟨L,
    (domainLimit_congr_punctured (fun x _ hx ↦ heq x hx)).mp hL⟩

theorem sine_reciprocal_exercise_no_limit :
    ¬ HasDomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ Real.sin (1 / x)) 0 :=
  sine_reciprocal_no_domainLimit

/-- Bài tập 3.2.3(a): giới hạn một phía của hàm dấu tịnh tiến. -/
theorem absolute_ratio_left_at_one :
    DomainLeftLimit (univ \ {(1 : ℝ)}) (fun x ↦ |x - 1| / (x - 1)) 1 (-1) := by
  refine ⟨leftAccumulation_univ_diff 1, fun ε hε ↦ ⟨1, zero_lt_one, ?_⟩⟩
  intro x _ _ hx
  change abs (abs (x - 1) / (x - 1) - (-1)) < ε
  rw [abs_of_neg (by linarith : x - 1 < 0), neg_div,
    div_self (by linarith : x - 1 ≠ 0), sub_self, abs_zero]
  exact hε

/-- Bài tập 3.2.3(b): giới hạn phải của 2x²+3 tại −1 bằng 5. -/
theorem quadratic_right_at_negative_one :
    DomainRightLimit univ (fun x ↦ 2 * x ^ 2 + 3) (-1) 5 := by
  have hf : Continuous (fun x : ℝ ↦ 2 * x ^ 2 + 3) :=
    (continuous_const.mul (continuous_id.pow 2)).add continuous_const
  have h := domainLimit_of_continuousAt (univ_accumulation (-1)) hf.continuousAt
  have hh := ((domainLimit_iff_left_right (leftAccumulation_univ (-1))
    (rightAccumulation_univ (-1))).mp h).2
  norm_num at hh ⊢
  exact hh


def quadraticPoleDomain : Set ℝ := {x : ℝ | x ≠ -2 ∧ x ≠ 2}

theorem quadraticPoleDomain_right_accumulation : RightAccumulationPointOf quadraticPoleDomain 2 := by
  intro δ hδ
  refine ⟨2 + δ / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem quadraticPoleDomain_left_accumulation : LeftAccumulationPointOf quadraticPoleDomain 2 := by
  intro δ hδ
  have hm : 0 < min δ 1 := lt_min hδ zero_lt_one
  refine ⟨2 - min δ 1 / 2, ⟨by linarith [min_le_right δ (1 : ℝ)], by linarith⟩,
    by linarith [min_le_left δ (1 : ℝ)], by linarith⟩

/-- Bài tập 3.2.3(c): giới hạn phải bằng +∞ trên miền tự nhiên. -/
theorem quadratic_reciprocal_right_top :
    DomainRightTopLimit quadraticPoleDomain (fun x ↦ 1 / (x ^ 2 - 4)) 2 := by
  refine ⟨quadraticPoleDomain_right_accumulation, ?_⟩
  have hc : Continuous (fun x : ℝ ↦ x ^ 2 - 4) := (continuous_id.pow 2).sub continuous_const
  have h0 : Tendsto (fun x : ℝ ↦ x ^ 2 - 4) (𝓝[quadraticPoleDomain ∩ Ioi 2] 2) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ ↦ x ^ 2 - 4) 2 := hc.continuousAt
    convert h.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have hp : ∀ᶠ x in 𝓝[quadraticPoleDomain ∩ Ioi 2] (2 : ℝ), 0 < x ^ 2 - 4 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hh : 2 < x := hx.2
    nlinarith
  exact (tendsto_nhdsWithin_iff.mpr ⟨h0, hp⟩).inv_tendsto_nhdsGT_zero.congr
    fun x ↦ by simp only [Pi.inv_apply, one_div]

/-- Bài tập 3.2.3(d): giới hạn trái bằng −∞. -/
theorem quadratic_reciprocal_left_bot :
    DomainLeftBotLimit quadraticPoleDomain (fun x ↦ 1 / (x ^ 2 - 4)) 2 := by
  refine ⟨quadraticPoleDomain_left_accumulation, ?_⟩
  have hc : Continuous (fun x : ℝ ↦ x ^ 2 - 4) := (continuous_id.pow 2).sub continuous_const
  have h0 : Tendsto (fun x : ℝ ↦ x ^ 2 - 4) (𝓝[quadraticPoleDomain ∩ Iio 2] 2) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ ↦ x ^ 2 - 4) 2 := hc.continuousAt
    convert h.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have hnear : ∀ᶠ x in 𝓝[quadraticPoleDomain ∩ Iio 2] (2 : ℝ), 1 < x :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hp : ∀ᶠ x in 𝓝[quadraticPoleDomain ∩ Iio 2] (2 : ℝ), x ^ 2 - 4 < 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx hxl
    have hh : x < 2 := hx.2
    nlinarith
  exact (tendsto_nhdsWithin_iff.mpr ⟨h0, hp⟩).inv_tendsto_nhdsLT_zero.congr
    fun x ↦ by simp only [Pi.inv_apply, one_div]




def squareRootRatioDomain : Set ℝ := {x : ℝ | x < -1 ∨ 1 < x}

/-- Bài tập 3.2.4(a): giới hạn tại −∞ trên miền tự nhiên. -/
theorem squareRootRatio_atBot_limit :
    DomainAtBotLimit squareRootRatioDomain (fun x ↦ x / Real.sqrt (x ^ 2 - 1)) (-1) := by
  have hD : ¬ BddBelow squareRootRatioDomain := by
    rintro ⟨m, hm⟩
    have hx : min m (-2) - 1 ∈ squareRootRatioDomain := by
      left
      linarith [min_le_right m (-2 : ℝ)]
    have hh := hm hx
    linarith [min_le_left m (-2 : ℝ)]
  apply (domainAtBotLimit_iff_tendsto hD).mpr
  have hi : Tendsto (fun x : ℝ ↦ 1 / x ^ 2) atBot (𝓝 0) := by
    have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
    have hh := hinv.pow 2
    simpa only [inv_pow, one_div, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hh
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (1 - 1 / x ^ 2)) atBot (𝓝 1) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hi)
    simpa only [sub_zero, Real.sqrt_one, Function.comp_def] using hh
  have hh : Tendsto (fun x : ℝ ↦ -(1 / Real.sqrt (1 - 1 / x ^ 2))) atBot (𝓝 (-1)) := by
    have hr := (tendsto_const_nhds (x := (1 : ℝ))).div hs (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun x : ℝ ↦ 1 / Real.sqrt (1 - 1 / x ^ 2)) atBot (𝓝 (1 / 1)) at hr
    simpa only [div_one] using hr.neg
  have heq : (fun x : ℝ ↦ -(1 / Real.sqrt (1 - 1 / x ^ 2))) =ᶠ[atBot]
      (fun x ↦ x / Real.sqrt (x ^ 2 - 1)) := by
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    have hn : x < 0 := by linarith
    have hx0 : x ≠ 0 := ne_of_lt hn
    have hp : x ^ 2 - 1 = x ^ 2 * (1 - 1 / x ^ 2) := by field_simp [hx0]
    have hroot : Real.sqrt (x ^ 2 - 1) = -x * Real.sqrt (1 - 1 / x ^ 2) := by
      rw [hp, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_neg hn]
    rw [hroot, div_mul_eq_div_div, div_neg, div_self hx0, neg_div]
  exact (hh.congr' heq).mono_left inf_le_left


theorem quadratic_linear_ratio_atTop_bot :
    DomainAtTopBotLimit (univ \ {(1 : ℝ)}) (fun x ↦ x ^ 2 / (1 - x)) := by
  have hD : ¬ BddAbove (univ \ {(1 : ℝ)}) := by
    rintro ⟨m, hm⟩
    have hx : max m 1 + 1 ∈ univ \ {(1 : ℝ)} := by
      simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
      linarith [le_max_right m (1 : ℝ)]
    have hh := hm hx
    linarith [le_max_left m (1 : ℝ)]
  refine ⟨hD, ?_⟩
  refine (show Tendsto (fun x : ℝ ↦ x ^ 2 / (1 - x)) atTop atBot from ?_).mono_left inf_le_left
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [eventually_ge_atTop (max (2 : ℝ) (-M))] with x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hM : -M ≤ x := (le_max_right _ _).trans hx
  have hden : 1 - x < 0 := by linarith
  have hr : x ^ 2 / (1 - x) ≤ -x := (div_le_iff_of_neg hden).mpr (by nlinarith)
  exact hr.trans (by linarith)

/-- Bài tập 3.2.4(c): aˣ→0 khi x→−∞, với a>1. -/
theorem real_power_atBot_zero {a : ℝ} (ha : 1 < a) :
    DomainAtBotLimit univ (fun x ↦ a ^ x) 0 :=
  (domainAtBotLimit_iff_tendsto not_bddBelow_univ).mpr
    ((tendsto_rpow_atBot_of_base_gt_one a ha).mono_left inf_le_left)

/-- Bài tập 3.2.4(d): aˣ→+∞ khi x→−∞, với 0<a<1. -/
theorem real_power_atBot_top {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    ¬ BddBelow (univ : Set ℝ) ∧
      Tendsto (fun x : ℝ ↦ a ^ x) (atBot ⊓ 𝓟 univ) atTop :=
  ⟨not_bddBelow_univ, (tendsto_rpow_atBot_of_base_lt_one a h0 h1).mono_left inf_le_left⟩

/-- Bài tập 3.2.5: giới hạn của |f| khi f có giới hạn hữu hạn. -/
theorem domainLimit_abs {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (h : DomainLimit D f a L) : DomainLimit D (fun x ↦ |f x|) a |L| :=
  (domainLimit_iff_tendsto h.1).mpr ((domainLimit_iff_tendsto h.1).mp h).abs

/-- Phản ví dụ cho chiều ngược: |sign|→1 nhưng hàm dấu không có giới hạn hữu hạn. -/
theorem absolute_limit_converse_counterexample :
    DomainLimit univ (fun x ↦ |Real.sign x|) 0 1 ∧ ¬ HasDomainLimit univ Real.sign 0 := by
  constructor
  · apply (domainLimit_congr_punctured (f := fun _ ↦ (1 : ℝ)) ?_).mp (constant_domainLimit 1 0)
    intro x _ hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · simp [Real.sign_of_neg hn]
    · simp [Real.sign_of_pos hp]
  · rintro ⟨L, hL⟩
    obtain ⟨hl, hr⟩ := (domainLimit_iff_left_right (leftAccumulation_univ 0)
      (rightAccumulation_univ 0)).mp hL
    have hleft := domainLeftLimit_unique sign_one_sided_limits.1 hl
    have hright := domainRightLimit_unique sign_one_sided_limits.2 hr
    linarith


noncomputable def rationalIdentityIrrationalReflection (x : ℝ) : ℝ := by
  classical
  exact if x ∈ range ((↑) : ℚ → ℝ) then x else 1 - x


theorem rationalReflection_half_limit :
    DomainLimit (Icc (0 : ℝ) 1) rationalIdentityIrrationalReflection (1 / 2) (1 / 2) := by
  classical
  have ha : AccumulationPointOf (Icc (0 : ℝ) 1) (1 / 2) :=
    accumulationPointOf_mono (unit_half_open_accumulation (by constructor <;> norm_num))
      (fun _ h ↦ ⟨h.1, h.2.le⟩)
  refine ⟨ha, fun ε hε ↦ ⟨ε, hε, ?_⟩⟩
  intro x _ _ hx
  unfold rationalIdentityIrrationalReflection
  split_ifs with hq
  · exact hx
  · have he : 1 - x - 1 / 2 = -(x - 1 / 2) := by ring
    simpa only [he, abs_neg] using hx


theorem rationalReflection_zero_no_limit :
    ¬ HasDomainLimit (Icc (0 : ℝ) 1) rationalIdentityIrrationalReflection 0 := by
  classical
  rintro ⟨L, _, hL⟩
  obtain ⟨δ, hδ, hh⟩ := hL (1 / 4) (by norm_num)
  have hm : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  obtain ⟨q, hq0, hqm⟩ := exists_rat_btwn hm
  obtain ⟨r, hri, hr0, hrm⟩ := exists_irrational_btwn hm
  have hqd : (q : ℝ) < δ := hqm.trans_le (min_le_left _ _)
  have hq4 : (q : ℝ) < 1 / 4 := hqm.trans_le (min_le_right _ _)
  have hrd : r < δ := hrm.trans_le (min_le_left _ _)
  have hr4 : r < 1 / 4 := hrm.trans_le (min_le_right _ _)
  have hfq : rationalIdentityIrrationalReflection q = q := by
    unfold rationalIdentityIrrationalReflection
    exact if_pos ⟨q, rfl⟩
  have hfr : rationalIdentityIrrationalReflection r = 1 - r := by
    unfold rationalIdentityIrrationalReflection
    exact if_neg hri
  have hqerr := hh q ⟨hq0.le, by linarith⟩
    (by simpa only [sub_zero, abs_of_pos hq0] using hq0)
    (by simpa only [sub_zero, abs_of_pos hq0] using hqd)
  have hrerr := hh r ⟨hr0.le, by linarith⟩
    (by simpa only [sub_zero, abs_of_pos hr0] using hr0)
    (by simpa only [sub_zero, abs_of_pos hr0] using hrd)
  rw [hfq, abs_lt] at hqerr
  rw [hfr, abs_lt] at hrerr
  linarith [hqerr.1, hrerr.2]


theorem rationalReflection_one_no_limit :
    ¬ HasDomainLimit (Icc (0 : ℝ) 1) rationalIdentityIrrationalReflection 1 := by
  classical
  rintro ⟨L, _, hL⟩
  obtain ⟨δ, hδ, hh⟩ := hL (1 / 4) (by norm_num)
  have hm : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  obtain ⟨q, hqm, hq1⟩ := exists_rat_btwn (show 1 - min δ (1 / 4) < (1 : ℝ) by linarith)
  obtain ⟨r, hri, hrm, hr1⟩ := exists_irrational_btwn
    (show 1 - min δ (1 / 4) < (1 : ℝ) by linarith)
  have hqd : 1 - δ < (q : ℝ) := lt_of_le_of_lt (by linarith [min_le_left δ (1 / 4 : ℝ)]) hqm
  have hq4 : 3 / 4 < (q : ℝ) := lt_of_le_of_lt (by linarith [min_le_right δ (1 / 4 : ℝ)]) hqm
  have hrd : 1 - δ < r := lt_of_le_of_lt (by linarith [min_le_left δ (1 / 4 : ℝ)]) hrm
  have hr4 : 3 / 4 < r := lt_of_le_of_lt (by linarith [min_le_right δ (1 / 4 : ℝ)]) hrm
  have hfq : rationalIdentityIrrationalReflection q = q := by
    unfold rationalIdentityIrrationalReflection
    exact if_pos ⟨q, rfl⟩
  have hfr : rationalIdentityIrrationalReflection r = 1 - r := by
    unfold rationalIdentityIrrationalReflection
    exact if_neg hri
  have hqerr := hh q ⟨by linarith, hq1.le⟩
    (by rw [abs_of_neg (by linarith : (q : ℝ) - 1 < 0)]; linarith)
    (by rw [abs_of_neg (by linarith : (q : ℝ) - 1 < 0)]; linarith)
  have hrerr := hh r ⟨by linarith, hr1.le⟩
    (by rw [abs_of_neg (by linarith : r - 1 < 0)]; linarith)
    (by rw [abs_of_neg (by linarith : r - 1 < 0)]; linarith)
  rw [hfq, abs_lt] at hqerr
  rw [hfr, abs_lt] at hrerr
  linarith [hqerr.2, hrerr.1]

end calculus.Chapter03.Section02Exercises
